import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet

namespace Qdt

namespace Incremental

open Std (DHashMap HashMap HashSet)

universe u

variable {ε Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Memo (R : Q → Type) (q : Q) where
  value : R q
  deps : HashMap Q UInt64

structure Engine (ε : Type) (R : Q → Type) where
  cache : DHashMap Q (Memo R) := DHashMap.emptyWithCapacity 1024
  reverseDeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024
  recover : ∀ q, EIO ε (R q)
  fingerprint : ∀ q, R q → UInt64
  isInput : Q → Bool

namespace Engine

def addReverseDep (engine : Engine ε R) (dependency dependent : Q) : Engine ε R :=
  let existing := engine.reverseDeps.getD dependency (HashSet.emptyWithCapacity 8)
  { engine with reverseDeps := engine.reverseDeps.insert dependency (existing.insert dependent) }

partial def getTransitiveDependents (engine : Engine ε R) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then
          go rest visited
        else
          let visited := visited.insert k
          let dependents := engine.reverseDeps.getD k (HashSet.emptyWithCapacity 0)
          let newWork := dependents.toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def invalidate (engine : Engine ε R) (changedKeys : HashSet Q) : Engine ε R :=
  let toInvalidate := engine.getTransitiveDependents changedKeys
  let newCache := toInvalidate.fold (init := engine.cache) fun cache key =>
    cache.erase key
  { engine with cache := newCache }

def invalidateFiles (engine : Engine ε R) (changedFiles : List Q) : Engine ε R :=
  let changedSet := changedFiles.foldl (init := HashSet.emptyWithCapacity changedFiles.length) (·.insert ·)
  engine.invalidate changedSet

end Engine

structure RunState (ε : Type) (R : Q → Type) where
  engine : Engine ε R
  started : DHashMap Q (Memo R)
  stack : List Q
  deps : HashMap Q UInt64

abbrev BaseM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
  StateRefT (RunState ε R) (EIO ε)

set_option checkBinderAnnotations false in
abbrev Task
    (c : (Type u → Type u) → Type (u + 1))
    (Q : Type u)
    (R : Q → Type u)
    (f : Type u → Type u) [c f] :=
  ReaderT (∀ q : Q, f (R q)) f

/-!
[Build systems à la carte]
The choice of the constraint `c` has concrete meanings:
- `c := Functor` - sequential only
- `c := Applicative` - static dependencies
- `c := Monad` - dynamic dependencies
-/

abbrev TaskT := Task (c := Monad)

abbrev TaskM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
  TaskT Q R (BaseM ε R)

def TaskM.fetch (q : Q) : TaskM ε R (R q) :=
  fun fetch => fetch q

export TaskM (fetch)

def trackDeps {α}
    (fingerprint : ∀ q, R q → UInt64)
    (task : TaskM ε R α) :
    TaskM ε R (α × HashMap Q UInt64) := do
  let oldDeps := (← get).deps
  modify fun st => { st with deps := HashMap.emptyWithCapacity 64 }
  let base ← read
  let fetchQ' : ∀ q, BaseM ε R (R q) := fun q => do
    let v ← base q
    let ds := (← get).deps
    if !ds.contains q then
      modify fun st => { st with deps := st.deps.insert q (fingerprint q v) }
    pure v
  let a ← task.run fetchQ'
  let deps := (← get).deps
  modify fun st => { st with deps := oldDeps }
  return (a, deps)

def verifyDeps
    (fingerprint : ∀ q, R q → UInt64)
    (deps : HashMap Q UInt64) :
    TaskM ε R Bool := do
  deps.toList.allM fun (q, old) => do
    let v ← fetch q
    return fingerprint q v == old

def runWithEngine {α}
    (engine : Engine ε R)
    (rules : ∀ q, TaskM ε R (R q))
    (task : TaskM ε R α) :
    EIO ε (α × Engine ε R) := do
  let init : RunState ε R :=
    {
      engine
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      deps := HashMap.emptyWithCapacity 64
    }
  let action : BaseM ε R (α × Engine ε R) := do
    let fetchRef : ST.Ref IO.RealWorld (∀ q, BaseM ε R (R q)) ←
      ST.mkRef (fun q => engine.recover q)

    let fetchIO (q : Q) : BaseM ε R (R q) := do
      (← fetchRef.get) q

    let rulesIO (q : Q) : BaseM ε R (R q) := do
      let st ← get

      match st.stack.head? with
      | some dependent =>
          modify fun st =>
            { st with engine := st.engine.addReverseDep q dependent }
      | none => pure ()

      match st.started.get? q with
      | some memo => pure memo.value
      | none =>
          if st.stack.contains q then
             let val ← st.engine.recover q
             return val
          modify fun st => { st with stack := q :: st.stack }
          try
            let st ← get
            let engine := st.engine

            let recompute (store : Bool) : BaseM ε R (R q) := do
              let (value, deps) ← (trackDeps engine.fingerprint (rules q)).run fetchIO
              let memo : Memo R q := { value, deps }
              modify fun st => { st with started := st.started.insert q memo }
              if store then
                modify fun st =>
                  { st with engine := { st.engine with cache := st.engine.cache.insert q memo } }
              pure value

            if engine.isInput q then
              recompute (store := false)
            else
              match engine.cache.get? q with
              | some memo =>
                  if ← (verifyDeps engine.fingerprint memo.deps).run fetchIO then
                    modify fun st => { st with started := st.started.insert q memo }
                    pure memo.value
                  else
                    recompute (store := true)
              | none =>
                  recompute (store := true)
          finally
            modify fun st =>
              match st.stack with
              | [] => st
              | _ :: rest => { st with stack := rest }

    fetchRef.set rulesIO

    let a ← task.run fetchIO
    let st ← get
    pure (a, st.engine)

  action.run' init

end Incremental

end Qdt
