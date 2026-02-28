import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Config

namespace Qdt

namespace Incremental

open Std (DHashMap HashMap HashSet)
open System (FilePath)

universe u

variable {Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Memo (R : Q → Type) (q : Q) where
  value : R q
  deps : HashMap Q UInt64

structure Engine (R : Q → Type) where
  cache : DHashMap Q (Memo R) := DHashMap.emptyWithCapacity 1024
  reverseDeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024
  fingerprint : ∀ q, R q → UInt64
  isInput : Q → Bool

namespace Engine

def addReverseDep (engine : Engine R) (dependency dependent : Q) : Engine R :=
  let existing := engine.reverseDeps.getD dependency (HashSet.emptyWithCapacity 8)
  { engine with reverseDeps := engine.reverseDeps.insert dependency (existing.insert dependent) }

partial def getTransitiveDependents (engine : Engine R) (keys : HashSet Q) : HashSet Q :=
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

def invalidate (engine : Engine R) (changedKeys : HashSet Q) : Engine R :=
  let toInvalidate := engine.getTransitiveDependents changedKeys
  let newCache := toInvalidate.fold (init := engine.cache) fun cache key =>
    cache.erase key
  { engine with cache := newCache }

def invalidateFiles (engine : Engine R) (changedFiles : List Q) : Engine R :=
  let changedSet := changedFiles.foldl (init := HashSet.emptyWithCapacity changedFiles.length) (·.insert ·)
  engine.invalidate changedSet

end Engine

structure BaseContext where
  config : Config
  overrides : HashMap FilePath String

structure RunState (R : Q → Type) where
  engine : Engine R
  started : DHashMap Q (Memo R)
  stack : List Q
  deps : HashMap Q UInt64

abbrev BaseM {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
  ReaderT BaseContext (StateRefT (RunState R) (EIO Unit))

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

abbrev TaskM {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
  TaskT Q R (BaseM R)

def TaskM.fetch (q : Q) : TaskM R (R q) :=
  fun fetch => fetch q

export TaskM (fetch)

def trackDeps {α}
    (fingerprint : ∀ q, R q → UInt64)
    (task : TaskM R α) :
    TaskM R (α × HashMap Q UInt64) := do
  let oldDeps := (← get).deps
  modify fun st => { st with deps := HashMap.emptyWithCapacity 64 }
  let base ← read
  let fetchQ' : ∀ q, BaseM R (R q) := fun q => do
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
    TaskM R Bool := do
  deps.toList.allM fun (q, old) => do
    try
      let v ← fetch q
      return fingerprint q v == old
    catch _ => return false

def runWithEngine {α}
    (rules : ∀ q, TaskM R (R q))
    (ctx : BaseContext)
    (engine : Engine R)
    (task : TaskM R α) :
    EIO Unit (α × Engine R) := do
  let init : RunState R :=
    {
      engine
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      deps := HashMap.emptyWithCapacity 64
    }
  let action : BaseM R (α × Engine R) := do
    let fetchRef : ST.Ref IO.RealWorld (∀ q, BaseM R (R q)) ←
      ST.mkRef (fun _ => throw ())

    let fetchIO (q : Q) : BaseM R (R q) := do
      (← fetchRef.get) q

    let rulesIO (q : Q) : BaseM R (R q) := do
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
             throw ()
          modify fun st => { st with stack := q :: st.stack }
          try
            let st ← get
            let engine := st.engine

            let recompute (store : Bool) : BaseM R (R q) := do
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

  (action ctx).run' init

end Incremental

end Qdt
