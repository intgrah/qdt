module

public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)
open System (FilePath)

universe u

/-!
[Build systems à la carte]
The choice of the constraint `c` has concrete meanings:
- `c := Functor` - sequential only
- `c := Applicative` - static dependencies
- `c := Monad` - dynamic dependencies
-/

-- Disable binder annotation checks to allow `[c f]`
set_option checkBinderAnnotations false in
def Task
    (c : (Type → Type) → Type 1)
    (Q : Type)
    (R : Q → Type)
    (α : Type) :
    Type 1 :=
  ∀ (f : Type → Type) [c f], (∀ q, f (R q)) → f α

variable (c : (Type → Type) → Type 1) (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

namespace Task

def fetch
    {c : (Type → Type) → Type 1}
    {Q : Type}
    {R : Q → Type}
    (q : Q) :
    Task c Q R (R q) :=
  fun _ [_] fetch => fetch q

instance {Q : Type} {R : Q → Type} : Monad (Task Monad Q R) where
  pure a := fun _ [_] _ => pure a
  bind t f := fun g [_] fetch => t g fetch >>= fun a => f a g fetch
  map f t := fun g [_] fetch => f <$> t g fetch

end Task

export Task (fetch)

structure Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64
  hash_value : Hashable.hash value = hash := by rfl

structure Store where
  cache : DHashMap Q (Memo Q R) := DHashMap.emptyWithCapacity 1024
  reverseDeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024

namespace Store

def addReverseDep (store : Store Q R) (dependency dependent : Q) : Store Q R :=
  let existing := store.reverseDeps.getD dependency ∅
  let existing := existing.insert dependent
  let reverseDeps := store.reverseDeps.insert dependency existing
  { store with reverseDeps }

partial def getTransitiveDependents (store : Store Q R) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then
          go rest visited
        else
          let visited := visited.insert k
          let dependents := store.reverseDeps.getD k (HashSet.emptyWithCapacity 0)
          let newWork := dependents.toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def invalidate (store : Store Q R) (changedKeys : HashSet Q) : Store Q R :=
  let toInvalidate := store.getTransitiveDependents Q R changedKeys
  let cache := toInvalidate.fold (init := store.cache) DHashMap.erase
  { store with cache }

end Store

def Tasks : Type 1 :=
  ∀ q, Option (Task c Q R (R q))

structure ProfEntry where
  hits    : Nat := 0
  misses  : Nat := 0
  totalNs : Nat := 0

abbrev Profile := IO.Ref (HashMap String ProfEntry)

def Build : Type 1 :=
  ∀ {α}, Tasks c Q R → Store Q R → Task c Q R α → EIO Unit (α × Store Q R)

namespace Busy

partial def build : Build Applicative Q R :=
  fun tasks store task => do
    let storeRef : ST.Ref IO.RealWorld (Store Q R) ← ST.mkRef store
    let rec fetch (q : Q) : EIO Unit (R q) := do
      match tasks q with
      | none =>
          match (← storeRef.get).cache.get? q with
          | some memo => return memo.value
          | none => throw ()
      | some t =>
          let v ← t _ fetch
          storeRef.modify fun s =>
            let memo := { value := v, deps := ∅, hash := hash v }
            let cache := s.cache.insert q memo
            { s with cache }
          return v
    let a ← task _ fetch
    let s ← storeRef.get
    pure (a, s)

end Busy

namespace Shake

structure State where
  store : Store Q R
  started : DHashMap Q (Memo Q R)
  stack : List Q
  currentDeps : HashMap Q UInt64

def build [∀ q, Hashable (R q)]
    (label : Q → String := fun _ => "?")
    (prof : Option Profile := none)
    (onBuildEvent : Option (Q → Bool → IO Unit) := none) : Build Monad Q R :=
  fun {α} tasks store task => do
    let init : State Q R := {
      store
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      currentDeps := HashMap.emptyWithCapacity 64
    }

    let action : StateRefT (State Q R) (EIO Unit) (α × Store Q R) := do
      let fetchRef : ST.Ref IO.RealWorld (∀ q, StateRefT (State Q R) (EIO Unit) (R q)) ←
        ST.mkRef fun _ => throw ()

      let rec buildRule (q : Q) : StateRefT (State Q R) (EIO Unit) (R q) := do
        let st ← get

        match st.started.get? q with
        | some memo =>
            match st.stack.head? with
            | some dependent =>
                modify fun st =>
                  let store := st.store.addReverseDep Q R q dependent
                  { st with store }
            | none => pure ()
            pure memo.value
        | none =>
            match st.stack.head? with
            | some dependent =>
                modify fun st =>
                  let store := st.store.addReverseDep Q R q dependent
                  { st with store }
            | none => pure ()
            if st.stack.contains q then
              let stackStr := st.stack.map label |>.toString
              (IO.eprintln s!"[cycle] {label q} in stack {stackStr}").catchExceptions fun _ => pure ()
              throw ()
            modify fun st => { st with stack := q :: st.stack }
            try
              let st ← get

              match tasks q with
              | none =>
                  match st.store.cache.get? q with
                  | some memo =>
                      modify fun st => { st with started := st.started.insert q memo }
                      pure memo.value
                  | none =>
                      throw ()
              | some taskQ =>
                  let compute : StateRefT (State Q R) (EIO Unit) (R q × HashMap Q UInt64) := do
                    let oldDeps := (← get).currentDeps
                    modify fun st => { st with currentDeps := HashMap.emptyWithCapacity 64 }
                    let fetch' : ∀ q, StateRefT (State Q R) (EIO Unit) (R q) := fun q => do
                      let v ← (← fetchRef.get) q
                      let ds := (← get).currentDeps
                      if !ds.contains q then
                        let h := match (← get).started.get? q with
                          | some memo => memo.hash
                          | none => hash v
                        modify fun st => { st with currentDeps := st.currentDeps.insert q h }
                      pure v
                    let a ← taskQ _ fetch'
                    let deps := (← get).currentDeps
                    modify fun st => { st with currentDeps := oldDeps }
                    pure (a, deps)

                  let verifyDeps (deps : HashMap Q UInt64) : StateRefT (State Q R) (EIO Unit) Bool := do
                    deps.toList.allM fun (depKey, oldHash) => do
                      try
                        let _ ← (← fetchRef.get) depKey
                        let h := match (← get).started.get? depKey with
                          | some memo => memo.hash
                          | none => 0
                        pure (h == oldHash)
                      catch _ => pure false

                  let recompute : StateRefT (State Q R) (EIO Unit) (R q) := do
                    if let some cb := onBuildEvent then
                      (cb q true).catchExceptions fun _ => pure ()
                    let t0 ← IO.monoNanosNow
                    let (value, deps) ← compute
                    let t1 ← IO.monoNanosNow
                    if let some p := prof then
                      p.modify fun m =>
                        let e := m.getD (label q) {}
                        m.insert (label q) { e with misses := e.misses + 1, totalNs := e.totalNs + (t1 - t0) }
                    let memo : Memo Q R q := { value, deps, hash := hash value }
                    modify fun st =>
                      { st with
                        started := st.started.insert q memo
                        store := { st.store with cache := st.store.cache.insert q memo } }
                    if let some cb := onBuildEvent then
                      (cb q false).catchExceptions fun _ => pure ()
                    pure value

                  match st.store.cache.get? q with
                  | some memo =>
                      if ← verifyDeps memo.deps then
                        if let some p := prof then
                          p.modify fun m =>
                            let e := m.getD (label q) {}
                            m.insert (label q) { e with hits := e.hits + 1 }
                        modify fun st => { st with started := st.started.insert q memo }
                        pure memo.value
                      else
                        recompute
                  | none =>
                      recompute
            finally
              modify fun st =>
                match st.stack with
                | [] => st
                | _ :: rest => { st with stack := rest }

      fetchRef.set buildRule

      let a ← task _ (← fetchRef.get)
      let st ← get
      return (a, st.store)

    action.run' init

end Shake

def padR (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.length) ' ')
def padL (s : String) (n : Nat) : String := String.ofList (List.replicate (n - s.length) ' ') ++ s

def Profile.print (p : Profile) : IO Unit := do
  let m ← p.get
  let rows := m.toArray.map fun (k, e) => (k, e.hits, e.misses, e.totalNs / 1000000)
  let rows := rows.toList.mergeSort (fun a b => a.2.2.2 > b.2.2.2)
  println!"{padR "Key" 22} {padL "hits" 8} {padL "misses" 8} {padL "ms" 10}"
  println! String.ofList (List.replicate 52 '-')
  for (k, hits, misses, ms) in rows do
    IO.println s!"{padR k 22} {padL (toString hits) 8} {padL (toString misses) 8} {padL (toString ms) 10}"

end Incremental
