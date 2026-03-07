module

public import Std.Data.DHashMap
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)
open System (FilePath)

/-!
[Build systems à la carte]
The choice of the constraint `c` has concrete meanings:
- `c := Functor` - sequential only
- `c := Applicative` - static dependencies
- `c := Monad` - dynamic dependencies
-/

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

inductive Cycle
  | mk
deriving Inhabited

def Tasks : Type 1 :=
  ∀ q, Option (Task c Q R (R q))

structure Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64
  hash_value : Hashable.hash value = hash := by rfl

structure Store where
  cache : DHashMap Q (Memo Q R) := DHashMap.emptyWithCapacity 1024
  reverseDeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024
deriving Inhabited

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

def Build : Type 1 :=
  Tasks c Q R → Q → Store Q R → Except Cycle (Store Q R)

namespace Busy

partial def build : Build Applicative Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) store
    let rec fetch (q : Q) : EST Cycle σ (R q) := do
      match tasks q with
      | none =>
          match (← stRef.get).cache.get? q with
          | some memo => return memo.value
          | none => throw .mk
      | some t =>
          let v ← t _ fetch
          stRef.modify fun s =>
            let memo := { value := v, deps := ∅, hash := hash v }
            let cache := s.cache.insert q memo
            { s with cache }
          return v
    let _ ← fetch target
    return (← stRef.get)

end Busy

namespace Shake

structure State where
  store : Store Q R
  started : DHashMap Q (Memo Q R)
  stack : List Q
  currentDeps : HashMap Q UInt64

partial def build : Build Monad Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) ({
      store
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      currentDeps := HashMap.emptyWithCapacity 64
    } : State Q R)

    let rec buildRule (q : Q) : EST Cycle σ (R q) := do
      let st ← stRef.get

      match st.started.get? q with
      | some memo =>
          match st.stack.head? with
          | some dependent =>
              stRef.modify fun st =>
                let store := st.store.addReverseDep Q R q dependent
                { st with store }
          | none => pure ()
          pure memo.value
      | none =>
          match st.stack.head? with
          | some dependent =>
              stRef.modify fun st =>
                let store := st.store.addReverseDep Q R q dependent
                { st with store }
          | none => pure ()
          if st.stack.contains q then
            throw .mk
          stRef.modify fun st => { st with stack := q :: st.stack }
          try
            let st ← stRef.get

            match tasks q with
            | none =>
                match st.store.cache.get? q with
                | some memo =>
                    stRef.modify fun st => { st with started := st.started.insert q memo }
                    pure memo.value
                | none =>
                    throw .mk
            | some task =>
                let compute : EST Cycle σ (R q × HashMap Q UInt64) := do
                  let oldDeps := (← stRef.get).currentDeps
                  stRef.modify fun st => { st with currentDeps := HashMap.emptyWithCapacity 64 }
                  let fetch' : ∀ q, EST Cycle σ (R q) := fun q => do
                    let v ← buildRule q
                    let ds := (← stRef.get).currentDeps
                    if !ds.contains q then
                      let h := match (← stRef.get).started.get? q with
                        | some memo => memo.hash
                        | none => hash v
                      stRef.modify fun st => { st with currentDeps := st.currentDeps.insert q h }
                    pure v
                  let a ← task _ fetch'
                  let deps := (← stRef.get).currentDeps
                  stRef.modify fun st => { st with currentDeps := oldDeps }
                  pure (a, deps)

                let verifyDeps (deps : HashMap Q UInt64) : EST Cycle σ PUnit := do
                  for (depKey, oldHash) in deps.toList do
                    try
                      let _ ← buildRule depKey
                      let h := match (← stRef.get).started.get? depKey with
                        | some memo => memo.hash
                        | none => hash 0
                      if h != oldHash then throw .mk
                    catch _ => throw .mk

                let recompute : EST Cycle σ (R q) := do
                  let (value, deps) ← compute
                  let memo : Memo Q R q := { value, deps, hash := hash value }
                  stRef.modify fun st =>
                    { st with
                      started := st.started.insert q memo
                      store := { st.store with cache := st.store.cache.insert q memo } }
                  pure value

                match st.store.cache.get? q with
                | some memo =>
                    try
                      verifyDeps memo.deps
                      stRef.modify fun st => { st with started := st.started.insert q memo }
                      pure memo.value
                    catch _ => recompute
                | none =>
                    recompute
          finally
            stRef.modify fun st =>
              match st.stack with
              | [] => st
              | _ :: rest => { st with stack := rest }

    let _ ← buildRule target
    return (← stRef.get).store

end Shake

end Incremental
