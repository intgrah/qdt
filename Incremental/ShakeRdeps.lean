module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace ShakeRdeps

open Std (DHashMap HashMap HashSet)

variable (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

structure Store where
  cache : DHashMap Q (Memo Q R) := DHashMap.emptyWithCapacity 1024
  rdeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

def Store.addRdep (store : Store Q R) (dependency dependent : Q) : Store Q R :=
  let existing := store.rdeps.getD dependency ∅
  let rdeps := store.rdeps.insert dependency (existing.insert dependent)
  { store with rdeps }

partial def getTransitiveDependents (info : Store Q R) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then
          go rest visited
        else
          let visited := visited.insert k
          let dependents := info.rdeps.getD k (HashSet.emptyWithCapacity 0)
          let newWork := dependents.toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def invalidate (store : Store Q R) (changedKeys : HashSet Q) : Store Q R :=
  let toInvalidate := getTransitiveDependents store changedKeys
  let cache := toInvalidate.fold (init := store.cache) DHashMap.erase
  { store with cache }

partial def build : Build Monad (Store Q R) Q R :=
  fun tasks target store => runEST fun σ => do
    let cache ← ST.mkRef (σ := σ) store.cache
    let rdeps ← ST.mkRef (σ := σ) store.rdeps
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024 : DHashMap Q (Memo Q R))
    let stack ← ST.mkRef (σ := σ) (#[] : Array Q)
    let rec fetch (q : Q) : EST Cycle σ (R q) := do
      if let some dependent := (← stack.get).back? then
        rdeps.modify fun rd =>
          rd.alter q (·.getD ∅ |>.insert dependent)
      match (← started.get).get? q with
      | some memo => pure memo.value
      | none =>
        let s ← stack.get
        if s.contains q then
          throw Cycle.mk
        stack.set (s.push q)
        try
          match tasks q with
          | none =>
            match (← cache.get).get? q with
            | some memo =>
              started.modify (·.insert q memo)
              pure memo.value
            | none => throw Cycle.mk
          | some task =>
            let compute : EST Cycle σ (R q × HashMap Q UInt64) := do
              let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
              let fetch' (q : Q) : EST Cycle σ (R q) := do
                let v ← fetch q
                let ds ← deps.get
                if !ds.contains q then
                  let h := match (← started.get).get? q with
                    | some memo => memo.hash
                    | none => hash v
                  deps.modify (·.insert q h)
                pure v
              let a ← task _ fetch'
              pure (a, ← deps.get)

            let verifyDeps (deps : HashMap Q UInt64) : EST Cycle σ PUnit := do
              for (depKey, oldHash) in deps do
                let _ ← fetch depKey
                let h := match (← started.get).get? depKey with
                  | some memo => memo.hash
                  | none => hash 0
                if h != oldHash then throw Cycle.mk

            let recompute : EST Cycle σ (R q) := do
              let (value, deps) ← compute
              let memo : Memo Q R q := { value, deps }
              started.modify (·.insert q memo)
              cache.modify (·.insert q memo)
              pure value

            match (← cache.get).get? q with
            | some memo =>
              try
                verifyDeps memo.deps
                started.modify (·.insert q memo)
                pure memo.value
              catch _ => recompute
            | none => recompute
        finally
          stack.modify Array.pop
    return (← fetch target, ⟨← cache.get, ← rdeps.get⟩)

end ShakeRdeps
