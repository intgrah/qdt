module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Shake

open Std (DHashMap HashMap HashSet)

variable (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

def Store := DHashMap Q (Memo Q R)

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

partial def build : Build Monad (Store Q R) Q R :=
  fun tasks target store => runEST fun σ => do
    let store ← ST.mkRef (σ := σ) store
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) (#[] : Array Q)
    let rec fetch (q : Q) : EST Cycle σ (R q) := do
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
            match (← store.get).get? q with
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
                  | none => 0
                if h != oldHash then throw Cycle.mk

            let recompute : EST Cycle σ (R q) := do
              let (value, deps) ← compute
              let memo : Memo Q R q := { value, deps }
              started.modify (·.insert q memo)
              store.modify (·.insert q memo)
              pure value

            match (← store.get).get? q with
            | some memo =>
              try
                verifyDeps memo.deps
                started.modify (·.insert q memo)
                pure memo.value
              catch _ => recompute
            | none => recompute
        finally
          stack.modify Array.pop
    return (← fetch target, ← store.get)

end Shake
