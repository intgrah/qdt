module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Busy

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

partial def build : Build Applicative Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) store
    let rec fetch (q : Q) : EST Cycle σ (R q) := do
      match tasks q with
      | none =>
          match (← stRef.get).cache.get? q with
          | some memo => return memo.value
          | none => throw Cycle.mk
      | some t =>
          let v ← t _ fetch
          stRef.modify fun s =>
            let memo := { value := v, deps := ∅ }
            let cache := s.cache.insert q memo
            { s with cache }
          return v
    let _ ← fetch target
    return (← stRef.get)

end Busy

end Incremental
