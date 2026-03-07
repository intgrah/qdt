module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Busy

open Std (DHashMap)

variable (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Store where
  cache : DHashMap Q R := DHashMap.emptyWithCapacity 1024

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q]

partial def build : Build Applicative (Store Q R) Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) store
    let rec fetch (q : Q) : EST Cycle σ (R q) := do
      match tasks q with
      | none =>
          match (← stRef.get).cache.get? q with
          | some v => return v
          | none => throw Cycle.mk
      | some t =>
          let v ← t _ fetch
          stRef.modify fun s => { s with cache := s.cache.insert q v }
          return v
    return (← fetch target, ← stRef.get)

end Busy

end Incremental
