module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Busy

open Std (DHashMap)

variable (Q : Type) (R : Q → Type)
  [BEq Q] [LawfulBEq Q] [Hashable Q]

def Store := DHashMap Q R

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q]

partial def build : Build Applicative (Store Q R) Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) store
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      match tasks q with
      | none =>
          match (← stRef.get).get? q with
          | some v => return v
          | none => throw .missingInput
      | some t =>
          let v ← t _ fetch
          stRef.modify (·.insert q v)
          return v
    return (← fetch target, ← stRef.get)

end Busy

end Incremental
