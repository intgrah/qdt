module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq Q] [LawfulBEq Q] [Hashable Q]

/--
Never remembers anything permanently, but remembers queries that it has already
computed during the current run, avoiding redundant computation of diamond dependencies.
This build system is most similar to a batch elaborator.
-/
public partial def LessBusy : Build Monad I V Q R ι where
  σ := ι
  init := id
  set i v := modify fun store => Input.set store i v
  build tasks q := fun store => runEST fun σ => do
    -- Call stack for cycle detection
    let stack ← ST.mkRef (σ := σ) #[]
    -- Queries it has already computed
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some r := (← started.get).get? q then return r
      if (← stack.get).contains q then throw .cycle
      stack.modify (·.push q)
      let r ← tasks q (EST BuildError σ) (fun i => pure (Input.get store i)) fetch
      stack.modify (·.pop)
      started.modify (·.insert q r)
      return r
    return (← fetch q, store)

end Incremental
