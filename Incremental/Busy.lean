module

public import Incremental.Basic

namespace Incremental

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq Q]

/-- Never remembers anything, always computes. -/
public partial def Busy : Build Monad I V Q R ι where
  σ := ι
  init := id
  set i v := modify fun store => Input.set store i v
  build tasks q := fun store => runEST fun σ => do
    -- Call stack for cycle detection
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if (← stack.get).contains q then throw .cycle
      stack.modify (·.push q)
      let r ← tasks q (EST BuildError σ) (fun i => pure (Input.get store i)) fetch
      stack.modify (·.pop)
      return r
    return (← fetch q, store)

end Incremental
