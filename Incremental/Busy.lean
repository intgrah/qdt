module

public import Incremental.Basic

@[expose] public section

namespace Incremental

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq Q]

partial def Busy : Build Applicative I V Q R ι where
  σ := ι
  init := id
  set s i v := Input.set s i v
  build tasks q s := runEST fun σ => do
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if (← stack.get).contains q then throw .cycle
      stack.modify (·.push q)
      let r ← tasks q (EST BuildError σ) (Input.get s) fetch
      stack.modify (·.pop)
      return r
    return (← fetch q, s)

open Std (DHashMap)

variable [LawfulBEq Q] [Hashable Q]

partial def LessBusy : Build Applicative I V Q R ι where
  σ := ι
  init := id
  set s i v := Input.set s i v
  build tasks q s := runEST fun σ => do
    let stack ← ST.mkRef (σ := σ) #[]
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some r := (← started.get).get? q then return r
      if (← stack.get).contains q then throw .cycle
      stack.modify (·.push q)
      let r ← tasks q (EST BuildError σ) (Input.get s) fetch
      stack.modify (·.pop)
      started.modify (·.insert q r)
      return r
    return (← fetch q, s)

end Incremental
