module

public import Incremental.Salsa

namespace Incremental

open Std (DHashMap HashMap)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

@[extern "lean_salsa_build"]
public opaque SalsaC.build'
    {I : Type} {V : I → Type} {Q : Type} {R : Q → Type} {ι : Type}
    [BEq I] [Hashable I]
    [BEq Q] [Hashable Q] [∀ q, Hashable (R q)]
    [Input I V ι] :
    Tasks Monad I V Q R → ∀ q,
    Salsa.Store I Q R ι → Except BuildError (R q × Salsa.Store I Q R ι)

public def SalsaC : Build Monad I V Q R ι where
  σ := Salsa.Store I Q R ι
  init inputs := {
    inputs
    revision := 0
    memos := DHashMap.emptyWithCapacity 1024
    inputRevisions := HashMap.emptyWithCapacity 64
  }
  set i v := modify fun store =>
    let revision := store.revision + 1
    let inputs := Input.set store.inputs i v
    let inputRevisions := store.inputRevisions.insert i revision
    { store with inputs, revision, inputRevisions }
  build := SalsaC.build'

end Incremental
