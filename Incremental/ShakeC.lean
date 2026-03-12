module

public import Incremental.Shake

public section

namespace Incremental

open Std (DHashMap)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

@[extern "lean_shake_build"]
opaque ShakeC.build'
    {I : Type} {V : I → Type} {Q : Type} {R : Q → Type} {ι : Type}
    [BEq I] [Hashable I] [∀ i, Hashable (V i)]
    [BEq Q] [Hashable Q] [∀ q, Hashable (R q)]
    [Input I V ι] :
    Tasks Monad I V Q R → ∀ q,
    Shake.Store I Q R ι → Except BuildError (R q × Shake.Store I Q R ι)

def ShakeC : Build Monad I V Q R ι where
  σ := Shake.Store I Q R ι
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  set i v := modify fun store => { store with inputs := Input.set store.inputs i v }
  build := ShakeC.build'

end Incremental
