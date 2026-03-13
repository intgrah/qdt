module

public import Incremental.Shake

namespace Incremental

open Std (DHashMap)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (J : Type) [Input I V J]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

@[extern "lean_shake_build"]
public opaque ShakeC.build'
    {I : Type} {V : I → Type} {Q : Type} {R : Q → Type} {J : Type}
    [BEq I] [Hashable I] [∀ i, Hashable (V i)]
    [BEq Q] [Hashable Q] [∀ q, Hashable (R q)]
    [Input I V J] :
    Tasks Monad I V Q R → ∀ q,
    Shake.Store I Q R J → Except BuildError (R q × Shake.Store I Q R J)

public def ShakeC : Build Monad I V Q R J where
  σ := Shake.Store I Q R J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  set i v := modify fun store => { store with inputs := Input.set store.inputs i v }
  build := ShakeC.build'

end Incremental
