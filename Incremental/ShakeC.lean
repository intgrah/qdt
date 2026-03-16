module

public import Incremental.Shake

namespace Incremental

open Std (DHashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

@[extern "lean_shake_build"]
unsafe opaque ShakeC.build_impl
    {ℭ : BuildConfig} {J : Type}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    [Input ℭ J] :
    Tasks Monad ℭ → ∀ q,
    Shake.Store ℭ J → ℭ.R q × Shake.Store ℭ J

public unsafe def ShakeC : Build Monad ℭ J where
  σ := Shake.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store => { store with inputs := Input.set store.inputs i v }
  build := ShakeC.build_impl

end Incremental
