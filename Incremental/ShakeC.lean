module

public import Incremental.ShakeStore

namespace Incremental

open Std (DHashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

instance {ℭ : BuildConfig} {J : Type}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    [Input ℭ J] :
    Nonempty (Tasks Monad ℭ → ∀ q, ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J) :=
  ⟨sorry⟩

@[extern "lean_shake_build"]
public opaque shakeCBuild
    {ℭ : BuildConfig} {J : Type}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    [Input ℭ J] :
    Tasks Monad ℭ → ∀ q,
    ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J

public def ShakeC : Build Monad ℭ J where
  cId := inferInstance
  σ := ShakeRT.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store => { store with inputs := Input.set store.inputs i v }
  build tasks q store :=
    let (r, s) := shakeCBuild tasks q store
    (⟨r, sorry⟩, s)

end Incremental
