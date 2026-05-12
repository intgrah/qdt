module

public import Incremental.ShakeStore

namespace Incremental

open Std (DHashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

instance
    {ℭ : BuildConfig}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    {J : Type} [Input ℭ J] :
    Inhabited (Tasks Monad ℭ → ∀ q, ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J) :=
  ⟨sorry⟩

@[extern "lean_shake_build"]
public opaque shakeCBuild
    {ℭ : BuildConfig}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    {J : Type} [Input ℭ J] :
    Tasks Monad ℭ → ∀ q,
    ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J

@[expose] public def ShakeC (tasks : Tasks Monad ℭ) : Build Monad ℭ J tasks Id where
  cId := Id.instMonad
  σ := ShakeRT.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store => { store with inputs := Input.set store.inputs i v }
  build q store :=
    let (r, s) := shakeCBuild tasks q store
    (⟨r, sorry⟩, s)

end Incremental
