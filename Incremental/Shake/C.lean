module

public import Incremental.Shake.Store

namespace Incremental

open Std (DHashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

instance : Inhabited (Tasks ℭ → ∀ q, ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J) where
  default tasks q s := ⟨compute tasks (Input.get s.inputs) q, s⟩

@[extern "lean_shake_build"]
public opaque shakeCBuild
    {ℭ : BuildConfig}
    [BEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    {J : Type} [Input ℭ J] :
    Tasks ℭ → ∀ q,
    ShakeRT.Store ℭ J → ℭ.R q × ShakeRT.Store ℭ J

@[expose] public def ShakeC (tasks : Tasks ℭ) : Build ℭ J tasks Id Id where
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
