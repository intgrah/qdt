module

public import Incremental.Salsa

namespace Incremental

open Std (DHashMap HashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

instance : Inhabited (Tasks ℭ → ∀ q, Salsa.Store ℭ J → ℭ.R q × Salsa.Store ℭ J) where
  default tasks q s := ⟨compute tasks (Input.get s.inputs) q, s⟩

@[extern "lean_salsa_build"]
public opaque salsaCBuild
    {ℭ : BuildConfig} {J : Type}
    [BEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    [Input ℭ J] :
    Tasks ℭ → ∀ q,
    Salsa.Store ℭ J → ℭ.R q × Salsa.Store ℭ J

@[expose] public def SalsaC (tasks : Tasks ℭ) : Build ℭ J tasks Id Id where
  σ := Salsa.Store ℭ J
  init inputs := {
    inputs
    revision := 0
    memos := DHashMap.emptyWithCapacity 1024
    inputRevisions := HashMap.emptyWithCapacity 64
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    let revision := store.revision + 1
    let inputs := Input.set store.inputs i v
    let inputRevisions := store.inputRevisions.insert i revision
    { store with inputs, revision, inputRevisions }
  build q store :=
    let (r, s) := salsaCBuild tasks q store
    (⟨r, sorry⟩, s)

end Incremental
