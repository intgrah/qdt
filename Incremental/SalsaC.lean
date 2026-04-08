module

public import Incremental.Salsa

namespace Incremental

open Std (DHashMap HashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

@[extern "lean_salsa_build"]
public unsafe opaque salsaCBuild
    {ℭ : BuildConfig} {J : Type}
    [BEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
    [Input ℭ J] :
    Tasks Monad ℭ → ∀ q,
    Salsa.Store ℭ J → ℭ.R q × Salsa.Store ℭ J

@[expose] public unsafe def SalsaC : Build Monad ℭ J where
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
  build := salsaCBuild

end Incremental
