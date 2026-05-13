module

public import Incremental.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]

public def Busy {c : (Type → Type) → Type 1} (cId : c Id) (tasks : Tasks c ℭ) :
    Build c ℭ J tasks Id Id where
  cId := cId
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build q store :=
    (⟨compute cId tasks (Input.get store) q, rfl⟩, store)

end Incremental
