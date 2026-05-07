module

public import Incremental.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]

public def Busy {c : (Type → Type) → Type 1} (cId : c Id) :
    Build c ℭ J where
  cId := cId
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q store :=
    (Subtype.mk (compute cId tasks (Input.get store) q) rfl, store)

end Incremental
