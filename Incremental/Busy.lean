module

public import Incremental.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]

public def Busy (tasks : Tasks ℭ) :
    Build ℭ J tasks Id Id where
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build q store :=
    (⟨compute tasks (Input.get store) q, rfl⟩, store)

end Incremental
