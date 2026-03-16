module

public import Incremental.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]

public def Busy : Build Monad ℭ J where
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q₀ := do
    let store ← get
    let ι₀ := Input.get store
    let rec fetch (q : ℭ.Q) : ℭ.R q :=
      tasks ι₀ q Id ι₀ (fun q₁ _hq => fetch q₁)
    termination_by (ℭ.wf ι₀).wrap q
    decreasing_by exact _hq
    return fetch q₀

end Incremental
