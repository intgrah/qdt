module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

public def LessBusy : Build Monad ℭ J where
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q₀ := fun store =>
    let ι₀ := Input.get store
    runST fun σ => do
      let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024 : DHashMap ℭ.Q ℭ.R)
      let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
        if let some r := (← started.get).get? q then return r
        let r ← tasks ι₀ q (ST σ) (fun i => pure (ι₀ i)) (fun q₁ _hq => fetch q₁)
        started.modify (·.insert q r)
        return r
      termination_by (ℭ.wf ι₀).wrap q
      decreasing_by exact _hq
      return (← fetch q₀, store)

end Incremental
