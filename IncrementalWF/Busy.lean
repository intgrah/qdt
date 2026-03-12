module

public import IncrementalWF.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]

public def Busy : Build Monad ℭ J where
  σ := J
  init := id
  inputs := Input.get
  set i v := fun store => Input.set store i v
  build tasks store q :=
    (⟨tasks.eval (Input.get store) q, rfl⟩, store)

end Incremental
