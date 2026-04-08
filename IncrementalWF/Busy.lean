module

public import IncrementalWF.Basic

namespace Incremental

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  (m : Type → Type) [Pure m]

public def Busy : Build Monad ℭ m J where
  σ := J
  init := id
  inputs := Input.get
  set i v := fun store => Input.set store i v
  build tasks store q :=
    pure (⟨tasks.eval (Input.get store) q, rfl⟩, store)

end Incremental
