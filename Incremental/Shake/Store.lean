module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap)

variable (ℭ : BuildConfig)
  [BEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

namespace ShakeRT

public structure Memo (q₀ : ℭ.Q) where
  value : ℭ.R q₀
  queryDeps : HashMap ℭ.Q UInt64
  inputDeps : HashMap ℭ.I UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

public structure Store (J : Type) where
  inputs : J
  memos : DHashMap ℭ.Q (ShakeRT.Memo ℭ)

end ShakeRT

end Incremental
