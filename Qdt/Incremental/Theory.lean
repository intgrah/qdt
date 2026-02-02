namespace Incremental

universe u

/-- Provides the ability to call `fetch q` -/
abbrev TaskT (Q : Type u) (R : Q → Type u) (m : Type u → Type u) :=
  ReaderT (∀ q, m (R q)) m

namespace TaskT

variable {Q : Type u} {R : Q → Type u} {m : Type u → Type u} [Monad m]

/-- Fetch the result of query q within a task computation -/
@[inline] def fetch (q : Q) : TaskT Q R m (R q) := fun f => f q

end TaskT

end Incremental
