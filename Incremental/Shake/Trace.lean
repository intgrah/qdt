module

public import Incremental.Shake.Standard

namespace Incremental

namespace Trace

public inductive DepNode (Q : Type) where
  | mk (q : Q) (durationNs : Nat) (children : Array (DepNode Q))

public abbrev Forest (Q : Type) := Array (DepNode Q)

public abbrev TraceT (Q : Type) (m : Type → Type) := StateT (Forest Q) m

variable {Q : Type} {m : Type → Type} {α : Type}

@[inline]
def bracket [Monad m] [MonadLiftT BaseIO m] (q : Q) (body : TraceT Q m α) :
    TraceT Q m α := fun outer => do
  let t₀ ← liftM (m := m) (IO.monoNanosNow : BaseIO Nat)
  let (a, inner) ← body #[]
  let t₁ ← liftM (m := m) (IO.monoNanosNow : BaseIO Nat)
  return (a, outer.push (.mk q (t₁ - t₀) inner))

@[inline]
public def run [Monad m] (x : TraceT Q m α) : m (α × Forest Q) :=
  StateT.run x #[]

end Trace

public def ShakeTrace
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    [MonadLiftT BaseIO m] :
    Build ℭ J tasks (Trace.TraceT ℭ.Q m) Id :=
  Shake ℭ J hI hR tasks (m := Trace.TraceT ℭ.Q m) Trace.bracket

end Incremental
