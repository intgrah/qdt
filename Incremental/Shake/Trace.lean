module

public import Incremental.Shake.Standard

@[expose] public section

namespace Incremental

namespace Trace

inductive DepNode (Q : Type) where
  | mk (q : Q) (durationNs : Nat) (children : Array (DepNode Q))

abbrev Forest (Q : Type) := Array (DepNode Q)

abbrev TraceT (Q : Type) (m : Type → Type) := StateT (Forest Q) m

variable {Q : Type} {m : Type → Type} {α : Type}

@[inline]
def bracket [Monad m] [MonadLiftT BaseIO m] (q : Q) (body : TraceT Q m α) :
    TraceT Q m α := fun outer => do
  let t0 ← liftM (m := m) (IO.monoNanosNow : BaseIO Nat)
  let (a, inner) ← body #[]
  let t1 ← liftM (m := m) (IO.monoNanosNow : BaseIO Nat)
  pure (a, outer.push (.mk q (t1 - t0) inner))

@[inline]
def run [Monad m] (x : TraceT Q m α) : m (α × Forest Q) :=
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
