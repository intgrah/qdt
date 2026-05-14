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

theorem bracket_canReturn [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    [MonadLiftT BaseIO m]
    (q : Q) (x : TraceT Q m α) (a : α) :
    MonadAttach.CanReturn (bracket q x) a → MonadAttach.CanReturn x a := by
  rintro ⟨s, s', hcan⟩
  have ⟨_, _, hrest₁⟩ := LawfulMonadAttach.canReturn_bind_imp' hcan
  have ⟨⟨a', inner⟩, hcan_inner, hrest₂⟩ :=
    LawfulMonadAttach.canReturn_bind_imp' (x := x #[]) hrest₁
  have ⟨_, _, hpure_can⟩ := LawfulMonadAttach.canReturn_bind_imp' hrest₂
  obtain ⟨rfl, _⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hpure_can)
  exact ⟨#[], inner, hcan_inner⟩

end Trace

public def ShakeTrace
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : MTasks ℭ)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    [MonadLiftT BaseIO m] :
    Build Monad ℭ J tasks (Trace.TraceT ℭ.Q m) Id :=
  Shake ℭ J hI hR tasks (m := Trace.TraceT ℭ.Q m)
    Trace.bracket Trace.bracket_canReturn

end Incremental
