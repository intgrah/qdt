module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Task.Monad

structure Action (κ₁ κ₂ : Type → Type) [Monad κ₁] [Monad κ₂] where
  rel {α β : Type} :
    (α → β → Prop) →
    (κ₁ α → κ₂ β → Prop)
  rel_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    R a b → rel R (pure a) (pure b)
  rel_bind
    {α₁ α₂ β₁ β₂ : Type}
    {R : α₁ → α₂ → Prop} {S : β₁ → β₂ → Prop}
    {ma : κ₁ α₁} {mb : κ₂ α₂}
    {ka : α₁ → κ₁ β₁} {kb : α₂ → κ₂ β₂} :
    rel R ma mb →
    (∀ a b, R a b → rel S (ka a) (kb b)) →
    rel S (ma >>= ka) (mb >>= kb)

end Task.Monad

structure MTask (ℭ : BuildConfig) (q₀ : ℭ.Q) (α : Type) : Type 1 where
  fn : Task Monad ℭ q₀ α
  param : ∀ {κ₁ κ₂ : Type → Type} [Monad κ₁] [Monad κ₂]
      (A : Task.Monad.Action κ₁ κ₂)
      (ι₁ : ∀ i, κ₁ (ℭ.V i)) (ι₂ : ∀ i, κ₂ (ℭ.V i))
      (f₁ : ∀ q (_ : ℭ.rel q q₀), κ₁ (ℭ.R q))
      (f₂ : ∀ q (_ : ℭ.rel q q₀), κ₂ (ℭ.R q)),
    (∀ i, A.rel Eq (ι₁ i) (ι₂ i)) →
    (∀ q hq, A.rel Eq (f₁ q hq) (f₂ q hq)) →
    A.rel Eq (fn κ₁ ι₁ f₁) (fn κ₂ ι₂ f₂)

namespace MTask

variable {ℭ : BuildConfig} {q₀ : ℭ.Q}

@[inline] def pure {α : Type} (a : α) : MTask ℭ q₀ α where
  fn := fun _ [_] _ _ => Pure.pure a
  param A _ _ _ _ _ _ := A.rel_pure rfl

@[inline] def bind {α β : Type} (m : MTask ℭ q₀ α) (k : α → MTask ℭ q₀ β) :
    MTask ℭ q₀ β where
  fn := fun g [_] inp fe => m.fn g inp fe >>= fun a => (k a).fn g inp fe
  param A ι₁ ι₂ f₁ f₂ hι hfe :=
    A.rel_bind (m.param A ι₁ ι₂ f₁ f₂ hι hfe)
      (fun a _b hab => hab ▸ (k a).param A ι₁ ι₂ f₁ f₂ hι hfe)

@[inline] def map {α β : Type} (f : α → β) (m : MTask ℭ q₀ α) :
    MTask ℭ q₀ β := bind m (pure ∘ f)

instance : Monad (MTask ℭ q₀) where
  pure := pure
  bind := bind
  map := map

@[inline] def input (i : ℭ.I) : MTask ℭ q₀ (ℭ.V i) where
  fn := fun _ [_] inp _ => inp i
  param _ _ _ _ _ hι _ := hι i

@[inline] def fetch (q : ℭ.Q) (h : ℭ.rel q q₀) : MTask ℭ q₀ (ℭ.R q) where
  fn := fun _ [_] _ fe => fe q h
  param _ _ _ _ _ _ hfe := hfe q h

end MTask

instance {ℭ : BuildConfig} {q₀ : ℭ.Q} {α : Type} :
    CoeFun (MTask ℭ q₀ α) (fun _ => Task Monad ℭ q₀ α) :=
  ⟨MTask.fn⟩

def MTasks (ℭ : BuildConfig) : Type 1 :=
  ∀ q₀, MTask ℭ q₀ (ℭ.R q₀)

namespace MTasks

variable {ℭ : BuildConfig}

@[inline] def fn (tasks : MTasks ℭ) : Tasks Monad ℭ :=
  fun q₀ => (tasks q₀).fn

instance : Coe (MTasks ℭ) (Tasks Monad ℭ) := ⟨MTasks.fn⟩

@[inline] def computeM (tasks : MTasks ℭ) (ι : ∀ i, ℭ.V i) (q : ℭ.Q) : ℭ.R q :=
  Incremental.computeM tasks.fn ι q

theorem freeTheorem
    {κ : Type → Type} [Monad κ]
    (tasks : MTasks ℭ) (q₀ : ℭ.Q)
    (F : Task.Monad.Action κ Id)
    (ι₀ : ∀ i, ℭ.V i)
    (ι₁ : ∀ i, κ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel q q₀ → κ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₀ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (tasks.computeM ι₀ q)) :
    F.rel Eq ((tasks q₀).fn κ ι₁ fetch₁) (tasks.computeM ι₀ q₀) := by
  have h := (tasks q₀).param F ι₁ ι₀ fetch₁
    (fun q _ => tasks.computeM ι₀ q) hι hfetch
  have heval : (tasks q₀).fn Id ι₀ (fun q _ => tasks.computeM ι₀ q) =
      tasks.computeM ι₀ q₀ := by
    show _ = Incremental.compute Id.instMonad tasks.fn ι₀ q₀
    conv => rhs; unfold compute
    rfl
  simpa only [heval] using h

end MTasks

end Incremental
