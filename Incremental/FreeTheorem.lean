module

public import Incremental.Basic

@[expose] public section

namespace Incremental

variable {ℭ : BuildConfig} {q₀ α}

namespace Task

namespace Monad

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

axiom freeTheorem
    {κ₁ κ₂ : Type → Type} [Monad κ₁] [Monad κ₂]
    (t : Task Monad ℭ q₀ α)
    (F : Action κ₁ κ₂)
    (ι₁ : ∀ i, κ₁ (ℭ.V i))
    (ι₂ : ∀ i, κ₂ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel q q₀ → κ₁ (ℭ.R q))
    (fetch₂ : ∀ q, ℭ.rel q q₀ → κ₂ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₂ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (fetch₂ q hq)) :
    F.rel Eq (t κ₁ ι₁ fetch₁) (t κ₂ ι₂ fetch₂)

end Monad

namespace Applicative

structure Action (κ₁ κ₂ : Type → Type) [Applicative κ₁] [Applicative κ₂] where
  rel {α β : Type} :
    (α → β → Prop) →
    (κ₁ α → κ₂ β → Prop)
  rel_pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    R a b → rel R (pure a) (pure b)
  rel_seq
    {α₁ α₂ β₁ β₂ : Type}
    {R : α₁ → α₂ → Prop} {S : β₁ → β₂ → Prop}
    {f : κ₁ (α₁ → β₁)} {g : κ₂ (α₂ → β₂)}
    {x : κ₁ α₁} {y : κ₂ α₂} :
    rel (fun fa fb => ∀ a b, R a b → S (fa a) (fb b)) f g →
    rel R x y →
    rel S (f <*> x) (g <*> y)

axiom freeTheorem
    {κ₁ κ₂ : Type → Type} [Applicative κ₁] [Applicative κ₂]
    (t : Task Applicative ℭ q₀ α)
    (F : Action κ₁ κ₂)
    (ι₁ : ∀ i, κ₁ (ℭ.V i))
    (ι₂ : ∀ i, κ₂ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel q q₀ → κ₁ (ℭ.R q))
    (fetch₂ : ∀ q, ℭ.rel q q₀ → κ₂ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₂ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (fetch₂ q hq)) :
    F.rel Eq (t κ₁ ι₁ fetch₁) (t κ₂ ι₂ fetch₂)

end Applicative

end Task

theorem Tasks.Monad.freeTheorem
    {κ : Type → Type} [Monad κ]
    (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q)
    (F : Task.Monad.Action κ Id)
    (ι₀ : ∀ i, ℭ.V i)
    (ι₁ : ∀ i, κ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel q q₀ → κ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₀ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (compute (inferInstance : Monad Id) tasks ι₀ q)) :
    F.rel Eq (tasks q₀ κ ι₁ fetch₁) (compute (inferInstance : Monad Id) tasks ι₀ q₀) := by
  have h := Task.Monad.freeTheorem (tasks q₀) F ι₁ ι₀ fetch₁
    (fun q _ => compute (inferInstance : Monad Id) tasks ι₀ q) hι hfetch
  have heval : tasks q₀ Id ι₀ (fun q _ => compute (inferInstance : Monad Id) tasks ι₀ q) =
      compute (inferInstance : Monad Id) tasks ι₀ q₀ := by
    conv => rhs; unfold compute
  simpa only [heval] using h

end Incremental
