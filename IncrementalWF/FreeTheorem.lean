module

public import IncrementalWF.Basic

/-!
# Free theorem for `Task`

Free theorem of relational parametricity for `Task` type

## References

- Reynolds, J. C. (1983). Types, abstraction and parametric polymorphism.
- Wadler, P. (1989). Theorems for free!
- Voigtländer, J. (2009). Free theorems involving type constructor classes. ICFP 2009.
- Atkey, R. (2012). Relational parametricity for higher kinds.
-/

@[expose] public section

namespace Incremental

structure MonadAction (κ₁ κ₂ : Type → Type) [Monad κ₁] [Monad κ₂] where
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

variable
  {ℭ : BuildConfig} {ι₀ q₀ α}
  (t : Task Monad ℭ ι₀ q₀ α)
  {κ κ₁ κ₂ : Type → Type} [Monad κ] [Monad κ₁] [Monad κ₂]

axiom Task.freeTheorem
    (F : MonadAction κ₁ κ₂)
    (ι₁ : ∀ i, κ₁ (ℭ.V i))
    (ι₂ : ∀ i, κ₂ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel ι₀ q q₀ → κ₁ (ℭ.R q))
    (fetch₂ : ∀ q, ℭ.rel ι₀ q q₀ → κ₂ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₂ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (fetch₂ q hq)) :
    F.rel Eq (t κ₁ ι₁ fetch₁) (t κ₂ ι₂ fetch₂)

theorem Tasks.freeTheorem
    (tasks : Tasks Monad ℭ) (q₀ : ℭ.Q)
    (F : MonadAction κ Id)
    (ι₀ : ∀ i, ℭ.V i)
    (ι₁ : ∀ i, κ (ℭ.V i))
    (fetch₁ : ∀ q, ℭ.rel ι₀ q q₀ → κ (ℭ.R q))
    (hι : ∀ i, F.rel Eq (ι₁ i) (ι₀ i))
    (hfetch : ∀ q hq, F.rel Eq (fetch₁ q hq) (tasks.eval ι₀ q)) :
    F.rel Eq (tasks ι₀ q₀ κ ι₁ fetch₁) (tasks.eval ι₀ q₀) := by
  have h := Task.freeTheorem (tasks ι₀ q₀) F ι₁ ι₀ fetch₁
    (fun q _ => tasks.eval ι₀ q) hι hfetch
  have heval : tasks ι₀ q₀ Id ι₀ (fun q _ => tasks.eval ι₀ q) = tasks.eval ι₀ q₀ := by
    conv => rhs; unfold Tasks.eval
  simpa only [heval] using h

end Incremental
