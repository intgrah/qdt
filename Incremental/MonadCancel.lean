module

public import Init.Control.Lawful.MonadAttach.Lemmas

@[expose] public section

namespace Incremental

universe u v

class MonadCancel (m : Type u → Type v) where
  CanCancel {α : Type u} : m α → Prop
  checkpoint : m PUnit

class LawfulMonadCancel (m : Type u → Type v)
    [Monad m] [MonadAttach m] [MonadCancel m] : Prop where
  canCancel_bind_imp : ∀ {α β} (ma : m α) (k : α → m β),
    MonadCancel.CanCancel (ma >>= k) →
      MonadCancel.CanCancel ma ∨
      ∃ a, MonadAttach.CanReturn ma a ∧ MonadCancel.CanCancel (k a)
  not_canCancel_pure : ∀ {α} (a : α), ¬MonadCancel.CanCancel (pure a : m α)

instance : MonadCancel Id where
  CanCancel _ := False
  checkpoint := pure ⟨⟩

instance : LawfulMonadCancel Id where
  canCancel_bind_imp _ _ h := absurd h id
  not_canCancel_pure _ := id

end Incremental
