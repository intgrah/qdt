module

import all Init.System.ST

@[expose] public section

variable {ε σ : Type}

instance : LawfulMonadAttach (ST σ) where
  map_attach := rfl
  canReturn_map_imp := by
    intro α P x a ⟨s, _, hxs⟩
    let (eq := h) ⟨⟨a, hs⟩, _⟩ := x s
    simp only [Functor.map, ST.bind, h] at hxs
    cases hxs
    exact hs

instance : LawfulMonadAttach (EST ε σ) where
  map_attach {_ x} := by
    funext s
    simp only [Functor.map, EST.bind, MonadAttach.attach]
    split
    next _ _ h_outer =>
      split at h_outer
      next h => cases h_outer; exact h.symm
      next h => cases h_outer
    next _ _ h_outer =>
      split at h_outer
      next h => cases h_outer
      next h => cases h_outer; exact h.symm
  canReturn_map_imp := by
    intro _ _ x _ ⟨s, _, hxs⟩
    cases h : x s with
    | ok val _ =>
      simp only [Functor.map, EST.bind, h] at hxs
      cases hxs
      exact val.property
    | error _ _ =>
      simp only [Functor.map, EST.bind, h] at hxs
      cases hxs

instance : LawfulMonadAttach BaseIO := inferInstanceAs (LawfulMonadAttach (ST IO.RealWorld))
instance : LawfulMonadAttach (EIO ε) := inferInstanceAs (LawfulMonadAttach (EST ε IO.RealWorld))
