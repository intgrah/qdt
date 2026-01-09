import Qdt.MLTT.Weakening

namespace Qdt

def Judgement.substAt {n} (c : Idx (n + 1)) (s : Tm n) : Judgement (n + 1) → Judgement n
  | Ctx.WF => Ctx.WF
  | Ty.WF T => Ty.WF (Ty.substAt c s T)
  | Tm.HasType t T => Tm.HasType (Tm.substAt c s t) (Ty.substAt c s T)
  | Tm.Eq t₁ t₂ T => Tm.Eq (Tm.substAt c s t₁) (Tm.substAt c s t₂) (Ty.substAt c s T)
  | Ty.Eq T₁ T₂ => Ty.Eq (Ty.substAt c s T₁) (Ty.substAt c s T₂)

def Judgement.subst {n} : Tm n → Judgement (n + 1) → Judgement n :=
  Judgement.substAt 0

instance {n} : GetElem (Judgement (n + 1)) (Tm n) (Judgement n) fun _ _ => True where
  getElem 𝒿 s _ := Judgement.subst s 𝒿

/-- HoTT book A.2.2, subst. -/
theorem Derives.subst' {m n n'}
    {Γ : Ctx 0 n'} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) n'}
    {𝒿 : Judgement n'} {x a A}
    (hn' : n' = n + 1)
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : Γ₁ ⊢ a : A)
    (h𝒿 : Γ ⊢ 𝒿) :
    (Γ₁ ++ (hn' ▸ Γ₂).subst a ⊢ (hn' ▸ 𝒿).substAt ⟨n - m, by have := Γ₂.le; omega⟩
      ((by have := Γ₂.le; omega : m + (n - m) = n) ▸ a.shift (n - m))) := by
  induction h𝒿 generalizing Γ₁ m x
  -- Easy inductive cases
  all_goals
    try subst hn' hΓ
    simp only [Judgement.substAt, Ty.substAt, Tm.substAt]
    try derives_constructor apply_rules

  case empty => contradiction
  case extend => sorry
  case el_form _ _ ih =>
      have h := ih rfl rfl ha
      rw [Judgement.substAt, Ty.substAt] at h
      exact Derives.el_form h
  case el_form_eq _ _ ih =>
      have h := ih rfl rfl ha
      rw [Judgement.substAt, Ty.substAt] at h
      exact Derives.el_form_eq h
  case pi_form _ _ _ _ _ ihA ihB =>
      apply Derives.pi_form (ihA rfl rfl ha)
      sorry
  case pi_form_eq => sorry
  case pi_intro_eq => sorry
  case pi_elim_eq => sorry
  case pi_comp => sorry
  case pi_uniq _ ih =>
      have h := ih rfl rfl ha
      rw [Judgement.substAt, Ty.substAt] at h
      simp only [Tm.substAt_succ_shift_comm]
      exact Derives.pi_uniq h
  case var => sorry
  case pi_intro => sorry
  case pi_elim _ _ ihf iha => sorry

theorem Derives.subst {m n}
    {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {𝒿 x a A} :
    (Γ₁ ⊢ a : A) →
    (Γ₁.snoc ⟨x, A⟩ ++ Γ₂ ⊢ 𝒿) →
    (Γ₁ ++ Γ₂.subst a ⊢ 𝒿.substAt ⟨n - m, by have := Γ₂.le; omega⟩
      ((by have := Γ₂.le; omega : m + (n - m) = n) ▸ a.shift (n - m))) :=
  Derives.subst' (n' := n + 1) (Γ := Γ₁.snoc ⟨x, A⟩ ++ Γ₂) rfl rfl

theorem Derives.subst_end {n}
    {Γ : Ctx 0 n} {𝒿 x a A}
    (ha : Γ ⊢ a : A)
    (h𝒿 : Γ.snoc ⟨x, A⟩ ⊢ 𝒿) :
    (Γ ⊢ 𝒿[a]) := by
  have heq :
      letI k := n - n
      (h : n + k = n) → a = h ▸ a.shift k :=
    Eq.subst
      (motive := fun k => (h : n + k = n) → a = h ▸ a.shift k)
      (Nat.sub_self n).symm
      (by simp)
  simpa [← heq] using Derives.subst (Γ₂ := Tele.nil) ha h𝒿

end Qdt
