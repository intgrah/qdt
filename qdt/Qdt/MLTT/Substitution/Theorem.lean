import Qdt.MLTT.Weakening

namespace Qdt

def Judgement.subst {n} (s : Tm n) : Judgement (n + 1) → Judgement n
  | Ctx.WF => Ctx.WF
  | Ty.WF A => Ty.WF A[s]
  | Tm.HasType a A => Tm.HasType a[s] A[s]
  | Tm.Eq a b A => Tm.Eq a[s] b[s] A[s]
  | Ty.Eq A B => Ty.Eq A[s] B[s]

instance {n} : GetElem (Judgement (n + 1)) (Tm n) (Judgement n) fun _ _ => True where
  getElem 𝒿 s _ := Judgement.subst s 𝒿

theorem Derives.subst {n n'}
    {Γ : Ctx 0 n} {Γ' : Ctx 0 n'}
    {𝒿 : Judgement n'}
    {x a A}
    (hn' : n' = n + 1)
    (hΓ' : Γ' = hn' ▸ Γ.snoc ⟨x, A⟩)
    (ha : Γ ⊢ a : A)
    (h𝒿 : Γ' ⊢ 𝒿) :
    (Γ ⊢ (hn' ▸ 𝒿)[a]) := by
  induction h𝒿
  -- Easy inductive cases
  all_goals
      try subst hn' hΓ'
      simp_all [GetElem.getElem, Judgement.subst, Ty.substAt, Tm.substAt]
      try derives_constructor assumption

  case empty => contradiction
  case extend => sorry
  case pi_form => sorry
  case pi_form_eq => sorry
  case pi_intro_eq => sorry
  case pi_elim_eq => sorry
  case pi_comp => sorry
  case pi_uniq => sorry
  case var => sorry
  case pi_intro => sorry
  case pi_elim => sorry
end Qdt
