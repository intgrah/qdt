import Qdt.MLTT.Judgements

namespace Qdt

theorem Ctx.get_weaken {m n}
    {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {x C}
    (i : Idx n) :
    Ctx.get (i.shiftAfter (n - m) 1) (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1) = (Ctx.get i (Γ₁ ++ Γ₂)).shiftAfter (n - m) 1 := by
  induction Γ₂ with
  | nil =>
      simp only [Nat.sub_self, Idx.shiftAfter]
      rfl
  | @snoc n' Γ₂ p ih =>
      have ⟨y, B⟩ := p
      have hle : m ≤ n' := Γ₂.le
      have ⟨i_val, hi⟩ := i
      match i_val with
      | 0 =>
        rw [Nat.succ_sub Γ₂.le]
        exact (Ty.shift_shift_comm (n' - m) B).symm
      | j + 1 =>
        have ih_spec := ih ⟨j, by omega⟩
        simp only [Idx.shiftAfter] at ih_spec
        show Ctx.get (if _ then _ else _) _ = _
        simp [Ctx.get]
        rw [Nat.succ_sub hle, Ty.shift_shift_comm]
        split
        · have h2 : n' - m ≤ j := by omega
          simp only [h2] at ih_spec
          exact congrArg (Ty.shift 1) ih_spec
        · have h2 : ¬ n' - m ≤ j := by omega
          simp only [h2] at ih_spec
          exact congrArg (Ty.shift 1) ih_spec

/-- Unified weakening theorem for all judgments. HoTT book A.2.2, wkg₁ and wkg₂. -/
theorem Derives.weaken {n m}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {𝒿 : Judgement n} {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : Γ₁ ⊢ C type)
    (h𝒿 : Γ ⊢ 𝒿) :
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ 𝒿.shiftAfter (n - m) 1) := by
  unfold Judgement.shiftAfter
  let Γ'' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
  induction h𝒿 generalizing Γ₁ x C with
  -- Context well-formedness
  | empty => cases Γ₂ with | nil => exact .extend hC
  | @extend _ _ _ _ hA ih =>
      cases Γ₂ with
      | nil => cases hΓ with | refl => exact .extend hC
      | snoc =>
          obtain ⟨hΓ', rfl⟩ := Tele.snoc.inj hΓ
          exact .extend (ih hΓ' hC)
  -- Type well-formedness
  | @pi_form _ Γ' y D _ _ _ ihA ihB =>
      apply Derives.pi_form (ihA hΓ hC)
      have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
  -- Type equality
  | trans_eq_ty _ _ ihAB ihBC => exact .trans_eq_ty (ihAB hΓ hC) (ihBC hΓ hC)
  | @pi_form_eq _ Γ' y D _ _ _ hA hB ihA ihB =>
      apply Derives.pi_form_eq (ihA hΓ hC)
      have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
  | el_form_eq _ ih => exact .el_form_eq (ih hΓ hC)
  -- Term equality
  | trans_eq_tm _ _ ihab ihbc => exact .trans_eq_tm (ihab hΓ hC) (ihbc hΓ hC)
  | @pi_intro_eq _ Γ' y _ _ D _ _ hA hB ihA ihB =>
      apply Derives.pi_intro_eq (ihA hΓ hC)
      have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
  | @pi_elim_eq n' Γ' y _ _ a' _ D E _ _ ihf iha =>
      let k := n' - m
      have ihf' : Γ'' ⊢ _ ≡ _ : .pi ⟨y, D.shiftAfter k 1⟩ (E.shiftAfter (k + 1) 1) := ihf hΓ hC
      have h := Derives.pi_elim_eq ihf' (iha hΓ hC)
      rw [Ty.shift_subst_comm] at h
      exact h
  | @pi_comp n' Γ' y a' b' D E _ _ ihB iha =>
      let k := n' - m
      have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB' : Γ''.snoc ⟨y, D.shiftAfter k 1⟩ ⊢ b'.shiftAfter (k + 1) 1 : E.shiftAfter (k + 1) 1 := by
        simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
      have h := Derives.pi_comp ihB' (iha hΓ hC)
      rw [Ty.shift_subst_comm, Tm.shift_subst_comm] at h
      exact h
  | @pi_uniq n' Γ' y D E f' hf ih =>
      have ihf := @ih Γ₁ Γ₂ x C hΓ hC
      have h := Derives.pi_uniq ihf
      have idx_shift :
          Idx.shiftAfter (n' - m + 1) 1 ⟨0, Nat.zero_lt_succ n'⟩ = ⟨0, Nat.zero_lt_succ (n' + 1)⟩ := by
        simp [Idx.shiftAfter]
      simp [Tm.shiftAfter, Tm.shift_shift_comm]
      exact h
  | conv_eq_tm _ _ ihheq ihhAB => exact .conv_eq_tm (ihheq hΓ hC) (ihhAB hΓ hC)
  -- Typing
  | @var n' Γ' _ i ih =>
      simp only [Tm.shiftAfter]
      subst hΓ
      have hget := @Ctx.get_weaken m n' Γ₁ Γ₂ x C i
      rw [← hget]
      exact .var (ih rfl hC) (i.shiftAfter (n' - m) 1)
  | @pi_intro _ Γ' y D body B hA hB ihA ihB =>
      apply Derives.pi_intro (ihA hΓ hC)
      have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
  | @pi_elim n' Γ' f a' y D E _ _ ihf iha =>
      let k := n' - m
      have ihf' : Γ'' ⊢ _ : .pi ⟨y, D.shiftAfter k 1⟩ (E.shiftAfter (k + 1) 1) := ihf hΓ hC
      have iha' : Γ'' ⊢ _ : D.shiftAfter k 1 := iha hΓ hC
      have h := Derives.pi_elim ihf' iha'
      have eq : (E.shiftAfter (k + 1) 1)[a'.shiftAfter k 1] = E[a'].shiftAfter k 1 := E.shift_subst_comm k a'
      rw [eq] at h
      exact h
  | _ => constructor <;> apply_rules

theorem Derives.presup {n}
    {Γ : Ctx 0 n}
    {𝒿 : Judgement n}
    (h𝒿 : Γ ⊢ 𝒿) :
    (Γ ⊢) := by
  induction h𝒿 with
  | empty => constructor
  | extend => constructor; assumption
  | _ => assumption

theorem Ctx.WF.drop {n}
    {Γ : Ctx 0 n} {x A} :
    (Γ.snoc ⟨x, A⟩ ⊢) →
    (Γ ⊢)
  | .extend hA => hA.presup

theorem Ctx.subst_snoc {m n x B} (a : Tm m) (Γ : Ctx (m + 1) (n + 1)) :
    Ctx.subst a (Γ.snoc ⟨x, B⟩) =
    (Ctx.subst a Γ).snoc ⟨x, B.substAt ⟨n - m, by omega⟩ (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ.le) ▸ a.shift (n - m))⟩ :=
  rfl

private theorem addrc {n k : Nat} : n + 1 + k = n + k + 1 := Nat.add_right_comm n 1 k

theorem Tm.cast_shiftAfter {n₁ n₂ : Nat} (h : n₁ = n₂) (m s : Nat) (t : Tm n₁) :
    (h ▸ t).shiftAfter m s = (congrArg (· + s) h ▸ t.shiftAfter m s) := by cases h; rfl
theorem Ty.cast_shiftAfter {n₁ n₂ : Nat} (h : n₁ = n₂) (m s : Nat) (T : Ty n₁) :
    (h ▸ T).shiftAfter m s = (congrArg (· + s) h ▸ T.shiftAfter m s) := by cases h; rfl

mutual

theorem Ty.shiftAfter_succ {n : Nat} (m k : Nat) :
    (T : Ty n) → T.shiftAfter m (k + 1) = (T.shiftAfter m k).shiftAfter m 1
  | 𝑢 => rfl
  | .el t => congrArg Ty.el (Tm.shiftAfter_succ m k t)
  | .pi ⟨x, A⟩ B => by
      simp only [Ty.shiftAfter]
      have ihA := Ty.shiftAfter_succ m k A
      have ihB := Ty.shiftAfter_succ (m + 1) k B
      simp only [ihA, Ty.cast_shiftAfter addrc (m + 1) 1, ihB]
termination_by structural T => T

theorem Tm.shiftAfter_succ {n : Nat} (m k : Nat) :
    (t : Tm n) → t.shiftAfter m (k + 1) = (t.shiftAfter m k).shiftAfter m 1
  | .var ⟨i, hi⟩ => by
      simp only [Tm.shiftAfter, Idx.shiftAfter]
      by_cases h : m ≤ i
      · have h' : m ≤ i + k := Nat.le_add_right_of_le h
        simp only [h, h', ↓reduceIte, Nat.add_assoc]
      · simp only [h, ↓reduceIte]
  | .const _ => rfl
  | .lam ⟨x, A⟩ body => by
      simp only [Tm.shiftAfter]
      have ihA := Ty.shiftAfter_succ m k A
      have ihBody := Tm.shiftAfter_succ (m + 1) k body
      simp only [ihA, Tm.cast_shiftAfter addrc (m + 1) 1, ihBody]
  | .app f a => by
      simp only [Tm.shiftAfter, Tm.shiftAfter_succ m k f, Tm.shiftAfter_succ m k a]
  | .piHat x a b => by
      simp only [Tm.shiftAfter]
      have iha := Tm.shiftAfter_succ m k a
      have ihb := Tm.shiftAfter_succ (m + 1) k b
      simp only [iha, Tm.cast_shiftAfter addrc (m + 1) 1, ihb]
  | .proj i t => congrArg (Tm.proj i) (Tm.shiftAfter_succ m k t)
  | .letE x ty t body => by
      simp only [Tm.shiftAfter]
      have ihty := Ty.shiftAfter_succ m k ty
      have iht := Tm.shiftAfter_succ m k t
      have ihbody := Tm.shiftAfter_succ (m + 1) k body
      simp only [ihty, iht, Tm.cast_shiftAfter addrc (m + 1) 1, ihbody]
termination_by structural t => t

end

theorem Tm.shift_succ {n : Nat} (k : Nat) (t : Tm n) : t.shift (k + 1) = (t.shift k).shift 1 :=
  Tm.shiftAfter_succ 0 k t

end Qdt
