module
-- import Qdt.MLTT.Declarative
@[expose] public section

-- namespace Qdt

-- def Judgement.weakenAt {n} (d : Nat) : Judgement n → Judgement (n + 1)
--   | Ctx.WF => Ctx.WF
--   | Ty.WF A => Ty.WF (A.subst (Subst.shift.upN d))
--   | Tm.HasType a A => Tm.HasType (a.subst (Subst.shift.upN d)) (A.subst (Subst.shift.upN d))
--   | Tm.Eq a b A => Tm.Eq (a.subst (Subst.shift.upN d)) (b.subst (Subst.shift.upN d)) (A.subst (Subst.shift.upN d))
--   | Ty.Eq A B => Ty.Eq (A.subst (Subst.shift.upN d)) (B.subst (Subst.shift.upN d))

-- abbrev Judgement.weaken {n} : Judgement n → Judgement (n + 1) := Judgement.weakenAt 0

-- theorem Ctx.get_weaken {m n}
--     {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
--     {x C}
--     (i : Idx n) :
--     Ctx.get (Fin.succ i) (Γ₁.snoc ⟨x, C⟩ ++ Ctx.weaken Γ₂) =
--     (Ctx.get i (Γ₁ ++ Γ₂)).subst (Subst.shift.upN (n - m)) := by
--   induction Γ₂ with
--   | nil =>
--       simp only [Ctx.weaken_nil, Tele.append_nil, Nat.sub_self, Subst.upN_zero]
--       rfl
--   | @snoc n' Γ₂ p ih =>
--       have ⟨y, B⟩ := p
--       have hle : m ≤ n' := Γ₂.le
--       have ⟨i_val, hi⟩ := i
--       rw [Ctx.weaken_snoc]
--       match i_val with
--       | 0 =>
--           -- Goal: get 1 ... = (↑B).subst (shift.upN (n'+1 - m))
--           rw [Nat.succ_sub hle]
--           simp only [Ctx.get, Subst.upN_succ]
--           -- Need: ↑↑B = (↑B).subst shift.up.upN (n' - m)
--           -- This is Ty.shift_shiftAfter equivalent
--           sorry
--       | j + 1 =>
--           have ih_spec := ih ⟨j, by omega⟩
--           simp only [Ctx.get]
--           rw [Nat.succ_sub hle]
--           -- Use ih and Ty.shift_shiftAfter commutation
--           sorry

-- /-! ## Weakening Lemma -/

-- theorem Derives.weaken {n m}
--     {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
--     {𝒿 x C}
--     (hΓ : Γ = Γ₁ ++ Γ₂)
--     (hC : Γ₁ ⊢ C type)
--     (h𝒿 : Γ ⊢ 𝒿) :
--     (Γ₁.snoc ⟨x, C⟩ ++ Ctx.weaken Γ₂ ⊢ 𝒿.weakenAt (n - m)) := by
--   induction h𝒿 generalizing Γ₁

--   all_goals
--     simp only [Judgement.weakenAt]
--     try derives_constructor apply_rules

--   case empty => cases Γ₂ with | nil => exact .extend hC
--   case extend hA ih =>
--       cases Γ₂ with
--       | nil => cases hΓ with | refl => exact .extend hC
--       | snoc =>
--           obtain ⟨hΓ', rfl⟩ := Tele.snoc.inj hΓ
--           exact .extend (ih hΓ' hC)
--   case pi_form _ Γ' y D _ _ _ ihA ihB =>
--       apply Derives.pi_form (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) (by rw [hΓ]; rfl) hC
--       -- ihB' has weakenAt (n+1 - m) = weakenAt ((n - m) + 1) when m ≤ n
--       simpa [Ctx.weaken_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_form_eq _ Γ' y D _ _ _ _ _ ihA ihB =>
--       apply Derives.pi_form_eq (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) (by rw [hΓ]; rfl) hC
--       simpa [Ctx.weaken_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_intro_eq _ Γ' y _ _ D _ _ hA hB ihA ihB =>
--       apply Derives.pi_intro_eq (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) (by rw [hΓ]; rfl) hC
--       simpa [Ctx.weaken_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_elim_eq _ _ ihf iha =>
--       let Γ'' := Γ₁.snoc ⟨x, C⟩ ++ Ctx.weaken Γ₂
--       have h := Derives.pi_elim_eq (Γ := Γ'') (ihf hΓ hC) (iha hΓ hC)
--       simp only [GetElem.getElem] at h ⊢
--       -- Need Ty.shift_subst_comm equivalent for upN
--       sorry
--   case pi_comp n' Γ' y a' b' D E hB ha ihB iha =>
--       let Γ'' := Γ₁.snoc ⟨x, C⟩ ++ Ctx.weaken Γ₂
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) (by rw [hΓ]; rfl) hC
--       simp [Ctx.weaken_snoc, Nat.succ_sub Γ₂.le] at ihB'
--       have h := Derives.pi_comp ihB' (iha hΓ hC)
--       simp only [GetElem.getElem] at h ⊢
--       -- Need Ty.shift_subst_comm and Tm.shift_subst_comm equivalents
--       sorry
--   case var _ i ih =>
--       rw [hΓ, ← Ctx.get_weaken]
--       exact .var (ih hΓ hC) _
--   case pi_intro _ Γ' y D body B hA hB ihA ihB =>
--       apply Derives.pi_intro (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) (by rw [hΓ]; rfl) hC
--       simpa [Ctx.weaken_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_elim _ _ ihf iha =>
--       let Γ'' := Γ₁.snoc ⟨x, C⟩ ++ Ctx.weaken Γ₂
--       have h := Derives.pi_elim (Γ := Γ'') (ihf hΓ hC) (iha hΓ hC)
--       simp only [GetElem.getElem] at h ⊢
--       -- Need Ty.shift_subst_comm equivalent
--       sorry
--   case pi_uniq hf ih =>
--       sorry -- Complex case

-- theorem Derives.presup {n} {Γ : Ctx 0 n} {𝒿}
--     (h𝒿 : Γ ⊢ 𝒿) :
--     (Γ ⊢) := by
--   induction h𝒿 with try constructor
--   | extend => assumption
--   | _ => assumption

-- theorem Ctx.WF.drop {n} {Γ : Ctx 0 n} {x A} :
--     (Γ.snoc ⟨x, A⟩ ⊢) →
--     (Γ ⊢)
--   | .extend hA => hA.presup

-- end Qdt

-- /-
-- import Qdt.MLTT.Declarative

-- namespace Qdt

-- def Judgement.shiftAfter {n} (m s : Nat) : Judgement n → Judgement (n + s)
--   | Ctx.WF => Ctx.WF
--   | Ty.WF A => Ty.WF (A.shiftAfter m s)
--   | Tm.HasType a A => Tm.HasType (a.shiftAfter m s) (A.shiftAfter m s)
--   | Tm.Eq a b A => Tm.Eq (a.shiftAfter m s) (b.shiftAfter m s) (A.shiftAfter m s)
--   | Ty.Eq A B => Ty.Eq (A.shiftAfter m s) (B.shiftAfter m s)

-- theorem Ctx.get_weaken {m n}
--     {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
--     {x C}
--     (i : Idx n) :
--     Ctx.get (i.shiftAfter (n - m) 1) (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1) = (Ctx.get i (Γ₁ ++ Γ₂)).shiftAfter (n - m) 1 := by
--   induction Γ₂ with
--   | nil =>
--       simp only [Nat.sub_self, Idx.shiftAfter]
--       rfl
--   | @snoc n' Γ₂ p ih =>
--       have ⟨y, B⟩ := p
--       have hle : m ≤ n' := Γ₂.le
--       have ⟨i_val, hi⟩ := i
--       match i_val with
--       | 0 =>
--         rw [Nat.succ_sub Γ₂.le]
--         exact (Ty.shift_shiftAfter (n' - m) B).symm
--       | j + 1 =>
--         have ih_spec := ih ⟨j, by omega⟩
--         simp only [Idx.shiftAfter] at ih_spec
--         show Ctx.get (if _ then _ else _) _ = _
--         simp [Ctx.get]
--         rw [Nat.succ_sub hle, Ty.shift_shiftAfter]
--         split
--         · have h2 : n' - m ≤ j := by omega
--           simp only [h2] at ih_spec
--           exact congrArg (Ty.shift 1) ih_spec
--         · have h2 : ¬ n' - m ≤ j := by omega
--           simp only [h2] at ih_spec
--           exact congrArg (Ty.shift 1) ih_spec

-- /-- HoTT book A.2.2, wkg₁ and wkg₂. -/
-- theorem Derives.weaken' {n m}
--     {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
--     {𝒿 x C}
--     (hΓ : Γ = Γ₁ ++ Γ₂)
--     (hC : Γ₁ ⊢ C type)
--     (h𝒿 : Γ ⊢ 𝒿) :
--     (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ 𝒿.shiftAfter (n - m) 1) := by
--   unfold Judgement.shiftAfter
--   let Γ'' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
--   induction h𝒿 generalizing Γ₁ x C
--   -- Easy inductive cases
--   all_goals
--     simp only [Tm.shiftAfter, Tm.shift_shiftAfter]
--     try derives_constructor apply_rules

--   case empty => cases Γ₂ with | nil => exact .extend hC
--   case extend hA ih =>
--       cases Γ₂ with
--       | nil => cases hΓ with | refl => exact .extend hC
--       | snoc =>
--           obtain ⟨hΓ', rfl⟩ := Tele.snoc.inj hΓ
--           exact .extend (ih hΓ' hC)
--   case pi_form _ Γ' y D _ _ _ ihA ihB =>
--       apply Derives.pi_form (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C (by rw [hΓ]; rfl) hC
--       simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_form_eq _ Γ' y D _ _ _ _ _ ihA ihB =>
--       apply Derives.pi_form_eq (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C (by rw [hΓ]; rfl) hC
--       simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_intro_eq _ Γ' y _ _ D _ _ hA hB ihA ihB =>
--       apply Derives.pi_intro_eq (ihA hΓ hC)
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C (by rw [hΓ]; rfl) hC
--       simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_elim_eq _ _ ihf iha =>
--       have h := Derives.pi_elim_eq (Γ := Γ'') (ihf hΓ hC) (iha hΓ hC)
--       rw [Ty.shift_subst_comm] at h
--       exact h
--   case pi_comp n' Γ' y a' b' D E _ _ ihB iha =>
--       let k := n' - m
--       have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C (by rw [hΓ]; rfl) hC
--       simp [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] at ihB'
--       have h := Derives.pi_comp ihB' (iha hΓ hC)
--       rw [Ty.shift_subst_comm, Tm.shift_subst_comm] at h
--       exact h
--   case var _ i ih =>
--       rw [hΓ, ← Ctx.get_weaken]
--       exact .var (ih hΓ hC) _
--   case pi_intro _ Γ' y D body B hA hB ihA ihB =>
--       apply Derives.pi_intro (ihA hΓ hC)
--       have hΓ' : Γ'.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
--       have ihB' := @ihB Γ₁ (Γ₂.snoc ⟨y, D⟩) x C hΓ' hC
--       simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB'
--   case pi_elim _ _ ihf iha =>
--       have h := Derives.pi_elim (Γ := Γ'') (ihf hΓ hC) (iha hΓ hC)
--       rw [Ty.shift_subst_comm] at h
--       exact h

-- theorem Derives.weaken {n m}
--     {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
--     {𝒿 x C} :
--     (Γ₁ ⊢ C type) →
--     (Γ₁ ++ Γ₂ ⊢ 𝒿) →
--     (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ 𝒿.shiftAfter (n - m) 1) :=
--   Derives.weaken' (Γ := Γ₁ ++ Γ₂) (hΓ := rfl)

-- theorem Derives.presup {n} {Γ : Ctx 0 n} {𝒿}
--     (h𝒿 : Γ ⊢ 𝒿) :
--     (Γ ⊢) := by
--   induction h𝒿 with try constructor
--   | extend => assumption
--   | _ => assumption

-- theorem Ctx.WF.drop {n} {Γ : Ctx 0 n} {x A} :
--     (Γ.snoc ⟨x, A⟩ ⊢) →
--     (Γ ⊢)
--   | .extend hA => hA.presup

-- theorem Ctx.subst_snoc {m n x B} (a : Tm m) (Γ : Ctx (m + 1) (n + 1)) :
--     Ctx.subst a (Γ.snoc ⟨x, B⟩) =
--     (Ctx.subst a Γ).snoc ⟨x, B.substAt ⟨n - m, by omega⟩ (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ.le) ▸ a.shift (n - m))⟩ :=
--   rfl

-- private theorem addrc {n k : Nat} : n + 1 + k = n + k + 1 := Nat.add_right_comm n 1 k

-- @[simp]
-- theorem Tm.cast_shiftAfter {n₁ n₂ : Nat} (h : n₁ = n₂) (m s : Nat) (t : Tm n₁) :
--     (h ▸ t).shiftAfter m s = congrArg (· + s) h ▸ t.shiftAfter m s := by cases h; rfl
-- @[simp]
-- theorem Ty.cast_shiftAfter {n₁ n₂ : Nat} (h : n₁ = n₂) (m s : Nat) (T : Ty n₁) :
--     (h ▸ T).shiftAfter m s = congrArg (· + s) h ▸ T.shiftAfter m s := by cases h; rfl

-- mutual

-- theorem Ty.shiftAfter_succ {n : Nat} (m k : Nat) :
--     (T : Ty n) → T.shiftAfter m (k + 1) = (T.shiftAfter m k).shiftAfter m 1
--   | 𝑢 => rfl
--   | .el t => congrArg Ty.el (Tm.shiftAfter_succ m k t)
--   | .pi ⟨x, A⟩ B => by
--       simp [Ty.shiftAfter, Ty.shiftAfter_succ m k, Ty.shiftAfter_succ (m + 1) k]

-- theorem Tm.shiftAfter_succ {n : Nat} (m k : Nat) :
--     (t : Tm n) → t.shiftAfter m (k + 1) = (t.shiftAfter m k).shiftAfter m 1
--   | .var ⟨i, hi⟩ => by
--       simp only [Tm.shiftAfter, Idx.shiftAfter]
--       by_cases h : m ≤ i
--       · have h' : m ≤ i + k := by omega
--         simp [h, h', Nat.add_assoc]
--       · simp [h]
--   | .const _ => rfl
--   | .lam ⟨x, A⟩ body => by
--       simp [Tm.shiftAfter, Ty.shiftAfter_succ m k, Tm.shiftAfter_succ (m + 1) k]
--   | .app f a => by
--       simp only [Tm.shiftAfter, Tm.shiftAfter_succ m k]
--   | .pi' x a b => by
--       simp [Tm.shiftAfter, Tm.shiftAfter_succ m k, Tm.shiftAfter_succ (m + 1) k]
--   | .proj i t => congrArg (Tm.proj i) (Tm.shiftAfter_succ m k t)
--   | .letE x ty t body => by
--       simp [Tm.shiftAfter, Ty.shiftAfter_succ m k, Tm.shiftAfter_succ m k, Tm.shiftAfter_succ (m + 1) k]

-- end

-- theorem Tm.shift_succ {n : Nat} (k : Nat) (t : Tm n) : t.shift (k + 1) = (t.shift k).shift 1 :=
--   Tm.shiftAfter_succ 0 k t

-- end Qdt

-- -/
