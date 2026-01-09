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
    split
    · rfl
    · omega
  | @snoc n' Γ₂ p ih =>
    have ⟨y, B⟩ := p
    have hle : m ≤ n' := Γ₂.le
    have ⟨i_val, hi⟩ := i
    match i_val with
    | 0 =>
      rw [Nat.succ_sub hle]
      exact (Ty.shift_shift_comm (n' - m) B).symm
    | j + 1 =>
      have ih_spec := ih ⟨j, by omega⟩
      simp only [Idx.shiftAfter] at ih_spec
      show Ctx.get (if _ then _ else _) _ = (Ctx.get ⟨j + 1, _⟩ _).shiftAfter (n' + 1 - m) 1
      simp [Ctx.get]
      split
      · rw [Nat.succ_sub hle, Ty.shift_shift_comm]
        have h2 : n' - m ≤ j := by omega
        simp only [h2] at ih_spec
        exact congrArg (Ty.shift 1) ih_spec
      · rw [Nat.succ_sub hle, Ty.shift_shift_comm]
        have h2 : ¬ n' - m ≤ j := by omega
        simp only [h2, ↓reduceIte] at ih_spec
        exact congrArg (Ty.shift 1) ih_spec

mutual

theorem Ty.WF.weaken {n m}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {A} {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : id <| Γ₁ ⊢ C type) : -- Use `id` to prevent field syntax from consuming this param
    (Γ ⊢ A type) →
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ A.shiftAfter (n - m) 1 type)
  | .u_form hΓwf => .u_form (hΓwf.weaken hΓ hC)
  | .el_form he => .el_form (he.weaken hΓ hC)
  | .pi_form (x := y) (A := D) hA hB => .pi_form (hA.weaken hΓ hC) <| by
      have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB := hB.weaken (x := x) hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB

/-- HoTT book A.2.2, wkg₁ -/
theorem Tm.HasType.weaken {n m}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {a A} {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : Γ₁ ⊢ C type) :
    (Γ ⊢ a : A) →
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ a.shiftAfter (n - m) 1 : A.shiftAfter (n - m) 1)
  | .var hΓwf i => hΓ ▸ Ctx.get_weaken i ▸ .var (hΓwf.weaken hΓ hC) (i.shiftAfter (n - m) 1)
  | .const hΓwf => .const (hΓwf.weaken hΓ hC)
  | .pi_intro (x := y) (A := D) hA hB => .pi_intro (hA.weaken hΓ hC) <| by
      have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB := hB.weaken (x := x) hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB
  | .pi_elim (x := y) (A := D) (B := E) (a := a') hf ha => by
      let Γ' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
      let k := n - m
      have ihf : Γ' ⊢ _ : .pi ⟨y, D.shiftAfter k 1⟩ (E.shiftAfter (k + 1) 1) := hf.weaken hΓ hC
      have iha : Γ' ⊢ _ : D.shiftAfter k 1 := ha.weaken hΓ hC
      have h := Tm.HasType.pi_elim ihf iha
      have eq : (E.shiftAfter (k + 1) 1)[a'.shiftAfter k 1] = E[a'].shiftAfter k 1 := E.shift_subst_comm k a'
      simp only [GetElem.getElem] at eq h ⊢
      rw [eq] at h
      exact h
  | .conv he hA => .conv (he.weaken hΓ hC) (hA.weaken hΓ hC)

/-- Because we have a type judgement -/
theorem Ty.Eq.weaken {n m}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {A B} {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : Γ₁ ⊢ C type) :
    (Γ ⊢ A ≡ B type) →
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ A.shiftAfter (n - m) 1 ≡ B.shiftAfter (n - m) 1 type)
  | .refl hA => .refl (hA.weaken hΓ hC)
  | .symm hAB => .symm (hAB.weaken hΓ hC)
  | .trans hAB hBC => .trans (hAB.weaken hΓ hC) (hBC.weaken hΓ hC)
  | .pi_form_eq (x := y) (A₁ := D) hA hB => .pi_form_eq (hA.weaken hΓ hC) <| by
      have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB := hB.weaken (x := x) hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB
  | .el_form_eq he => .el_form_eq (he.weaken hΓ hC)

/-- HoTT book A.2.2, wkg₂ -/
theorem Tm.Eq.weaken {n m}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {a b A} {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : Γ₁ ⊢ C type) :
    (Γ ⊢ a ≡ b : A) →
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢ a.shiftAfter (n - m) 1 ≡ b.shiftAfter (n - m) 1 : A.shiftAfter (n - m) 1)
  | .refl he => .refl (he.weaken hΓ hC)
  | .symm heq => .symm (heq.weaken hΓ hC)
  | .trans hab hbc => .trans (hab.weaken hΓ hC) (hbc.weaken hΓ hC)
  | .pi_intro_eq (x := y) (A₁ := D) hA hB => .pi_intro_eq (hA.weaken hΓ hC) <| by
      have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB := hB.weaken (x := x) hΓ' hC
      simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using ihB
  | .pi_elim_eq (x := y) (A := D) (B := E) (a₁ := a₁') hf ha => by
      let Γ' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
      let k := n - m
      have ihf : Γ' ⊢ _ ≡ _ : .pi ⟨y, D.shiftAfter k 1⟩ (E.shiftAfter (k + 1) 1) := hf.weaken hΓ hC
      have iha : Γ' ⊢ _ ≡ _ : D.shiftAfter k 1 := ha.weaken hΓ hC
      have h := Tm.Eq.pi_elim_eq ihf iha
      have eq : (E.shiftAfter (k + 1) 1)[a₁'.shiftAfter k 1] = E[a₁'].shiftAfter k 1 := Ty.shift_subst_comm k a₁' E
      simp only [GetElem.getElem] at eq h ⊢
      rw [eq] at h
      exact h
  | .pi_comp (x := y) (A := D) (a := a') (B := E) (b := b') hB ha => by
      let Γ' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
      let k := n - m
      have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      have ihB : Γ'.snoc ⟨y, D.shiftAfter k 1⟩ ⊢ b'.shiftAfter (k + 1) 1 : E.shiftAfter (k + 1) 1 := by
        simpa [Ctx.shift_snoc, Nat.succ_sub Γ₂.le] using hB.weaken (x := x) hΓ' hC
      have iha : Γ' ⊢ a'.shiftAfter k 1 : D.shiftAfter k 1 := ha.weaken hΓ hC
      have h := Tm.Eq.pi_comp ihB iha
      have ty_eq : (E.shiftAfter (k + 1) 1)[a'.shiftAfter k 1] = E[a'].shiftAfter k 1 := Ty.shift_subst_comm k a' E
      have tm_eq : (b'.shiftAfter (k + 1) 1)[a'.shiftAfter k 1] = b'[a'].shiftAfter k 1 := Tm.shift_subst_comm k a' b'
      simp only [GetElem.getElem] at ty_eq tm_eq h ⊢
      rw [ty_eq, tm_eq] at h
      exact h
  | .pi_uniq (x := y) (A := D) (B := E) (f := f') hf => by
      let Γ' := Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1
      let k := n - m
      have ihf : Γ' ⊢ f'.shiftAfter k 1 : .pi ⟨y, D.shiftAfter k 1⟩ (E.shiftAfter (k + 1) 1) :=
        hf.weaken hΓ hC
      have h := Tm.Eq.pi_uniq ihf
      have idx_shift : Idx.shiftAfter (k + 1) 1 ⟨0, Nat.zero_lt_succ n⟩ =
                       ⟨0, Nat.zero_lt_succ (n + 1)⟩ := by
        unfold Idx.shiftAfter
        have : ¬ k + 1 ≤ 0 := by omega
        simp [this]
      have eq_rhs : (Tm.lam ⟨y, D⟩ ((Tm.shift 1 f').app (.var ⟨0, Nat.zero_lt_succ n⟩))).shiftAfter k 1 =
                    Tm.lam ⟨y, D.shiftAfter k 1⟩ ((Tm.shift 1 (f'.shiftAfter k 1)).app (.var ⟨0, Nat.zero_lt_succ (n+1)⟩)) := by
        simp only [Tm.shiftAfter]
        rw [Tm.shift_shift_comm k f', idx_shift]
      rw [eq_rhs]
      exact h
  | .conv heq hAB => .conv (heq.weaken hΓ hC) (hAB.weaken hΓ hC)

theorem Ctx.WF.weaken {m n}
    {Γ : Ctx 0 n} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx m n}
    {x C}
    (hΓ : Γ = Γ₁ ++ Γ₂)
    (hC : Γ₁ ⊢ C type)
    (hΓwf : Γ ⊢) :
    (Γ₁.snoc ⟨x, C⟩ ++ Γ₂.shift 1 ⊢) :=
  match Γ₂, hΓwf with
  | .nil, _ => .extend hC
  | .snoc _ _, .extend hA =>
    have ⟨hΓ', hp⟩ := Tele.snoc.inj hΓ
    hp ▸ .extend (hA.weaken hΓ' hC)

end

mutual

theorem Ty.WF.presup {n}
    {Γ : Ctx 0 n}
    {A} :
    (Γ ⊢ A type) →
    (Γ ⊢)
  | .u_form hΓ => hΓ
  | .el_form he => Tm.HasType.presup he
  | .pi_form hA _ => Ty.WF.presup hA

theorem Tm.HasType.presup {n}
    {Γ : Ctx 0 n}
    {a A} :
    (Γ ⊢ a : A) →
    (Γ ⊢)
  | .var hΓ _ => hΓ
  | .const hΓ => hΓ
  | .pi_intro hA _ => Ty.WF.presup hA
  | .pi_elim hf _ => Tm.HasType.presup hf
  | .conv he _ => Tm.HasType.presup he

theorem Tm.Eq.presup {n}
    {Γ : Ctx 0 n}
    {a b A} :
    (Γ ⊢ a ≡ b : A) →
    (Γ ⊢)
  | .refl ha => Tm.HasType.presup ha
  | .symm heq => Tm.Eq.presup heq
  | .trans heq _ => Tm.Eq.presup heq
  | .pi_intro_eq hA _ => Ty.Eq.presup hA
  | .pi_elim_eq heq _ => Tm.Eq.presup heq
  | .pi_comp _ ha => Tm.HasType.presup ha
  | .pi_uniq hf => Tm.HasType.presup hf
  | .conv heq _ => Tm.Eq.presup heq

theorem Ty.Eq.presup {n}
    {Γ : Ctx 0 n}
    {A B} :
    (Γ ⊢ A ≡ B type) →
    (Γ ⊢)
  | .refl hA => Ty.WF.presup hA
  | .symm heq => Ty.Eq.presup heq
  | .trans heq _ => Ty.Eq.presup heq
  | .pi_form_eq hA _ => Ty.Eq.presup hA
  | .el_form_eq heq => Tm.Eq.presup heq

end

theorem Ctx.WF.presup {n}
    {Γ : Ctx 0 n} :
    (Γ ⊢) →
    (Γ ⊢) := id

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

private def Ctx.size : {m n : Nat} → Ctx m n → Nat
  | _, _, .nil => 0
  | _, _, .snoc Γ _ => 1 + Ctx.size Γ

mutual

theorem Ty.WF.subst {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {B} {x a A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : id <| Γ₁ ⊢ a : A) :
    let c : Idx (n + 1) := ⟨n - m, by omega⟩
    let s : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    (Γ ⊢ B type) →
    (Γ₁ ++ Γ₂[a] ⊢ B.substAt c s type)
  | .u_form hΓwf => by simp only [Ty.substAt]; exact .u_form (Ctx.WF.subst hΓ ha hΓwf)
  | .el_form (t := t) he => by
      sorry
      -- simp only [Ty.substAt]
      -- have h : Γ₁ ++ Γ₂[a] ⊢ Tm.substAt ⟨n - m, by omega⟩ (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)) t : 𝑢 := by
      --   have ht := Tm.HasType.subst hΓ ha he
      --   simp only [Ty.substAt] at ht
      --   exact ht
      -- exact .el_form h
  | .pi_form (x := y) (A := D) hA hB => by
      sorry
      -- simp only [Ty.substAt]
      -- refine .pi_form (hA.subst hΓ ha) ?_
      -- have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      -- have ihB := hB.subst (x := x) hΓ' ha
      -- have hle : m ≤ n := Nat.le_of_succ_le_succ Γ₂.le
      -- simp only [GetElem.getElem, Ctx.subst_snoc, Tele.append_snoc, Nat.succ_sub hle] at ihB ⊢
      -- -- ihB : ... ⊢ substAt ⟨(n - m).succ, _⟩ (h₂ ▸ a.shift (n + 1 - m)) B type
      -- -- goal: ... ⊢ substAt ⟨n - m, _⟩.succ ((h₁ ▸ a.shift (n - m)).shift 1) B type
      -- -- The indices ⟨(n - m).succ, _⟩ and ⟨n - m, _⟩.succ are definitionally equal
      -- -- Need to show the terms are equal
      -- have term_eq : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) a : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) a : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   -- Both sides are casts to Tm (n + 1)
      --   have h1 : (a.shiftAfter 0 (n - m)).shiftAfter 0 1 = a.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) a).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   -- Show the underlying values are HEq
      --   have underlying_heq : HEq ((a.shiftAfter 0 (n - m)).shiftAfter 0 1) (a.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (a.shiftAfter 0 (n - m + 1)) (a.shiftAfter 0 k)) HEq.rfl
      --   -- Casted values are equal when underlying values are HEq and casts target the same type
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- rw [term_eq]
      -- exact ihB

/-- HoTT book A.2.2, subst₁ -/
theorem Tm.HasType.subst {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {b B} {x a A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : Γ₁ ⊢ a : A) :
    let c : Idx (n + 1) := ⟨n - m, by omega⟩
    let s : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    (Γ ⊢ b : B) →
    (Γ₁ ++ Γ₂[a] ⊢ Tm.substAt c s b : Ty.substAt c s B) := sorry

/-- Because we have a type judgement -/
theorem Ty.Eq.subst {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {B C} {x a A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : Γ₁ ⊢ a : A) :
    let c : Idx (n + 1) := ⟨n - m, by omega⟩
    let s : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    (Γ ⊢ B ≡ C type) →
    (Γ₁ ++ Γ₂[a] ⊢ B.substAt c s ≡ C.substAt c s type) := sorry

/-- Because we have a type judgement -/
theorem Ty.Eq.subst' {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {C} {x a b A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (hab : Γ₁ ⊢ a ≡ b : A) :
    let c : Idx (n + 1) := ⟨n - m, by omega⟩
    let sa : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    let sb : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ b.shift (n - m)
    (Γ ⊢ C type) →
    (Γ₁ ++ Ctx.subst a Γ₂ ⊢ C.substAt c sa ≡ C.substAt c sb type)
  | .u_form hΓwf => sorry -- by simp only [Ty.substAt]; exact .refl (Ty.WF.u_form (Ctx.WF.subst hΓ hab.presup₁ hΓwf))
  | .el_form he => by
      sorry
      -- simp only [Ty.substAt]
      -- have h := Tm.Eq.subst' hΓ hab he
      -- simp only [Ty.substAt] at h
      -- exact .el_form_eq h
  | .pi_form (x := y) (A := D) hA hB => sorry
      -- simp only [Ty.substAt]
      -- refine .pi_form_eq (Ty.Eq.subst' hΓ hab hA) ?_
      -- have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      -- have ihB := Ty.Eq.subst' hΓ' hab hB
      -- have hle : m ≤ n := Nat.le_of_succ_le_succ Γ₂.le
      -- simp only [Ctx.subst_snoc, Tele.append_snoc, Nat.succ_sub hle] at ihB ⊢
      -- -- For both a and b, we need to show the shifted terms are equal
      -- have term_eq_a : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) a : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) a : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   have h1 : (a.shiftAfter 0 (n - m)).shiftAfter 0 1 = a.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) a).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   have underlying_heq : HEq ((a.shiftAfter 0 (n - m)).shiftAfter 0 1) (a.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (a.shiftAfter 0 (n - m + 1)) (a.shiftAfter 0 k)) HEq.rfl
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- have term_eq_b : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) b : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) b : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   have h1 : (b.shiftAfter 0 (n - m)).shiftAfter 0 1 = b.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) b).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   have underlying_heq : HEq ((b.shiftAfter 0 (n - m)).shiftAfter 0 1) (b.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (b.shiftAfter 0 (n - m + 1)) (b.shiftAfter 0 k)) HEq.rfl
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- rw [term_eq_a, term_eq_b]
      -- exact ihB

/-- HoTT book A.2.2, subst₂ -/
theorem Tm.Eq.subst {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {b c B} {x a A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : Γ₁ ⊢ a : A) :
    let k : Idx (n + 1) := ⟨n - m, by omega⟩
    let s : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    (Γ ⊢ b ≡ c : B) →
    (Γ₁ ++ Γ₂[a] ⊢ Tm.substAt k s b ≡ Tm.substAt k s c : Ty.substAt k s B)
  | .refl he => sorry -- .refl (Tm.HasType.subst hΓ ha he)
  | .symm heq => sorry -- .symm (Tm.Eq.subst hΓ ha heq)
  | .trans hab hbc => sorry -- .trans (Tm.Eq.subst hΓ ha hab) (Tm.Eq.subst hΓ ha hbc)
  | .pi_intro_eq (x := y) (A₁ := D) hAeq hbeq => by
      sorry
      -- simp only [Tm.substAt, Ty.substAt]
      -- refine .pi_intro_eq (Ty.Eq.subst hΓ ha hAeq) ?_
      -- have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      -- have ihbeq := Tm.Eq.subst hΓ' ha hbeq
      -- have hle : m ≤ n := Nat.le_of_succ_le_succ Γ₂.le
      -- simp only [GetElem.getElem, Ctx.subst_snoc, Tele.append_snoc, Nat.succ_sub hle] at ihbeq ⊢
      -- have term_eq : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) a : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) a : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   have h1 : (a.shiftAfter 0 (n - m)).shiftAfter 0 1 = a.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) a).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   have underlying_heq : HEq ((a.shiftAfter 0 (n - m)).shiftAfter 0 1) (a.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (a.shiftAfter 0 (n - m + 1)) (a.shiftAfter 0 k)) HEq.rfl
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- rw [term_eq]
      -- exact ihbeq
  | .pi_elim_eq hf ha' => sorry
  | .pi_comp hb ha' => sorry
  | .pi_uniq hf => sorry
  | .conv heq hAB => sorry -- .conv (Tm.Eq.subst hΓ ha heq) (Ty.Eq.subst hΓ ha hAB)

/-- HoTT book A.2.2, subst₃ -/
theorem Tm.Eq.subst' {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {c C} {x a b A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (hab : Γ₁ ⊢ a ≡ b : A) :
    let k : Idx (n + 1) := ⟨n - m, by omega⟩
    let sa : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ a.shift (n - m)
    let sb : Tm n := Nat.add_sub_cancel' (Nat.le_of_succ_le_succ Γ₂.le) ▸ b.shift (n - m)
    (Γ ⊢ c : C) →
    (Γ₁ ++ Γ₂[a] ⊢ Tm.substAt k sa c ≡ Tm.substAt k sb c : Ty.substAt k sa C)
  | .var hΓwf i => sorry
  | .const hΓwf => sorry -- by simp only [Tm.substAt, Ty.substAt]; exact .refl (.const (Ctx.WF.subst hΓ hab.presup₁ hΓwf))
  | .pi_intro (x := y) (A := D) hA hbody => by
      sorry
      -- simp only [Tm.substAt, Ty.substAt]
      -- refine .pi_intro_eq (Ty.Eq.subst' hΓ hab hA) ?_
      -- have hΓ' : Γ.snoc ⟨y, D⟩ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂.snoc ⟨y, D⟩ := by rw [hΓ]; rfl
      -- have ihB := Tm.Eq.subst' hΓ' hab hbody
      -- have hle : m ≤ n := Nat.le_of_succ_le_succ Γ₂.le
      -- simp only [GetElem.getElem, Ctx.subst_snoc, Tele.append_snoc, Nat.succ_sub hle] at ihB ⊢
      -- have term_eq_a : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) a : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) a : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   have h1 : (a.shiftAfter 0 (n - m)).shiftAfter 0 1 = a.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) a).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   have underlying_heq : HEq ((a.shiftAfter 0 (n - m)).shiftAfter 0 1) (a.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (a.shiftAfter 0 (n - m + 1)) (a.shiftAfter 0 k)) HEq.rfl
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- have term_eq_b : (Nat.add_sub_cancel' hle ▸ Tm.shift (n - m) b : Tm n).shift 1 =
      --     (Nat.add_sub_cancel' (Nat.le_of_succ_le_succ (Γ₂.snoc ⟨y, D⟩).le) ▸ Tm.shift (n + 1 - m) b : Tm (n + 1)) := by
      --   simp only [Tm.shift]
      --   rw [Tm.cast_shiftAfter (Nat.add_sub_cancel' hle) 0 1]
      --   have h1 : (b.shiftAfter 0 (n - m)).shiftAfter 0 1 = b.shiftAfter 0 (n - m + 1) :=
      --     (Tm.shiftAfter_succ 0 (n - m) b).symm
      --   have h2 : n + 1 - m = n - m + 1 := Nat.succ_sub hle
      --   have underlying_heq : HEq ((b.shiftAfter 0 (n - m)).shiftAfter 0 1) (b.shiftAfter 0 (n + 1 - m)) := by
      --     rw [h1]
      --     have h2' : n - m + 1 = n + 1 - m := h2.symm
      --     exact h2'.rec (motive := fun k _ => HEq (b.shiftAfter 0 (n - m + 1)) (b.shiftAfter 0 k)) HEq.rfl
      --   apply eq_of_heq
      --   refine HEq.trans (eqRec_heq _ _) ?_
      --   refine HEq.trans underlying_heq ?_
      --   exact (eqRec_heq _ _).symm
      -- rw [term_eq_a, term_eq_b]
      -- exact ihB
  | .pi_elim (x := y) (A := D) (B := E) (a := a') hf ha' => sorry
  | .conv he hAB => sorry -- .conv (Tm.Eq.subst' hΓ hab he) (Ty.Eq.subst hΓ hab.presup₁ hAB)

theorem Ctx.WF.subst {m n}
    {Γ : Ctx 0 (n + 1)} {Γ₁ : Ctx 0 m} {Γ₂ : Ctx (m + 1) (n + 1)}
    {x a A}
    (hΓ : Γ = Γ₁.snoc ⟨x, A⟩ ++ Γ₂)
    (ha : Γ₁ ⊢ a : A)
    (hΓwf : Γ ⊢) :
    (Γ₁ ++ Γ₂[a] ⊢) := by
  rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ Γ₂.le) with hmn | hm_lt_n
  · -- m = n: Γ₂ = nil
    subst hmn
    cases Γ₂ with
    | nil =>
        simp only [GetElem.getElem, Ctx.subst]
        exact ha.presup
    | snoc Γ₂' _ => exact absurd Γ₂'.le (by omega)
  · -- m < n: Γ₂ = Γ₂'.snoc ⟨y, B⟩
    cases Γ₂ with
    | nil => omega
    | @snoc n' Γ₂' p =>
        simp only [GetElem.getElem]
        obtain ⟨y, B⟩ := p
        rw [hΓ, Tele.append_snoc] at hΓwf
        cases hΓwf with
        | extend hB =>
            sorry

end

end Qdt
