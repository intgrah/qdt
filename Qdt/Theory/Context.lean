module

public import Qdt.Theory.Substitution.Basic

@[expose] public section

namespace Qdt

namespace Ctx

def get {n} : Idx n → Ctx 0 n → Ty n
  | i, .nil => nomatch i
  | ⟨0, _⟩, .snoc _ ⟨_, A⟩ => ↑A
  | ⟨i + 1, hi⟩, .snoc Γ _ => ↑get ⟨i, Nat.lt_of_succ_lt_succ hi⟩ Γ

def weaken {a b} : Ctx a b → Ctx (a + 1) (b + 1) :=
  Tele.dmap 1 (fun ⟨x, t⟩ => ⟨x, t.subst Subst.shift⟩)

@[simp]
theorem weaken_nil {n} : weaken (Tele.nil : Ctx n n) = Tele.nil := rfl

theorem weaken_snoc {m n x A}
    (Γ : Ctx m n) :
    weaken (Γ.snoc ⟨x, A⟩) = Nat.succ_add n 1 ▸ (weaken Γ).snoc ⟨x, A.weaken⟩ := by
  unfold weaken
  rw [Tele.dmap_snoc]

def subst {m} (a : Tm m) : {n : Nat} → Ctx (m + 1) (n + 1) → Ctx m n
  | _, .nil => .nil
  | n + 1, .snoc Γ ⟨x, B⟩ =>
      have := Γ.le
      have heq : m + (n - m) = n := by omega
      .snoc (subst a Γ) ⟨x, B.subst (Subst.beta (heq ▸ a.subst (Subst.shiftN (n - m))))⟩

instance {m n} : GetElem (Ctx (m + 1) (n + 1)) (Tm m) (Ctx m n) fun _ _ => True where
  getElem Γ s _ := subst s Γ

@[simp]
theorem subst_nil {n} {a : Tm n} : subst a Tele.nil = Tele.nil := by
  unfold subst
  rfl

@[simp]
theorem get_snoc_zero {n} {x : Lean.Name} {A : Ty n} {Γ : Ctx 0 n}
    (h : (0 : Nat) < n + 1 := by omega) :
    Ctx.get ⟨0, h⟩ (Γ.snoc ⟨x, A⟩) = A.weaken := rfl

@[simp]
theorem get_snoc_succ {n} {x : Lean.Name} {A : Ty n} {Γ : Ctx 0 n}
    (i : Idx n) :
    Ctx.get ⟨i.val + 1, by have := i.isLt; omega⟩ (Γ.snoc ⟨x, A⟩)
      = (Ctx.get i Γ).weaken := rfl

end Ctx

end Qdt
