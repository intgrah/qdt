import Qdt.MLTT.Substitution
import Qdt.Tele

namespace Qdt

abbrev Ctx := Tele Param

def Ctx.get {n} : Idx n → Ctx 0 n → Ty n
  | i, .nil => nomatch i
  | ⟨0, _⟩, .snoc _ ⟨_, A⟩ => ↑A
  | ⟨i + 1, hi⟩, .snoc Γ _ => ↑Ctx.get ⟨i, Nat.lt_of_succ_lt_succ hi⟩ Γ


def Ctx.shift {a b} (s : Nat) : Ctx a b → Ctx (a + s) (b + s) :=
  Tele.dmap s (fun {i} ⟨x, t⟩ => ⟨x, t.shiftAfter (i - a) s⟩)

@[simp]
theorem Ctx.shift_nil {n s} : Ctx.shift s (Tele.nil : Ctx n n) = Tele.nil := rfl

theorem Ctx.shift_snoc {m n s x A}
    (Γ : Ctx m n) :
    (Ctx.shift s (Γ.snoc ⟨x, A⟩) = Nat.succ_add n s ▸ (Ctx.shift s Γ).snoc ⟨x, A.shiftAfter (n - m) s⟩) := by
  unfold Ctx.shift
  rw [Tele.dmap_snoc]

def Ctx.subst {m} (a : Tm m) : {n : Nat} → Ctx (m + 1) (n + 1) → Ctx m n
  | _, .nil => .nil
  | n + 1, .snoc Γ ⟨x, B⟩ =>
      have := Γ.le
      have heq : m + (n - m) = n := by omega
      .snoc (Ctx.subst a Γ) ⟨x, B.substAt ⟨n - m, by omega⟩ (heq ▸ a.shift (n - m))⟩

instance {m n} : GetElem (Ctx (m + 1) (n + 1)) (Tm m) (Ctx m n) fun _ _ => True where
  getElem Γ s _ := Ctx.subst s Γ

end Qdt
