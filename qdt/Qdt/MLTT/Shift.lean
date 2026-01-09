import Qdt.MLTT.Syntax

namespace Qdt

def Idx.shiftAfter {n} (m s : Nat) (i : Idx n) : Idx (n + s) :=
  if m ≤ i.val then
    ⟨i.val + s, by omega⟩
  else
    ⟨i.val, by omega⟩

private theorem addrc {n k} : n + 1 + k = n + k + 1 := Nat.add_right_comm n 1 k

mutual

/--
s: the shift amount
m: shift only variables with indices at least this value
-/
def Ty.shiftAfter {n} (m s : Nat) : Ty n → Ty (n + s)
  | 𝑢 => 𝑢
  | .pi ⟨x, a⟩ b => .pi ⟨x, a.shiftAfter m s⟩ (addrc ▸ b.shiftAfter (m + 1) s)
  | .el t => .el (t.shiftAfter m s)

def Tm.shiftAfter {n} (m s : Nat) : Tm n → Tm (n + s)
  | .var i => .var (i.shiftAfter m s)
  | .proj i t => .proj i (t.shiftAfter m s)
  | .const name => .const name
  | .lam ⟨x, a⟩ body => .lam ⟨x, a.shiftAfter m s⟩ (addrc ▸ body.shiftAfter (m + 1) s)
  | .app f a => .app (f.shiftAfter m s) (a.shiftAfter m s)
  | .piHat x a b => .piHat x (a.shiftAfter m s) (addrc ▸ b.shiftAfter (m + 1) s)
  | .letE name ty t body =>
      .letE name (ty.shiftAfter m s) (t.shiftAfter m s)
        (addrc ▸ body.shiftAfter (m + 1) s)

end

abbrev Ty.shift {n} : ∀ s, Ty n → Ty (n + s) := Ty.shiftAfter 0
abbrev Tm.shift {n} : ∀ s, Tm n → Tm (n + s) := Tm.shiftAfter 0

prefix:50 "↑" => Ty.shift 1
prefix:50 "↑" => Tm.shift 1

theorem Idx.shift_shift_comm_gen {n} (m k : Nat) :
    ∀ i : Idx n,
    (i.shiftAfter m 1).shiftAfter (k + m + 1) 1 = (i.shiftAfter (k + m) 1).shiftAfter m 1
  | ⟨i, hi⟩ => by
      simp only [Idx.shiftAfter]
      by_cases h₁ : m ≤ i <;>
      by_cases h₂ : k + m ≤ i <;>
      try simp [h₁, h₂]; try omega

mutual

theorem Ty.shift_shift_comm_gen {n} (m k : Nat) :
    ∀ t : Ty n,
    (t.shiftAfter m 1).shiftAfter (k + m + 1) 1 = (t.shiftAfter (k + m) 1).shiftAfter m 1
  | 𝑢 => rfl
  | .pi ⟨x, a⟩ b => by
      simp only [Ty.shiftAfter]
      have ha := Ty.shift_shift_comm_gen m k a
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Ty.shift_shift_comm_gen (m + 1) k b
      simp only [ha, hb]
  | .el e => by
      simp only [Ty.shiftAfter]
      exact congrArg Ty.el (Tm.shift_shift_comm_gen m k e)
termination_by structural t => t

theorem Tm.shift_shift_comm_gen {n} (m k : Nat) :
    ∀ t : Tm n,
    (t.shiftAfter m 1).shiftAfter (k + m + 1) 1 = (t.shiftAfter (k + m) 1).shiftAfter m 1
  | .var i => by
      simp only [Tm.shiftAfter]
      exact congrArg Tm.var (Idx.shift_shift_comm_gen m k i)
  | .const .. => rfl
  | .lam ⟨x, a⟩ body => by
      simp only [Tm.shiftAfter]
      have ha := Ty.shift_shift_comm_gen m k a
      have hb :
          (body.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (body.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shift_shift_comm_gen (m + 1) k body
      simp only [ha, hb]
  | .app f a => by
      simp only [Tm.shiftAfter]
      have hf := Tm.shift_shift_comm_gen m k f
      have ha := Tm.shift_shift_comm_gen m k a
      simp only [hf, ha]
  | .piHat x a b => by
      simp only [Tm.shiftAfter]
      have ha := Tm.shift_shift_comm_gen m k a
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shift_shift_comm_gen (m + 1) k b
      simp only [ha, hb]
  | .proj i t => by
      simp only [Tm.shiftAfter]
      exact congrArg (Tm.proj i) (Tm.shift_shift_comm_gen m k t)
  | .letE x ty t body => by
      simp only [Tm.shiftAfter]
      have hty := Ty.shift_shift_comm_gen m k ty
      have ht := Tm.shift_shift_comm_gen m k t
      have hbody :
          (body.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (body.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shift_shift_comm_gen (m + 1) k body
      simp only [hty, ht, hbody]
termination_by structural t => t

end

theorem Ty.shift_shift_comm {n} :
    ∀ k (t : Ty n),
    (t.shift 1).shiftAfter (k + 1) 1 = (t.shiftAfter k 1).shift 1 :=
  Ty.shift_shift_comm_gen 0

theorem Tm.shift_shift_comm {n} :
    ∀ k (t : Tm n),
    (t.shift 1).shiftAfter (k + 1) 1 = (t.shiftAfter k 1).shift 1 :=
  Tm.shift_shift_comm_gen 0

end Qdt
