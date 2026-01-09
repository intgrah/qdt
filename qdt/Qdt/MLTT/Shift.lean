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

theorem Ty.shiftAfter_shiftAfter {n} (m k : Nat) :
    ∀ t : Ty n,
    (t.shiftAfter m 1).shiftAfter (k + m + 1) 1 = (t.shiftAfter (k + m) 1).shiftAfter m 1
  | 𝑢 => rfl
  | .pi ⟨_, _⟩ b => by
      simp only [Ty.shiftAfter]
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Ty.shiftAfter_shiftAfter (m + 1) k b
      simp only [Ty.shiftAfter_shiftAfter, hb]
  | .el e => congrArg Ty.el (Tm.shiftAfter_shiftAfter m k e)

theorem Tm.shiftAfter_shiftAfter {n} (m k : Nat) :
    ∀ t : Tm n,
    (t.shiftAfter m 1).shiftAfter (k + m + 1) 1 = (t.shiftAfter (k + m) 1).shiftAfter m 1
  | .var i => congrArg Tm.var (Idx.shift_shift_comm_gen m k i)
  | .const .. => rfl
  | .lam ⟨_, _⟩ b => by
      simp only [Tm.shiftAfter]
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shiftAfter_shiftAfter (m + 1) k b
      simp only [Ty.shiftAfter_shiftAfter, hb]
  | .app .. => by simp only [Tm.shiftAfter, Tm.shiftAfter_shiftAfter]
  | .piHat _ _ b => by
      simp only [Tm.shiftAfter]
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shiftAfter_shiftAfter (m + 1) k b
      simp only [Tm.shiftAfter_shiftAfter, hb]
  | .proj i t => congrArg (Tm.proj i) (Tm.shiftAfter_shiftAfter m k t)
  | .letE _ _ _ b => by
      simp only [Tm.shiftAfter]
      have hb :
          (b.shiftAfter (m + 1) 1).shiftAfter (k + m + 2) 1 =
          (b.shiftAfter (k + m + 1) 1).shiftAfter (m + 1) 1 :=
        Tm.shiftAfter_shiftAfter (m + 1) k b
      simp only [Ty.shiftAfter_shiftAfter, Tm.shiftAfter_shiftAfter, hb]

end

theorem Ty.shift_shiftAfter {n} :
    ∀ k (t : Ty n),
    (t.shift 1).shiftAfter (k + 1) 1 = (t.shiftAfter k 1).shift 1 :=
  Ty.shiftAfter_shiftAfter 0

theorem Tm.shift_shiftAfter {n} :
    ∀ k (t : Tm n),
    (t.shift 1).shiftAfter (k + 1) 1 = (t.shiftAfter k 1).shift 1 :=
  Tm.shiftAfter_shiftAfter 0

@[simp]
theorem Idx.shiftAfter_zero {n} (c : Nat) (i : Idx n) : Idx.shiftAfter c 0 i = i := by
  simp only [Idx.shiftAfter, Nat.add_zero]
  split <;> rfl

mutual

@[simp]
theorem Ty.shiftAfter_zero {n} (c : Nat) : ∀ A : Ty n, Ty.shiftAfter c 0 A = A
  | .u => rfl
  | .pi ⟨_, _⟩ _ => by simp only [Ty.shiftAfter, Ty.shiftAfter_zero]
  | .el .. => by simp [Ty.shiftAfter, Tm.shiftAfter_zero]

@[simp]
theorem Tm.shiftAfter_zero {n} (c : Nat) : ∀ a : Tm n, Tm.shiftAfter c 0 a = a
  | .var .. => by simp [Tm.shiftAfter]
  | .const .. => rfl
  | .lam ⟨_, _⟩ _ => by simp only [Tm.shiftAfter, Ty.shiftAfter_zero, Tm.shiftAfter_zero]
  | .app .. => by simp [Tm.shiftAfter, Tm.shiftAfter_zero]
  | .proj .. => by simp [Tm.shiftAfter, Tm.shiftAfter_zero]
  | .piHat .. => by simp only [Tm.shiftAfter, Tm.shiftAfter_zero]
  | .letE .. => by simp only [Tm.shiftAfter, Ty.shiftAfter_zero, Tm.shiftAfter_zero]

end

@[simp]
theorem Ty.shift_zero {n} : ∀ A : Ty n, A.shift 0 = A := Ty.shiftAfter_zero 0

@[simp]
theorem Tm.shift_zero {n} : ∀ a : Tm n, a.shift 0 = a := Tm.shiftAfter_zero 0

end Qdt
