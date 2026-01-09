import Qdt.MLTT.Shift

namespace Qdt

mutual

def Ty.substAt {n} (c : Idx (n + 1)) (s : Tm n) : Ty (n + 1) → Ty n
  | 𝑢 => 𝑢
  | .pi ⟨x, a⟩ b => .pi ⟨x, Ty.substAt c s a⟩ (Ty.substAt c.succ (↑s) b)
  | .el t => .el (Tm.substAt c s t)

def Tm.substAt {n} (c : Idx (n + 1)) (s : Tm n) : Tm (n + 1) → Tm n
  | .var i =>
      if hlt : i.val < c.val then
        .var ⟨i.val, by omega⟩
      else if heq : i.val = c.val then
        s
      else
        .var ⟨i.val - 1, by omega⟩
  | .const name => .const name
  | .lam ⟨x, a⟩ body => .lam ⟨x, Ty.substAt c s a⟩ (Tm.substAt c.succ (↑s) body)
  | .app f a => .app (Tm.substAt c s f) (Tm.substAt c s a)
  | .piHat x a b => .piHat x (Tm.substAt c s a) (Tm.substAt c.succ (↑s) b)
  | .proj i t => .proj i (Tm.substAt c s t)
  | .letE x ty t body => .letE x (Ty.substAt c s ty) (Tm.substAt c s t) (Tm.substAt c.succ (↑s) body)

end

abbrev Ty.subst {n} : Tm n → Ty (n + 1) → Ty n := Ty.substAt 0
abbrev Tm.subst {n} : Tm n → Tm (n + 1) → Tm n := Tm.substAt 0

instance {n} : GetElem (Tm (n + 1)) (Tm n) (Tm n) fun _ _ => True where
  getElem t i _ := Tm.subst i t

instance {n} : GetElem (Ty (n + 1)) (Tm n) (Ty n) fun _ _ => True where
  getElem t i _ := Ty.subst i t

private theorem Idx.shift_substAt_comm {n}
    (a : Tm n)
    (c : Idx (n + 1))
    (k : Nat) :
    (i : Idx (n + 1)) →
    Tm.substAt c.castSucc (a.shiftAfter (k + c.val) 1) (Tm.var (Idx.shiftAfter (k + c.val + 1) 1 i)) =
    (Tm.substAt c a (Tm.var i)).shiftAfter (k + c.val) 1
  | ⟨j, hj⟩ => by
      unfold Tm.substAt Idx.shiftAfter Fin.castSucc
      by_cases hjc : j < c.val
      · have h1 : ¬ k + c.val + 1 ≤ j := by omega
        have h2 : ¬ k + c.val ≤ j := by omega
        simp [h1, hjc, h2, Tm.shiftAfter, Idx.shiftAfter]
      by_cases hjc' : j = c.val
      · have : ¬ k + c.val + 1 ≤ c.val := by omega
        simp [hjc', this]
      · have hgt : c.val < j := by omega
        have hcc : (Fin.castAdd 1 c).val = c.val := rfl
        by_cases hk : k + c.val + 1 ≤ j
        all_goals simp only [hk, hcc, hjc, hjc', ↓reduceIte, dite_false]
        case pos =>
          have h₁ : ¬ j + 1 < c.val := by omega
          have h₂ : j + 1 ≠ c.val := by omega
          have h₃ : k + c.val ≤ j - 1 := by omega
          have hj₁ : j + 1 - 1 = j := by omega
          have hj₂ : j - 1 + 1 = j := by omega
          simp [h₁, h₂, h₃, hj₁, hj₂, Tm.shiftAfter, Idx.shiftAfter]
        case neg =>
          have h : ¬ k + c.val ≤ j - 1 := by omega
          simp [h, Tm.shiftAfter, Idx.shiftAfter]

private theorem ha {n} (a : Tm n) (k : Nat) (c : Idx (n + 1)) :
    (a.shift 1).shiftAfter (k + c.val + 1) 1 = (a.shiftAfter (k + c.val) 1).shift 1 :=
  Tm.shift_shift_comm_gen 0 (k + c.val) a

private theorem add_succ_val {n} (c : Idx (n + 1)) (k : Nat) :
    k + c.val + 1 = k + c.succ.val := rfl

mutual

theorem Ty.shift_substAt_comm {n}
    (c : Idx (n + 1))
    (k : Nat)
    (a : Tm n) :
    (B : Ty (n + 1)) →
    Ty.substAt c.castSucc (a.shiftAfter (k + c.val) 1) (B.shiftAfter (k + c.val + 1) 1) =
    (Ty.substAt c a B).shiftAfter (k + c.val) 1
  | 𝑢 => by simp only [Ty.shiftAfter, Ty.substAt]
  | .pi ⟨x, A⟩ B => by
      simp only [Ty.shiftAfter, Ty.substAt]
      congr 2
      · exact Ty.shift_substAt_comm c k a A
      · rw [Fin.succ_castSucc, ← ha, add_succ_val]
        exact Ty.shift_substAt_comm c.succ k (↑a) B
  | .el .. => by
      simp only [Ty.shiftAfter, Ty.substAt]
      congr 1
      · apply Tm.shift_substAt_comm

theorem Tm.shift_substAt_comm {n}
    (c : Idx (n + 1))
    (k : Nat)
    (a : Tm n) :
    (b : Tm (n + 1)) →
    Tm.substAt c.castSucc (a.shiftAfter (k + c.val) 1) (b.shiftAfter (k + c.val + 1) 1) =
    (Tm.substAt c a b).shiftAfter (k + c.val) 1
  | .var .. => by apply Idx.shift_substAt_comm
  | .const .. => by simp only [Tm.shiftAfter, Tm.substAt]
  | .lam ⟨x, A⟩ body => by
      simp only [Tm.shiftAfter, Tm.substAt]
      congr 2
      · exact Ty.shift_substAt_comm c k a A
      · rw [Fin.succ_castSucc, ← ha, add_succ_val]
        exact Tm.shift_substAt_comm c.succ k (↑a) body
  | .app .. => by
      simp only [Tm.shiftAfter, Tm.substAt]
      congr 1
      · apply Tm.shift_substAt_comm
      · apply Tm.shift_substAt_comm
  | .piHat .. => by
      simp only [Tm.shiftAfter, Tm.substAt]
      congr 1
      · apply Tm.shift_substAt_comm
      · rw [← ha, Fin.succ_castSucc, add_succ_val]
        apply Tm.shift_substAt_comm
  | .proj .. => by
      simp only [Tm.shiftAfter, Tm.substAt]
      congr 1
      · apply Tm.shift_substAt_comm
  | .letE .. => by
      simp only [Tm.shiftAfter, Tm.substAt]
      congr 1
      · apply Ty.shift_substAt_comm
      · apply Tm.shift_substAt_comm
      · rw [← ha, Fin.succ_castSucc, add_succ_val]
        apply Tm.shift_substAt_comm

end

theorem Ty.shift_subst_comm {n} :
    ∀ k (a : Tm n) (B : Ty (n + 1)),
    (B.shiftAfter (k + 1) 1)[a.shiftAfter k 1] = B[a].shiftAfter k 1 :=
  Ty.shift_substAt_comm 0

theorem Tm.shift_subst_comm {n} :
    ∀ k (a : Tm n) (b : Tm (n + 1)),
    (b.shiftAfter (k + 1) 1)[a.shiftAfter k 1] = b[a].shiftAfter k 1 :=
  Tm.shift_substAt_comm 0

end Qdt
