module

public import Qdt.Theory.Universe

@[expose] public section

namespace Qdt

namespace Universe

variable (ρ : Nat → Nat)

def denote (ρ : Nat → Nat) : Universe → Nat
  | .zero => 0
  | .level n => ρ n
  | .mvar _ => 0
  | .succ u => denote ρ u + 1
  | .max u v => Nat.max (denote ρ u) (denote ρ v)

theorem denote_addOffset : ∀ k u, denote ρ (u.addOffset k) = denote ρ u + k
  | 0, _ => rfl
  | k + 1, u => by
    show denote ρ (u.succ.addOffset k) = _
    rw [denote_addOffset k u.succ]
    show denote ρ u + 1 + k = _
    omega

namespace NF

def denoteList (ρ : Nat → Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (n, k) :: rest => Nat.max (ρ n + k) (denoteList ρ rest)

def denoteMVars : List (UMVarId × Nat) → Nat
  | [] => 0
  | (_, k) :: rest => Nat.max k (denoteMVars rest)

def denote (ρ : Nat → Nat) : NF → Nat
  | ⟨c, L, M⟩ => Nat.max c (Nat.max (denoteList ρ L) (denoteMVars M))

theorem denoteList_bound {n k : Nat} :
    ∀ {L : List (Nat × Nat)}, (n, k) ∈ L → ρ n + k ≤ denoteList ρ L
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (denoteList_bound h) (Nat.le_max_right _ _)

theorem denoteList_offset_bound {n k : Nat} :
    ∀ {L : List (Nat × Nat)}, (n, k) ∈ L → k ≤ denoteList ρ L :=
  fun h => Nat.le_trans (Nat.le_add_left _ _) (denoteList_bound (ρ := ρ) h)

theorem denoteMVars_bound {id k : Nat} :
    ∀ {M : List (UMVarId × Nat)}, (id, k) ∈ M → k ≤ denoteMVars M
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (denoteMVars_bound h) (Nat.le_max_right _ _)

theorem maxOffset_le_denoteList : ∀ L, maxOffset L ≤ denoteList ρ L
  | [] => Nat.le_refl _
  | (n, k) :: rest => Nat.max_le.mpr ⟨
    Nat.le_trans (Nat.le_add_left k (ρ n)) (Nat.le_max_left _ _),
    Nat.le_trans (maxOffset_le_denoteList rest) (Nat.le_max_right _ _)⟩

@[simp] theorem zero_denote : NF.zero.denote ρ = 0 := rfl

@[simp] theorem level_denote (n) : (NF.level n).denote ρ = ρ n := by
  show Nat.max 0 (Nat.max (Nat.max (ρ n + 0) 0) 0) = ρ n
  simp

@[simp] theorem mvar_denote (id) : (NF.mvar id).denote ρ = 0 := by
  show Nat.max 0 (Nat.max 0 (Nat.max (0 + 0) 0)) = 0
  simp

theorem map_succ_denoteList : ∀ L,
    denoteList ρ (L.map fun (i, k) => (i, k + 1)) =
      if L.isEmpty then 0 else denoteList ρ L + 1
  | [] => rfl
  | (n, k) :: rest => by
    simp only [List.map_cons, denoteList, List.isEmpty_cons]
    rw [map_succ_denoteList rest]
    cases rest <;> grind [denoteList]

theorem map_succ_denoteMVars : ∀ M,
    denoteMVars (M.map fun (id, k) => (id, k + 1)) =
      if M.isEmpty then 0 else denoteMVars M + 1
  | [] => rfl
  | (_, k) :: rest => by
    simp only [List.map_cons, denoteMVars, List.isEmpty_cons]
    rw [map_succ_denoteMVars rest]
    cases rest <;> grind [denoteMVars]

theorem succ_denote : ∀ nf, (succ nf).denote ρ = nf.denote ρ + 1
  | ⟨c, L, M⟩ => by
    unfold succ
    show Nat.max (c + 1) (Nat.max
      (denoteList ρ (L.map fun (i, k) => (i, k + 1)))
      (denoteMVars (M.map fun (id, k) => (id, k + 1)))) = _
    rw [map_succ_denoteList, map_succ_denoteMVars]
    cases L <;> cases M <;> simp [denote, denoteList, denoteMVars] <;> grind

theorem merge_denoteList : ∀ L L',
    denoteList ρ (merge L L') = Nat.max (denoteList ρ L) (denoteList ρ L')
  | [], _ => by
    unfold merge
    simp [denoteList]
  | (_, _) :: _, [] => by
    unfold merge
    simp [denoteList]
  | (n₁, k₁) :: xs, (n₂, k₂) :: ys => by
    unfold merge
    split
    · simp only [denoteList, merge_denoteList xs ((n₂, k₂) :: ys)]
      grind
    · split
      · simp only [denoteList, merge_denoteList ((n₁, k₁) :: xs) ys]
        grind
      · obtain rfl : n₁ = n₂ := by omega
        simp only [denoteList, merge_denoteList xs ys]
        grind

theorem merge_denoteMVars : ∀ M M',
    denoteMVars (merge M M') = Nat.max (denoteMVars M) (denoteMVars M')
  | [], _ => by unfold merge; simp [denoteMVars]
  | (_, _) :: _, [] => by unfold merge; simp [denoteMVars]
  | (n₁, k₁) :: xs, (n₂, k₂) :: ys => by
    unfold merge
    split
    · simp only [denoteMVars, merge_denoteMVars xs ((n₂, k₂) :: ys)]
      grind
    · split
      · simp only [denoteMVars, merge_denoteMVars ((n₁, k₁) :: xs) ys]
        grind
      · obtain rfl : n₁ = n₂ := by omega
        simp only [denoteMVars, merge_denoteMVars xs ys]
        grind

theorem maxOf_denote : ∀ nf₁ nf₂,
    (maxOf nf₁ nf₂).denote ρ = Nat.max (nf₁.denote ρ) (nf₂.denote ρ)
  | ⟨_, _, _⟩, ⟨_, _, _⟩ => by
    unfold maxOf
    show Nat.max _ (Nat.max (denoteList ρ (merge _ _)) (denoteMVars (merge _ _))) = _
    rw [merge_denoteList, merge_denoteMVars]
    simp [denote]
    grind

theorem ofUniverse_denote : ∀ u, (NF.ofUniverse u).denote ρ = Universe.denote ρ u
  | .zero => rfl
  | .level n => level_denote ρ n
  | .mvar id => mvar_denote ρ id
  | .succ u => by
    show (NF.succ (ofUniverse u)).denote ρ = _
    rw [succ_denote, ofUniverse_denote u]
    rfl
  | .max u v => by
    show (NF.maxOf (ofUniverse u) (ofUniverse v)).denote ρ = _
    rw [maxOf_denote, ofUniverse_denote u, ofUniverse_denote v]
    rfl

theorem reifyLevels_denote : ∀ (seed : Universe) L,
    Universe.denote ρ (reifyLevels seed L)
      = Nat.max (Universe.denote ρ seed) (denoteList ρ L)
  | seed, [] => by
    show Universe.denote ρ seed = Nat.max (Universe.denote ρ seed) 0
    grind
  | seed, (i, j) :: rest => by
    change Universe.denote ρ
            (reifyLevels (Universe.max seed ((Universe.level i).addOffset j)) rest)
        = Nat.max (Universe.denote ρ seed) (denoteList ρ ((i, j) :: rest))
    rw [reifyLevels_denote]
    simp only [Universe.denote, denote_addOffset, denoteList]
    show Nat.max (Nat.max (Universe.denote ρ seed) (ρ i + j)) (denoteList ρ rest)
       = Nat.max (Universe.denote ρ seed) (Nat.max (ρ i + j) (denoteList ρ rest))
    grind

theorem reifyMVars_denote : ∀ (seed : Universe) M,
    Universe.denote ρ (reifyMVars seed M)
      = Nat.max (Universe.denote ρ seed) (denoteMVars M)
  | seed, [] => by
    show Universe.denote ρ seed = Nat.max (Universe.denote ρ seed) 0
    grind
  | seed, (id, j) :: rest => by
    change Universe.denote ρ
            (reifyMVars (Universe.max seed ((Universe.mvar id).addOffset j)) rest)
        = Nat.max (Universe.denote ρ seed) (denoteMVars ((id, j) :: rest))
    rw [reifyMVars_denote]
    simp only [Universe.denote, denote_addOffset, denoteMVars]
    show Nat.max (Nat.max (Universe.denote ρ seed) (0 + j)) (denoteMVars rest)
       = Nat.max (Universe.denote ρ seed) (Nat.max j (denoteMVars rest))
    grind

theorem toUniverse_denote : ∀ (nf : NF), Universe.denote ρ nf.toUniverse = NF.denote ρ nf
  | ⟨0, [], []⟩ => by simp [toUniverse, Universe.denote, denote, denoteList, denoteMVars]
  | ⟨0, (i, j) :: rest, M⟩ => by
    unfold toUniverse
    rw [reifyMVars_denote, reifyLevels_denote]
    simp only [denote, denoteList, denote_addOffset, Universe.denote, Nat.zero_max]
  | ⟨0, [], (id, j) :: rest⟩ => by
    unfold toUniverse
    rw [reifyMVars_denote]
    simp only [denote, denoteList, denoteMVars, denote_addOffset, Universe.denote,
      Nat.zero_max, Nat.zero_add]
  | ⟨c + 1, [], []⟩ => by
    simp [toUniverse, denote, denoteList, denoteMVars, Universe.denote, denote_addOffset]
  | ⟨c + 1, [], (id, j) :: rest⟩ => by
    simp only [toUniverse]
    split
    next hCond =>
      rw [reifyMVars_denote, denote_addOffset]
      simp only [Universe.denote, Nat.zero_add, denote, denoteList, denoteMVars]
      have : c + 1 ≤ Nat.max j (denoteMVars rest) := by
        rcases hCond with h | h
        · exact Nat.le_trans h (Nat.le_max_left _ _)
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteMVars_bound hMem) (Nat.le_max_right _ _))
      grind
    next =>
      show Nat.max (Universe.denote ρ (reifyMVars ((Universe.mvar id).addOffset j) rest))
              (Universe.denote ρ (Universe.zero.addOffset (c + 1))) = _
      rw [reifyMVars_denote, denote_addOffset]
      simp only [Universe.denote, Nat.zero_add, denote, denoteList, denoteMVars, denote_addOffset]
      grind
  | ⟨c + 1, (i, j) :: rest, M⟩ => by
    simp only [toUniverse]
    split
    next hCond =>
      rw [reifyMVars_denote, reifyLevels_denote, denote_addOffset]
      simp only [Universe.denote, Nat.zero_add, denote, denoteList, denoteMVars]
      have : c + 1 ≤ Nat.max (Nat.max (ρ i + j) (denoteList ρ rest)) (denoteMVars M) := by
        rcases hCond with h | h | h
        · exact Nat.le_trans
            (Nat.le_trans h (Nat.le_add_left _ (ρ i)))
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteList_offset_bound (ρ := ρ) hMem)
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteMVars_bound hMem) (Nat.le_max_right _ _))
      grind
    next =>
      show Nat.max (Universe.denote ρ
              (reifyMVars (reifyLevels ((Universe.level i).addOffset j) rest) M))
              (Universe.denote ρ (Universe.zero.addOffset (c + 1))) = _
      rw [reifyMVars_denote, reifyLevels_denote, denote_addOffset]
      simp only [Universe.denote, Nat.zero_add, denote, denoteList, denoteMVars, denote_addOffset]
      grind

end NF

theorem normalise_denote (u : Universe) :
    Universe.denote ρ (normalise u) = Universe.denote ρ u := by
  unfold normalise; rw [NF.toUniverse_denote, NF.ofUniverse_denote]

end Universe

end Qdt
