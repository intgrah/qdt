module

public import Qdt.Theory.Universe

@[expose] public section

namespace Qdt

open Lean (Name)

namespace Universe

abbrev Valuation := Name ⊕ UMVarId → Nat

variable (θ : Valuation)

def denote (θ : Valuation) : Universe → Nat
  | .zero => 0
  | .param n => θ (.inl n)
  | .mvar id => θ (.inr id)
  | .succ u => denote θ u + 1
  | .max u v => Nat.max (denote θ u) (denote θ v)

theorem denote_addOffset : ∀ k u, denote θ (u.addOffset k) = denote θ u + k
  | 0, _ => rfl
  | k + 1, u => by
    show denote θ (u.succ.addOffset k) = _
    rw [denote_addOffset k u.succ]
    show denote θ u + 1 + k = _
    omega

namespace NF

def denoteList (θ : Valuation) : List (Name × Nat) → Nat
  | [] => 0
  | (n, k) :: rest => Nat.max (θ (.inl n) + k) (denoteList θ rest)

def denoteMVars (θ : Valuation) : List (UMVarId × Nat) → Nat
  | [] => 0
  | (id, k) :: rest => Nat.max (θ (.inr id) + k) (denoteMVars θ rest)

def denote (θ : Valuation) : NF → Nat
  | ⟨c, L, M⟩ => Nat.max c (Nat.max (denoteList θ L) (denoteMVars θ M))

theorem denoteList_bound {n : Name} {k : Nat} :
    ∀ {L : List (Name × Nat)}, (n, k) ∈ L → θ (.inl n) + k ≤ denoteList θ L
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (denoteList_bound h) (Nat.le_max_right _ _)

theorem denoteList_offset_bound {n : Name} {k : Nat} :
    ∀ {L : List (Name × Nat)}, (n, k) ∈ L → k ≤ denoteList θ L :=
  fun h => Nat.le_trans (Nat.le_add_left _ _) (denoteList_bound (θ := θ) h)

theorem denoteMVars_bound {id k : Nat} :
    ∀ {M : List (UMVarId × Nat)}, (id, k) ∈ M → θ (.inr id) + k ≤ denoteMVars θ M
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (denoteMVars_bound h) (Nat.le_max_right _ _)

theorem denoteMVars_offset_bound {id k : Nat} :
    ∀ {M : List (UMVarId × Nat)}, (id, k) ∈ M → k ≤ denoteMVars θ M :=
  fun h => Nat.le_trans (Nat.le_add_left _ _) (denoteMVars_bound (θ := θ) h)

theorem maxOffset_le_denoteList : ∀ L, maxOffset L ≤ denoteList θ L
  | [] => Nat.le_refl _
  | (n, k) :: rest => Nat.max_le.mpr ⟨
    Nat.le_trans (Nat.le_add_left k (θ (.inl n))) (Nat.le_max_left _ _),
    Nat.le_trans (maxOffset_le_denoteList rest) (Nat.le_max_right _ _)⟩

@[simp] theorem zero_denote : NF.zero.denote θ = 0 := rfl

@[simp] theorem param_denote (n) : (NF.param n).denote θ = θ (.inl n) := by
  show Nat.max 0 (Nat.max (Nat.max (θ (.inl n) + 0) 0) 0) = θ (.inl n)
  simp

@[simp] theorem mvar_denote (id) : (NF.mvar id).denote θ = θ (.inr id) := by
  show Nat.max 0 (Nat.max 0 (Nat.max (θ (.inr id) + 0) 0)) = θ (.inr id)
  simp

theorem map_succ_denoteList : ∀ L,
    denoteList θ (L.map fun (n, k) => (n, k + 1)) =
      if L.isEmpty then 0 else denoteList θ L + 1
  | [] => rfl
  | (n, k) :: rest => by
    simp only [List.map_cons, denoteList, List.isEmpty_cons]
    rw [map_succ_denoteList rest]
    cases rest <;> grind [denoteList]

theorem map_succ_denoteMVars : ∀ M,
    denoteMVars θ (M.map fun (id, k) => (id, k + 1)) =
      if M.isEmpty then 0 else denoteMVars θ M + 1
  | [] => rfl
  | (id, k) :: rest => by
    simp only [List.map_cons, denoteMVars, List.isEmpty_cons]
    rw [map_succ_denoteMVars rest]
    cases rest <;> grind [denoteMVars]

theorem succ_denote : ∀ nf, (succ nf).denote θ = nf.denote θ + 1
  | ⟨c, L, M⟩ => by
    unfold succ
    show Nat.max (c + 1) (Nat.max
      (denoteList θ (L.map fun (n, k) => (n, k + 1)))
      (denoteMVars θ (M.map fun (id, k) => (id, k + 1)))) = _
    rw [map_succ_denoteList, map_succ_denoteMVars]
    cases L <;> cases M <;> simp [denote, denoteList, denoteMVars] <;> grind

theorem merge_denoteList : ∀ L L',
    denoteList θ (merge L L') = Nat.max (denoteList θ L) (denoteList θ L')
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
    · simp only [denoteList, merge_denoteList ((n₁, k₁) :: xs) ys]
      grind
    · next h =>
      obtain rfl := nameCmp_eq h
      simp only [denoteList, merge_denoteList xs ys]
      grind

theorem mergeMVars_denoteMVars : ∀ M M',
    denoteMVars θ (mergeMVars M M') = Nat.max (denoteMVars θ M) (denoteMVars θ M')
  | [], _ => by unfold mergeMVars; simp [denoteMVars]
  | (_, _) :: _, [] => by unfold mergeMVars; simp [denoteMVars]
  | (i₁, k₁) :: xs, (i₂, k₂) :: ys => by
    unfold mergeMVars
    split
    · simp only [denoteMVars, mergeMVars_denoteMVars xs ((i₂, k₂) :: ys)]
      grind
    · simp only [denoteMVars, mergeMVars_denoteMVars ((i₁, k₁) :: xs) ys]
      grind
    · next h =>
      obtain rfl := Std.LawfulEqOrd.eq_of_compare (α := Nat) h
      simp only [denoteMVars, mergeMVars_denoteMVars xs ys]
      grind

theorem maxOf_denote : ∀ nf₁ nf₂,
    (maxOf nf₁ nf₂).denote θ = Nat.max (nf₁.denote θ) (nf₂.denote θ)
  | ⟨_, _, _⟩, ⟨_, _, _⟩ => by
    unfold maxOf
    show Nat.max _ (Nat.max (denoteList θ (merge _ _)) (denoteMVars θ (mergeMVars _ _))) = _
    rw [merge_denoteList, mergeMVars_denoteMVars]
    simp [denote]
    grind

theorem ofUniverse_denote : ∀ u, (NF.ofUniverse u).denote θ = Universe.denote θ u
  | .zero => rfl
  | .param n => param_denote θ n
  | .mvar id => mvar_denote θ id
  | .succ u => by
    show (NF.succ (ofUniverse u)).denote θ = _
    rw [succ_denote, ofUniverse_denote u]
    rfl
  | .max u v => by
    show (NF.maxOf (ofUniverse u) (ofUniverse v)).denote θ = _
    rw [maxOf_denote, ofUniverse_denote u, ofUniverse_denote v]
    rfl

theorem reifyParams_denote : ∀ (seed : Universe) L,
    Universe.denote θ (reifyParams seed L)
      = Nat.max (Universe.denote θ seed) (denoteList θ L)
  | seed, [] => by
    show Universe.denote θ seed = Nat.max (Universe.denote θ seed) 0
    grind
  | seed, (n, j) :: rest => by
    change Universe.denote θ
            (reifyParams (Universe.max seed ((Universe.param n).addOffset j)) rest)
        = Nat.max (Universe.denote θ seed) (denoteList θ ((n, j) :: rest))
    rw [reifyParams_denote]
    simp only [Universe.denote, denote_addOffset, denoteList]
    show Nat.max (Nat.max (Universe.denote θ seed) (θ (.inl n) + j)) (denoteList θ rest)
       = Nat.max (Universe.denote θ seed) (Nat.max (θ (.inl n) + j) (denoteList θ rest))
    grind

theorem reifyMVars_denote : ∀ (seed : Universe) M,
    Universe.denote θ (reifyMVars seed M)
      = Nat.max (Universe.denote θ seed) (denoteMVars θ M)
  | seed, [] => by
    show Universe.denote θ seed = Nat.max (Universe.denote θ seed) 0
    grind
  | seed, (id, j) :: rest => by
    change Universe.denote θ
            (reifyMVars (Universe.max seed ((Universe.mvar id).addOffset j)) rest)
        = Nat.max (Universe.denote θ seed) (denoteMVars θ ((id, j) :: rest))
    rw [reifyMVars_denote]
    simp only [Universe.denote, denote_addOffset, denoteMVars]
    show Nat.max (Nat.max (Universe.denote θ seed) (θ (.inr id) + j)) (denoteMVars θ rest)
       = Nat.max (Universe.denote θ seed) (Nat.max (θ (.inr id) + j) (denoteMVars θ rest))
    grind

theorem toUniverse_denote : ∀ (nf : NF), Universe.denote θ nf.toUniverse = NF.denote θ nf
  | ⟨0, [], []⟩ => by simp [toUniverse, Universe.denote, denote, denoteList, denoteMVars]
  | ⟨0, (n, j) :: rest, M⟩ => by
    unfold toUniverse
    rw [reifyMVars_denote, reifyParams_denote]
    simp only [denote, denoteList, denote_addOffset, Universe.denote, Nat.zero_max]
  | ⟨0, [], (id, j) :: rest⟩ => by
    unfold toUniverse
    rw [reifyMVars_denote]
    simp only [denote, denoteList, denoteMVars, denote_addOffset, Universe.denote, Nat.zero_max]
  | ⟨c + 1, [], []⟩ => by
    simp [toUniverse, denote, denoteList, denoteMVars, Universe.denote, denote_addOffset]
  | ⟨c + 1, [], (id, j) :: rest⟩ => by
    simp only [toUniverse]
    split
    next hCond =>
      rw [reifyMVars_denote, denote_addOffset]
      simp only [Universe.denote, denote, denoteList, denoteMVars]
      have : c + 1 ≤ Nat.max (θ (.inr id) + j) (denoteMVars θ rest) := by
        rcases hCond with h | h
        · exact Nat.le_trans h (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _))
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteMVars_offset_bound (θ := θ) hMem) (Nat.le_max_right _ _))
      grind
    next =>
      show Nat.max (Universe.denote θ (reifyMVars ((Universe.mvar id).addOffset j) rest))
              (Universe.denote θ (Universe.zero.addOffset (c + 1))) = _
      rw [reifyMVars_denote, denote_addOffset]
      simp only [Universe.denote, denote, denoteList, denoteMVars, denote_addOffset]
      grind
  | ⟨c + 1, (n, j) :: rest, M⟩ => by
    simp only [toUniverse]
    split
    next hCond =>
      rw [reifyMVars_denote, reifyParams_denote, denote_addOffset]
      simp only [Universe.denote, denote, denoteList]
      have : c + 1 ≤ Nat.max (Nat.max (θ (.inl n) + j) (denoteList θ rest)) (denoteMVars θ M) := by
        rcases hCond with h | h | h
        · exact Nat.le_trans
            (Nat.le_trans h (Nat.le_add_left _ (θ (.inl n))))
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteList_offset_bound (θ := θ) hMem)
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)))
        · simp only [List.any_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨_, k'⟩, hMem, hk'⟩ := h
          exact Nat.le_trans hk'
            (Nat.le_trans (denoteMVars_offset_bound (θ := θ) hMem) (Nat.le_max_right _ _))
      grind
    next =>
      show Nat.max (Universe.denote θ
              (reifyMVars (reifyParams ((Universe.param n).addOffset j) rest) M))
              (Universe.denote θ (Universe.zero.addOffset (c + 1))) = _
      rw [reifyMVars_denote, reifyParams_denote, denote_addOffset]
      simp only [Universe.denote, Nat.zero_add, denote, denoteList, denote_addOffset]
      grind

end NF

theorem normalise_denote (u : Universe) :
    Universe.denote θ (normalise u) = Universe.denote θ u := by
  unfold normalise; rw [NF.toUniverse_denote, NF.ofUniverse_denote]

end Universe

end Qdt
