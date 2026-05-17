module

public import Qdt.Theory.Universe

@[expose] public section

namespace Qdt

namespace Universe

variable (ρ : Nat → Nat)

def denote (ρ : Nat → Nat) : Universe → Nat
  | .zero => 0
  | .level n => ρ n
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

def denote (ρ : Nat → Nat) : NF → Nat
  | ⟨c, L⟩ => Nat.max c (denoteList ρ L)

theorem denoteList_bound {n k : Nat} :
    ∀ {L : List (Nat × Nat)}, (n, k) ∈ L → ρ n + k ≤ denoteList ρ L
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (denoteList_bound h) (Nat.le_max_right _ _)

theorem maxOffset_le_denoteList : ∀ L, maxOffset L ≤ denoteList ρ L
  | [] => Nat.le_refl _
  | (n, k) :: rest => Nat.max_le.mpr ⟨
    Nat.le_trans (Nat.le_add_left k (ρ n)) (Nat.le_max_left _ _),
    Nat.le_trans (maxOffset_le_denoteList rest) (Nat.le_max_right _ _)⟩

@[simp] theorem zero_denote : NF.zero.denote ρ = 0 := rfl

@[simp] theorem level_denote (n) : (NF.level n).denote ρ = ρ n := by
  show Nat.max 0 (Nat.max (ρ n + 0) 0) = ρ n
  simp

theorem map_succ_denoteList : ∀ L,
    denoteList ρ (L.map fun (i, k) => (i, k + 1)) =
      if L.isEmpty then 0 else denoteList ρ L + 1
  | [] => rfl
  | (n, k) :: rest => by
    simp only [List.map_cons, denoteList, List.isEmpty_cons]
    rw [map_succ_denoteList rest]
    cases rest <;> grind [denoteList]

theorem succ_denote : ∀ nf, (succ nf).denote ρ = nf.denote ρ + 1
  | ⟨c, L⟩ => by
    unfold succ
    show Nat.max (c + 1) (denoteList ρ (L.map fun (i, k) => (i, k + 1))) = _
    rw [map_succ_denoteList]
    cases L <;> simp [denote, denoteList] <;> grind

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

theorem maxOf_denote : ∀ nf₁ nf₂,
    (maxOf nf₁ nf₂).denote ρ = Nat.max (nf₁.denote ρ) (nf₂.denote ρ)
  | ⟨_, _⟩, ⟨_, _⟩ => by
    unfold maxOf
    show Nat.max _ (denoteList ρ (merge _ _)) = _
    rw [merge_denoteList]
    simp [denote]
    grind

theorem ofUniverse_denote : ∀ u, (NF.ofUniverse u).denote ρ = Universe.denote ρ u
  | .zero => rfl
  | .level n => level_denote ρ n
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

theorem toUniverse_denote : ∀ (nf : NF), Universe.denote ρ nf.toUniverse = NF.denote ρ nf
  | ⟨c, []⟩ => by
    show Universe.denote ρ (Universe.zero.addOffset c) = Nat.max c 0
    rw [denote_addOffset]
    show 0 + c = Nat.max c 0
    grind
  | ⟨0, (_, _) :: _⟩ => by
    unfold toUniverse
    rw [reifyLevels_denote]
    simp only [denote, denoteList, denote_addOffset, Universe.denote, Nat.zero_max]
  | ⟨c + 1, (i, j) :: rest⟩ => by
    show Nat.max (Universe.denote ρ (reifyLevels _ rest))
            (Universe.denote ρ (Universe.zero.addOffset _)) = _
    rw [reifyLevels_denote, denote_addOffset, denote_addOffset]
    show Nat.max (Nat.max (ρ i + j) (denoteList ρ rest)) (0 + (c + 1))
       = Nat.max (c + 1) (Nat.max (ρ i + j) (denoteList ρ rest))
    grind

end NF

theorem normalise_denote (u : Universe) :
    Universe.denote ρ (normalise u) = Universe.denote ρ u := by
  unfold normalise; rw [NF.toUniverse_denote, NF.ofUniverse_denote]

end Universe

end Qdt
