module

public import Qdt.Theory.Universe.Denotation

@[expose] public section

namespace Qdt

namespace Universe

abbrev Atom : Type := Option Nat × Nat

namespace Atom

def eval (ρ : Nat → Nat) : Atom → Nat
  | (none, k) => k
  | (some i, k) => ρ i + k

theorem eval_zero_le_eval (ρ : Nat → Nat) : ∀ a, eval (fun _ => 0) a ≤ eval ρ a
  | (none, _) => Nat.le_refl _
  | (some _, _) => Nat.add_le_add_right (Nat.zero_le _) _

def dominates : Atom → Atom → Bool
  | (_, kb), (none, ka) => decide (ka ≤ kb)
  | (some j, kb), (some i, ka) => decide (i = j) && decide (ka ≤ kb)
  | (none, _), (some _, _) => false

theorem dominates_sound (ρ : Nat → Nat) : ∀ {b a : Atom}, dominates b a = true →
    eval ρ a ≤ eval ρ b
  | (none, _), (none, _), h => decide_eq_true_eq.mp h
  | (some _, _), (none, _), h => by
    have := decide_eq_true_eq.mp h
    simp only [eval]
    omega
  | (some _, _), (some _, _), h => by
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at h
    have ⟨rfl, hle⟩ := h
    show _ + _ ≤ _ + _
    omega
  | (none, _), (some _, _), h => by
    simp only [dominates, Bool.false_eq_true] at h

theorem dominates_complete : ∀ (b a : Atom),
    (∀ ρ, eval ρ a ≤ eval ρ b) → dominates b a = true
  | (none, _), (none, _), h => decide_eq_true_eq.mpr (h (fun _ => 0))
  | (some _, _), (none, _), h => by
    have := h (fun _ => 0)
    simp only [eval] at this
    exact decide_eq_true_eq.mpr (by omega)
  | (none, kb), (some i, _), h => by
    have := h (fun j => if j = i then kb + 1 else 0)
    simp only [eval, ↓reduceIte] at this
    omega
  | (some j, kb), (some i, ka), h => by
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hij : i = j
    · subst hij
      have := h (fun _ => 0)
      simp only [eval] at this
      exact ⟨rfl, by omega⟩
    · exfalso
      have := h (fun k => if k = i then kb + 1 else 0)
      have hji : ¬ j = i := fun e => hij e.symm
      simp only [eval, ↓reduceIte, if_neg hji] at this
      omega

theorem dominates_iff (b a : Atom) :
    dominates b a = true ↔ ∀ ρ, eval ρ a ≤ eval ρ b :=
  ⟨fun h ρ => dominates_sound ρ h, dominates_complete b a⟩

end Atom

namespace NF

theorem foldr_max_le_of_mem {x : Nat} : ∀ {L : List Nat}, x ∈ L → x ≤ L.foldr Nat.max 0
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (foldr_max_le_of_mem h) (Nat.le_max_right _ _)

theorem le_foldr_max_iff {x : Nat} : ∀ {L : List Nat},
    x ≤ L.foldr Nat.max 0 → x = 0 ∨ ∃ y ∈ L, x ≤ y
  | [], h => Or.inl (Nat.le_zero.mp h)
  | y :: L', h => by
    by_cases hxy : x ≤ y
    · exact Or.inr ⟨y, List.mem_cons_self, hxy⟩
    have h' : x ≤ Nat.max y _ := h
    have : x ≤ L'.foldr Nat.max 0 := by grind
    exact (le_foldr_max_iff this).imp_right fun ⟨z, hmem, hle⟩ =>
      ⟨z, List.mem_cons_of_mem _ hmem, hle⟩

theorem foldr_max_le_of_all {x : Nat} : ∀ {L : List Nat},
    (∀ y ∈ L, y ≤ x) → L.foldr Nat.max 0 ≤ x
  | [], _ => Nat.zero_le _
  | _ :: _, h => Nat.max_le.mpr
    ⟨h _ List.mem_cons_self,
     foldr_max_le_of_all fun _ hy => h _ (List.mem_cons_of_mem _ hy)⟩

def atoms : NF → List Atom
  | ⟨c, L⟩ => (none, c) :: L.map (fun (i, k) => (some i, k))

theorem atoms_ne_nil : ∀ nf : NF, nf.atoms ≠ []
  | ⟨_, _⟩ => List.cons_ne_nil _ _

theorem denoteList_eq_foldr (ρ : Nat → Nat) : ∀ L,
    denoteList ρ L = (L.map (fun (i, k) => ρ i + k)).foldr Nat.max 0
  | [] => rfl
  | (_, _) :: rest => congrArg (Nat.max _) (denoteList_eq_foldr ρ rest)

theorem atoms_map_eval (ρ : Nat → Nat) : ∀ nf : NF,
    nf.atoms.map (Atom.eval ρ) = nf.constant :: nf.levels.map (fun (i, k) => ρ i + k)
  | ⟨c, L⟩ => by
    show Atom.eval ρ (none, c) :: (L.map _).map (Atom.eval ρ) = _
    simp only [Atom.eval, List.map_map]
    rfl

theorem denote_eq_foldr_atoms (ρ : Nat → Nat) : ∀ nf : NF,
    denote ρ nf = (nf.atoms.map (Atom.eval ρ)).foldr Nat.max 0
  | ⟨c, L⟩ => by
    show Nat.max c _ = _
    rw [atoms_map_eval, denoteList_eq_foldr]
    rfl

end NF

namespace Atom

theorem extract_dominator : ∀ (a : Atom) (B : List Atom),
    B ≠ [] → (∀ ρ, eval ρ a ≤ (B.map (eval ρ)).foldr Nat.max 0) →
    ∃ b ∈ B, ∀ ρ, eval ρ a ≤ eval ρ b
  | (none, ka), B, hB, h => by
    by_cases hka : ka = 0
    · have ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
      exact ⟨b, hb, fun _ => hka ▸ Nat.zero_le _⟩
    rcases NF.le_foldr_max_iff (h (fun _ => 0)) with heq | ⟨_, hymem, hyle⟩
    · exact absurd heq hka
    have ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hymem
    exact ⟨b, hbmem, fun ρ => Nat.le_trans (hbeq ▸ hyle) (eval_zero_le_eval ρ b)⟩
  | (some i, ka), B, _, h => by
    let C := (B.map (eval (fun _ => 0))).foldr Nat.max 0
    let N := C + ka + 1
    let ρ_N : Nat → Nat := fun j => if j = i then N else 0
    have hρi : ρ_N i = N := if_pos rfl
    have hKey : N + ka ≤ (B.map (eval ρ_N)).foldr Nat.max 0 := hρi ▸ h ρ_N
    rcases NF.le_foldr_max_iff hKey with hzero | ⟨y, hymem, hyle⟩
    · exact absurd hzero (by show C + ka + 1 + ka ≠ 0; omega)
    have ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hymem
    have hbBound : eval (fun _ => 0) b ≤ C :=
      NF.foldr_max_le_of_mem (List.mem_map_of_mem hbmem)
    rcases b with ⟨_ | j, kb⟩
    · simp only [eval] at hbeq hbBound
      omega
    · simp only [eval] at hbeq hbBound
      by_cases hji : j = i
      · subst hji
        refine ⟨_, hbmem, fun ρ => ?_⟩
        show ρ j + ka ≤ ρ j + kb
        rw [hρi] at hbeq
        omega
      · have : ρ_N j = 0 := if_neg hji
        rw [this] at hbeq
        omega

end Atom

namespace NF

def NFle (u v : NF) : Bool :=
  u.atoms.all fun a => v.atoms.any fun b => Atom.dominates b a

theorem NFle_iff (u v : NF) :
    NFle u v = true ↔ ∀ ρ, NF.denote ρ u ≤ NF.denote ρ v := by
  simp only [NFle, List.all_eq_true, List.any_eq_true]
  refine ⟨fun h ρ => ?_, fun h a ha => ?_⟩
  · rw [denote_eq_foldr_atoms, denote_eq_foldr_atoms]
    apply foldr_max_le_of_all
    intro y hy
    have ⟨a, ha, haeq⟩ := List.mem_map.mp hy
    have ⟨b, hbmem, hdom⟩ := h a ha
    exact haeq ▸ Nat.le_trans (Atom.dominates_sound ρ hdom)
      (foldr_max_le_of_mem (List.mem_map_of_mem hbmem))
  · have hPoint : ∀ ρ, Atom.eval ρ a ≤ (v.atoms.map (Atom.eval ρ)).foldr Nat.max 0 := fun ρ => by
      rw [← denote_eq_foldr_atoms]
      exact Nat.le_trans
        (denote_eq_foldr_atoms ρ u ▸ foldr_max_le_of_mem (List.mem_map_of_mem ha)) (h ρ)
    have ⟨b, hbmem, hb⟩ := Atom.extract_dominator a v.atoms (atoms_ne_nil v) hPoint
    exact ⟨b, hbmem, Atom.dominates_complete b a hb⟩

end NF

instance : LE Universe :=
  ⟨fun u v => ∀ ρ : Nat → Nat, denote ρ u ≤ denote ρ v⟩

theorem le_def (u v : Universe) : u ≤ v ↔ ∀ ρ, denote ρ u ≤ denote ρ v := Iff.rfl

instance : DecidableLE Universe := fun u v =>
  decidable_of_iff (NF.NFle (NF.ofUniverse u) (NF.ofUniverse v) = true) <| by
    simp only [NF.NFle_iff, NF.ofUniverse_denote, le_def]

theorem le_refl' (u : Universe) : u ≤ u := fun _ => Nat.le_refl _

theorem le_trans' {u v w : Universe} (h₁ : u ≤ v) (h₂ : v ≤ w) : u ≤ w :=
  fun ρ => Nat.le_trans (h₁ ρ) (h₂ ρ)

end Universe

end Qdt
