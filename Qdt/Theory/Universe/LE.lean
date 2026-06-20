module

public import Qdt.Theory.Universe.Denotation

@[expose] public section

namespace Qdt

open Lean (Name)

namespace Universe

abbrev AtomKey : Type := Name ⊕ UMVarId

abbrev Atom : Type := Option AtomKey × Nat

namespace Atom

def eval (θ : Valuation) : Atom → Nat
  | (none, k) => k
  | (some key, k) => θ key + k

theorem eval_zero_le_eval (θ : Valuation) : ∀ a, eval (fun _ => 0) a ≤ eval θ a
  | (none, _) => Nat.le_refl _
  | (some _, _) => Nat.add_le_add_right (Nat.zero_le _) _

def dominates : Atom → Atom → Bool
  | (_, kb), (none, ka) => decide (ka ≤ kb)
  | (some jb, kb), (some ja, ka) => decide (jb = ja) && decide (ka ≤ kb)
  | (none, _), (some _, _) => false

theorem dominates_sound (θ : Valuation) : ∀ {b a : Atom}, dominates b a = true →
    eval θ a ≤ eval θ b
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
    (∀ θ, eval θ a ≤ eval θ b) → dominates b a = true
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
    by_cases hij : j = i
    · subst hij
      have := h (fun _ => 0)
      simp only [eval] at this
      exact ⟨rfl, by omega⟩
    · exfalso
      have := h (fun k => if k = i then kb + 1 else 0)
      have hji : ¬ j = i := hij
      simp only [eval, ↓reduceIte, if_neg hji] at this
      omega

theorem dominates_iff (b a : Atom) :
    dominates b a = true ↔ ∀ θ, eval θ a ≤ eval θ b :=
  ⟨fun h θ => dominates_sound θ h, dominates_complete b a⟩

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
  | ⟨c, L, M⟩ =>
    (none, c) :: L.map (fun (n, k) => (some (.inl n), k)) ++ M.map (fun (id, k) => (some (.inr id), k))

theorem atoms_ne_nil : ∀ nf : NF, nf.atoms ≠ []
  | ⟨_, _, _⟩ => List.cons_ne_nil _ _

theorem denoteList_eq_foldr (θ : Valuation) : ∀ L,
    denoteList θ L = (L.map (fun (n, k) => θ (.inl n) + k)).foldr Nat.max 0
  | [] => rfl
  | (_, _) :: rest => congrArg (Nat.max _) (denoteList_eq_foldr θ rest)

theorem denoteMVars_eq_foldr (θ : Valuation) : ∀ M,
    denoteMVars θ M = (M.map (fun (id, k) => θ (.inr id) + k)).foldr Nat.max 0
  | [] => rfl
  | (_, _) :: rest => congrArg (Nat.max _) (denoteMVars_eq_foldr θ rest)

theorem foldr_max_append : ∀ (xs ys : List Nat),
    (xs ++ ys).foldr Nat.max 0 = Nat.max (xs.foldr Nat.max 0) (ys.foldr Nat.max 0)
  | [], ys => by simp
  | x :: xs, ys => by
    simp only [List.cons_append, List.foldr_cons, foldr_max_append xs ys]
    grind

theorem denote_eq_foldr_atoms (θ : Valuation) : ∀ nf : NF,
    denote θ nf = (nf.atoms.map (Atom.eval θ)).foldr Nat.max 0
  | ⟨c, L, M⟩ => by
    show Nat.max c (Nat.max (denoteList θ L) (denoteMVars θ M))
       = List.foldr Nat.max 0 (List.map (Atom.eval θ)
           ((none, c) :: L.map (fun (n, k) => (some (.inl n), k))
             ++ M.map (fun (id, k) => (some (.inr id), k))))
    rw [denoteList_eq_foldr, denoteMVars_eq_foldr]
    simp only [List.map_cons, List.map_append, List.map_map, List.foldr_cons, foldr_max_append]
    have hL : List.map (Atom.eval θ ∘ fun (p : Name × Nat) => ((some (.inl p.1), p.2) : Atom)) L
            = List.map (fun p => θ (.inl p.1) + p.2) L := by
      apply List.map_congr_left; intro ⟨_, _⟩ _; rfl
    have hM : List.map (Atom.eval θ ∘ fun (p : UMVarId × Nat) => ((some (.inr p.1), p.2) : Atom)) M
            = List.map (fun p => θ (.inr p.1) + p.2) M := by
      apply List.map_congr_left; intro ⟨_, _⟩ _; rfl
    rw [hL, hM]
    show Nat.max c (Nat.max _ _) = Nat.max (Nat.max (Atom.eval θ (none, c)) _) _
    simp [Atom.eval, ← Nat.max_assoc]

end NF

namespace Atom

theorem extract_dominator : ∀ (a : Atom) (B : List Atom),
    B ≠ [] → (∀ θ, eval θ a ≤ (B.map (eval θ)).foldr Nat.max 0) →
    ∃ b ∈ B, ∀ θ, eval θ a ≤ eval θ b
  | (none, ka), B, hB, h => by
    by_cases hka : ka = 0
    · have ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
      exact ⟨b, hb, fun _ => hka ▸ Nat.zero_le _⟩
    rcases NF.le_foldr_max_iff (h (fun _ => 0)) with heq | ⟨_, hymem, hyle⟩
    · exact absurd heq hka
    have ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hymem
    exact ⟨b, hbmem, fun θ => Nat.le_trans (hbeq ▸ hyle) (eval_zero_le_eval θ b)⟩
  | (some i, ka), B, _, h => by
    let C := (B.map (eval (fun _ => 0))).foldr Nat.max 0
    let N := C + ka + 1
    let θ_N : Valuation := fun j => if j = i then N else 0
    have hθi : θ_N i = N := if_pos rfl
    have hKey : N + ka ≤ (B.map (eval θ_N)).foldr Nat.max 0 := hθi ▸ h θ_N
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
        refine ⟨_, hbmem, fun θ => ?_⟩
        show θ j + ka ≤ θ j + kb
        rw [hθi] at hbeq
        omega
      · have : θ_N j = 0 := if_neg hji
        rw [this] at hbeq
        omega

end Atom

namespace NF

def NFle (u v : NF) : Bool :=
  u.atoms.all fun a => v.atoms.any fun b => Atom.dominates b a

theorem NFle_iff (u v : NF) :
    NFle u v = true ↔ ∀ θ, NF.denote θ u ≤ NF.denote θ v := by
  simp only [NFle, List.all_eq_true, List.any_eq_true]
  refine ⟨fun h θ => ?_, fun h a ha => ?_⟩
  · rw [denote_eq_foldr_atoms, denote_eq_foldr_atoms]
    apply foldr_max_le_of_all
    intro y hy
    have ⟨a, ha, haeq⟩ := List.mem_map.mp hy
    have ⟨b, hbmem, hdom⟩ := h a ha
    exact haeq ▸ Nat.le_trans (Atom.dominates_sound θ hdom)
      (foldr_max_le_of_mem (List.mem_map_of_mem hbmem))
  · have hPoint : ∀ θ, Atom.eval θ a ≤ (v.atoms.map (Atom.eval θ)).foldr Nat.max 0 := fun θ => by
      rw [← denote_eq_foldr_atoms]
      exact Nat.le_trans
        (denote_eq_foldr_atoms θ u ▸ foldr_max_le_of_mem (List.mem_map_of_mem ha)) (h θ)
    have ⟨b, hbmem, hb⟩ := Atom.extract_dominator a v.atoms (atoms_ne_nil v) hPoint
    exact ⟨b, hbmem, Atom.dominates_complete b a hb⟩

end NF

instance : LE Universe :=
  ⟨fun u v => ∀ θ : Valuation, denote θ u ≤ denote θ v⟩

theorem le_def (u v : Universe) : u ≤ v ↔ ∀ θ, denote θ u ≤ denote θ v := Iff.rfl

instance : DecidableLE Universe := fun u v =>
  decidable_of_iff (NF.NFle (NF.ofUniverse u) (NF.ofUniverse v) = true) <| by
    simp only [NF.NFle_iff, NF.ofUniverse_denote, le_def]

theorem le_refl' (u : Universe) : u ≤ u := fun _ => Nat.le_refl _

theorem le_trans' {u v w : Universe} (h₁ : u ≤ v) (h₂ : v ≤ w) : u ≤ w :=
  fun θ => Nat.le_trans (h₁ θ) (h₂ θ)

end Universe

end Qdt
