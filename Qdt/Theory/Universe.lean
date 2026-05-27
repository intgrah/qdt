module

@[expose] public section

namespace Qdt

open Lean (Name)

abbrev UMVarId := Nat

inductive Universe
  | level (i : Nat)
  | zero
  | succ (u : Universe)
  | max (u v : Universe)
  | mvar (id : UMVarId)
deriving Inhabited, Hashable, DecidableEq

namespace Universe

instance {n} : OfNat Universe n where
  ofNat := n.repeat .succ .zero

instance : HAdd Universe Nat Universe where
  hAdd i n := n.repeat .succ i

open Lean (Name)

def parenIf (p : Bool) : Std.Format → Std.Format :=
  if p then .paren else id

protected def fmt (univs : List Name) (u : Universe) (prec : Nat) : Std.Format :=
  match u with
  | .zero => "0"
  | .level i =>
    match univs[i]? with
    | some n => Std.Format.text n.toString
    | none => "u#" ++ repr i
  | .mvar id => "?u#" ++ repr id
  | .succ u' =>
    let rec countSuccs (acc : Nat) : Universe → Nat × Std.Format
      | .succ u'' => countSuccs (acc + 1) u''
      | .zero => (acc + 1, repr (acc + 1))
      | base => (acc + 1, parenIf (prec > 10) (base.fmt univs 66 ++ " + " ++ repr (acc + 1)))
    (countSuccs 0 u').snd
  | .max u' v' =>
    parenIf (prec > 10) ("max " ++ u'.fmt univs 11 ++ " " ++ v'.fmt univs 11)

protected def reprPrec (u : Universe) (prec : Nat) : Std.Format :=
  Universe.fmt [] u prec

instance : Repr Universe where
  reprPrec := Universe.reprPrec

instance : ToString Universe where
  toString u := (repr u).pretty

#guard toString (Universe.level 0 |>.succ.succ.succ.succ) == "u#0 + 4"
#guard (Universe.fmt [`u] (Universe.level 0 |>.succ.succ) 0).pretty == "u + 2"

def addOffset (u : Universe) : Nat → Universe
  | 0 => u
  | n + 1 => addOffset u.succ n

structure NF where
  constant : Nat
  levels : List (Nat × Nat)
  mvars : List (UMVarId × Nat)
deriving Repr, DecidableEq

namespace NF

def zero : NF := ⟨0, [], []⟩

def level (i : Nat) : NF := ⟨0, [(i, 0)], []⟩

def mvar (id : UMVarId) : NF := ⟨0, [], [(id, 0)]⟩

def maxOffset : List (Nat × Nat) → Nat
  | [] => 0
  | (_, k) :: rest => Nat.max k (maxOffset rest)

def succ : NF → NF
  | ⟨c, L, M⟩ => ⟨c + 1, L.map fun p => (p.1, p.2 + 1), M.map fun p => (p.1, p.2 + 1)⟩

def merge : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (i₁, k₁) :: xs, (i₂, k₂) :: ys =>
    if i₁ < i₂      then (i₁, k₁) :: merge xs ((i₂, k₂) :: ys)
    else if i₁ > i₂ then (i₂, k₂) :: merge ((i₁, k₁) :: xs) ys
    else                 (i₁, Nat.max k₁ k₂) :: merge xs ys

def maxOf : NF → NF → NF
  | ⟨c₁, L₁, M₁⟩, ⟨c₂, L₂, M₂⟩ => ⟨Nat.max c₁ c₂, merge L₁ L₂, merge M₁ M₂⟩

def ofUniverse : Universe → NF
  | .zero => zero
  | .level i => level i
  | .mvar id => mvar id
  | .succ u => succ (ofUniverse u)
  | .max u v => maxOf (ofUniverse u) (ofUniverse v)

def reifyLevels : Universe → List (Nat × Nat) → Universe :=
  List.foldl (fun acc (i, k) => Universe.max acc ((Universe.level i).addOffset k))

def reifyMVars : Universe → List (UMVarId × Nat) → Universe :=
  List.foldl (fun acc (id, k) => Universe.max acc ((Universe.mvar id).addOffset k))

def toUniverse : NF → Universe
  | ⟨0, [], []⟩ => Universe.zero
  | ⟨0, (i, k) :: rest, M⟩ =>
      reifyMVars (reifyLevels ((Universe.level i).addOffset k) rest) M
  | ⟨0, [], (id, k) :: rest⟩ =>
      reifyMVars ((Universe.mvar id).addOffset k) rest
  | ⟨c + 1, [], []⟩ =>
      Universe.zero.addOffset (c + 1)
  | ⟨c + 1, [], (id, k) :: rest⟩ =>
      let main := reifyMVars ((Universe.mvar id).addOffset k) rest
      if k ≥ c + 1 ∨ rest.any (fun (_, k') => decide (k' ≥ c + 1)) then main
      else main.max (Universe.zero.addOffset (c + 1))
  | ⟨c + 1, (i, k) :: rest, M⟩ =>
      let main := reifyMVars (reifyLevels ((Universe.level i).addOffset k) rest) M
      if k ≥ c + 1 ∨ rest.any (fun (_, k') => decide (k' ≥ c + 1))
          ∨ M.any (fun (_, k') => decide (k' ≥ c + 1)) then main
      else main.max (Universe.zero.addOffset (c + 1))

end NF

def normalise (u : Universe) : Universe := (NF.ofUniverse u).toUniverse

def mkSucc (u : Universe) : Universe :=
  normalise (.succ u)

def mkMax (u v : Universe) : Universe :=
  normalise (.max u v)

def checkLevels (numParams : Nat) : Universe → Except Nat Unit
  | .level i => do if i < numParams then return else throw i
  | .zero => do return
  | .mvar _ => do return
  | .succ u => do u.checkLevels numParams
  | .max u v => do u.checkLevels numParams; v.checkLevels numParams

def usedLevels : Universe → List Nat
  | .level i => [i]
  | .zero => []
  | .mvar _ => []
  | .succ u => u.usedLevels
  | .max u v => u.usedLevels ++ v.usedLevels

def hasMVar : Universe → Bool
  | .level _ => false
  | .zero => false
  | .mvar _ => true
  | .succ u => u.hasMVar
  | .max u v => u.hasMVar || v.hasMVar

def freeMVars : Universe → List UMVarId
  | .level _ => []
  | .zero => []
  | .mvar id => [id]
  | .succ u => u.freeMVars
  | .max u v => u.freeMVars ++ v.freeMVars

def substMVars (f : UMVarId → Option Universe) : Universe → Universe
  | .level i => .level i
  | .zero => .zero
  | .mvar id => (f id).getD (.mvar id)
  | .succ u => (u.substMVars f).mkSucc
  | .max u v => (u.substMVars f).mkMax (v.substMVars f)

def shift (k : Nat) : Universe → Universe
  | .level i => .level (i + k)
  | .zero => .zero
  | .mvar id => .mvar id
  | .succ u => .succ (u.shift k)
  | .max u v => .max (u.shift k) (v.shift k)

section Tests

open Universe

private abbrev u : Universe := .level 0
private abbrev v : Universe := .level 1

#guard normalise u == u
#guard normalise 0 == 0
#guard normalise (max u v) == max u v
#guard normalise (max v u) == max u v

end Tests

def Bounded (k : Nat) : Universe → Prop
  | .level i => i < k
  | .zero => True
  | .mvar _ => True
  | .succ u => u.Bounded k
  | .max u v => u.Bounded k ∧ v.Bounded k

theorem Bounded.addOffset {k : Nat} (n : Nat) :
    ∀ {u : Universe}, u.Bounded k → (u.addOffset n).Bounded k := by
  induction n with
  | zero => intro u h; exact h
  | succ n ih => intro u h; exact ih (u := u.succ) h

namespace NF

def Bounded (k : Nat) (nf : NF) : Prop :=
  ∀ p ∈ nf.levels, p.1 < k

theorem Bounded.zero {k : Nat} : NF.Bounded k NF.zero := by
  intro p hp; cases hp

theorem Bounded.level {k i : Nat} (h : i < k) : NF.Bounded k (NF.level i) := by
  intro p hp
  cases hp with
  | head => exact h
  | tail _ ht => cases ht

theorem Bounded.succ {k : Nat} {nf : NF} (h : NF.Bounded k nf) :
    NF.Bounded k (NF.succ nf) := by
  cases nf with
  | mk c L =>
    intro p hp
    show p.1 < k
    simp only [NF.succ, List.mem_map] at hp
    have ⟨p', hp', hpEq⟩ := hp
    rw [← hpEq]
    exact h p' hp'

private theorem Bounded.merge_aux {k : Nat} :
    ∀ (L₁ L₂ : List (Nat × Nat)),
    (∀ p ∈ L₁, p.1 < k) → (∀ p ∈ L₂, p.1 < k) →
    ∀ p ∈ NF.merge L₁ L₂, p.1 < k
  | [], _, _, h₂ => fun p hp => h₂ p (by simpa [NF.merge] using hp)
  | (i₁, k₁) :: _, [], h₁, _ => fun p hp =>
    h₁ p (by simpa [NF.merge] using hp)
  | (i₁, k₁) :: xs, (i₂, k₂) :: ys, h₁, h₂ => by
    intro p hp
    unfold NF.merge at hp
    split at hp
    next hLt =>
      cases hp with
      | head => exact h₁ (i₁, k₁) List.mem_cons_self
      | tail _ ht =>
        exact Bounded.merge_aux xs ((i₂, k₂) :: ys)
          (fun p hp => h₁ p (List.mem_cons_of_mem _ hp)) h₂ p ht
    next hNotLt =>
      split at hp
      next hGt =>
        cases hp with
        | head => exact h₂ (i₂, k₂) List.mem_cons_self
        | tail _ ht =>
          exact Bounded.merge_aux ((i₁, k₁) :: xs) ys h₁
            (fun p hp => h₂ p (List.mem_cons_of_mem _ hp)) p ht
      next hNotGt =>
        cases hp with
        | head => exact h₁ (i₁, k₁) List.mem_cons_self
        | tail _ ht =>
          exact Bounded.merge_aux xs ys
            (fun p hp => h₁ p (List.mem_cons_of_mem _ hp))
            (fun p hp => h₂ p (List.mem_cons_of_mem _ hp)) p ht

theorem Bounded.maxOf {k : Nat} : ∀ {nf₁ nf₂ : NF},
    NF.Bounded k nf₁ → NF.Bounded k nf₂ →
    NF.Bounded k (NF.maxOf nf₁ nf₂)
  | ⟨_, L₁, _⟩, ⟨_, L₂, _⟩, h₁, h₂ => Bounded.merge_aux L₁ L₂ h₁ h₂

theorem Bounded.ofUniverse {k : Nat} : ∀ {u : Universe},
    u.Bounded k → NF.Bounded k (NF.ofUniverse u)
  | .zero, _ => Bounded.zero
  | .level _, h => Bounded.level h
  | .mvar _, _ => by intro p hp; cases hp
  | .succ u, h => Bounded.succ (Bounded.ofUniverse (u := u) h)
  | .max _ _, ⟨hu, hv⟩ =>
    Bounded.maxOf (Bounded.ofUniverse hu) (Bounded.ofUniverse hv)

private theorem Bounded.reifyLevels_aux {k : Nat} {u : Universe}
    (hu : u.Bounded k) :
    ∀ (L : List (Nat × Nat)), (∀ p ∈ L, p.1 < k) →
    (NF.reifyLevels u L).Bounded k
  | [], _ => hu
  | (i, j) :: rest, hL => by
    unfold NF.reifyLevels
    simp only [List.foldl]
    apply Bounded.reifyLevels_aux
    · exact ⟨hu, Universe.Bounded.addOffset j
        (hL (i, j) List.mem_cons_self : Universe.Bounded k (Universe.level i))⟩
    · exact fun p hp => hL p (List.mem_cons_of_mem _ hp)

private theorem Bounded.reifyMVars_aux {k : Nat} {u : Universe}
    (hu : u.Bounded k) :
    ∀ (M : List (UMVarId × Nat)), (NF.reifyMVars u M).Bounded k
  | [] => hu
  | (_, j) :: rest => by
    unfold NF.reifyMVars
    simp only [List.foldl]
    apply Bounded.reifyMVars_aux
    exact ⟨hu, Universe.Bounded.addOffset j (show Universe.Bounded k (Universe.mvar _) from trivial)⟩

theorem Bounded.toUniverse {k : Nat} :
    ∀ {nf : NF}, NF.Bounded k nf → nf.toUniverse.Bounded k
  | ⟨0, [], []⟩, _ => trivial
  | ⟨0, (i, j) :: rest, M⟩, h => by
    have hi : Universe.Bounded k (Universe.level i) := h (i, j) List.mem_cons_self
    have hRest : ∀ p ∈ rest, p.1 < k :=
      fun p hp => h p (List.mem_cons_of_mem _ hp)
    exact Bounded.reifyMVars_aux
      (Bounded.reifyLevels_aux (Universe.Bounded.addOffset j hi) rest hRest) M
  | ⟨0, [], (_, j) :: rest⟩, _ => by
    exact Bounded.reifyMVars_aux
      (Universe.Bounded.addOffset j (show Universe.Bounded k (Universe.mvar _) from trivial)) rest
  | ⟨c + 1, [], []⟩, _ => by
    exact Universe.Bounded.addOffset (c + 1) (show Universe.Bounded k Universe.zero from trivial)
  | ⟨c + 1, [], (id, k') :: rest⟩, h => by
    have bMain : Universe.Bounded k
        (NF.reifyMVars ((Universe.mvar id).addOffset k') rest) :=
      Bounded.reifyMVars_aux
        (Universe.Bounded.addOffset k' (show Universe.Bounded k (Universe.mvar id) from trivial)) rest
    show Universe.Bounded k _
    simp only [NF.toUniverse]
    split
    · exact bMain
    · exact ⟨bMain,
        Universe.Bounded.addOffset (c + 1) (show Universe.Bounded k Universe.zero from trivial)⟩
  | ⟨c + 1, (i, j) :: rest, M⟩, h => by
    have hi : Universe.Bounded k (Universe.level i) := h (i, j) List.mem_cons_self
    have hRest : ∀ p ∈ rest, p.1 < k :=
      fun p hp => h p (List.mem_cons_of_mem _ hp)
    have bMain : Universe.Bounded k
        (NF.reifyMVars (NF.reifyLevels ((Universe.level i).addOffset j) rest) M) :=
      Bounded.reifyMVars_aux
        (Bounded.reifyLevels_aux (Universe.Bounded.addOffset j hi) rest hRest) M
    show Universe.Bounded k _
    simp only [NF.toUniverse]
    split
    · exact bMain
    · exact ⟨bMain,
        Universe.Bounded.addOffset (c + 1) (show Universe.Bounded k Universe.zero from trivial)⟩

end NF

theorem Bounded.normalise {k : Nat} {u : Universe} (h : u.Bounded k) :
    u.normalise.Bounded k :=
  NF.Bounded.toUniverse (NF.Bounded.ofUniverse h)

theorem mkSucc_bounded {k : Nat} {u : Universe} (h : u.Bounded k) :
    (Universe.mkSucc u).Bounded k :=
  Bounded.normalise (h : u.succ.Bounded k)

theorem mkMax_bounded {k : Nat} {u v : Universe}
    (hu : u.Bounded k) (hv : v.Bounded k) :
    (Universe.mkMax u v).Bounded k :=
  Bounded.normalise (⟨hu, hv⟩ : (u.max v).Bounded k)

end Universe

end Qdt
