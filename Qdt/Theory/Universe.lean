module

public import Lean.Data.Name
public import Init.Data.Ord
public import Init.Data.Order.Ord

@[expose] public section

namespace Qdt

open Lean (Name)

abbrev UMVarId := Nat

inductive Universe
  | param (n : Name)
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

protected def fmt (u : Universe) (prec : Nat) : Std.Format :=
  match u with
  | .zero => "0"
  | .param n => Std.Format.text n.toString
  | .mvar id => "?u#" ++ repr id
  | .succ u' =>
    let rec countSuccs (acc : Nat) : Universe → Nat × Std.Format
      | .succ u'' => countSuccs (acc + 1) u''
      | .zero => (acc + 1, repr (acc + 1))
      | base => (acc + 1, parenIf (prec > 10) (base.fmt 66 ++ " + " ++ repr (acc + 1)))
    (countSuccs 0 u').snd
  | .max u' v' =>
    parenIf (prec > 10) ("max " ++ u'.fmt 11 ++ " " ++ v'.fmt 11)

instance : Repr Universe where
  reprPrec := Universe.fmt

instance : ToString Universe where
  toString u := (repr u).pretty

#guard toString (Universe.param `u |>.succ.succ.succ.succ) == "u + 4"
#guard (Universe.fmt (Universe.param `u |>.succ.succ) 0).pretty == "u + 2"

def nameCmp : Name → Name → Ordering
  | .anonymous, .anonymous => .eq
  | .anonymous, _ => .lt
  | _, .anonymous => .gt
  | .num p₁ i₁, .num p₂ i₂ => match nameCmp p₁ p₂ with | .eq => compare i₁ i₂ | o => o
  | .num _ _, .str _ _ => .lt
  | .str _ _, .num _ _ => .gt
  | .str p₁ s₁, .str p₂ s₂ => match nameCmp p₁ p₂ with | .eq => compare s₁ s₂ | o => o

theorem nameCmp_eq : ∀ {n₁ n₂ : Name}, nameCmp n₁ n₂ = .eq → n₁ = n₂
  | .anonymous, .anonymous, _ => rfl
  | .str p₁ s₁, .str p₂ s₂, h => by
      simp only [nameCmp] at h
      split at h
      · next hp =>
          have := Std.LawfulEqOrd.eq_of_compare (α := String) h
          have := nameCmp_eq hp
          subst this; subst ‹s₁ = s₂›; rfl
      · next => exact absurd h (by simp_all)
  | .num p₁ i₁, .num p₂ i₂, h => by
      simp only [nameCmp] at h
      split at h
      · next hp =>
          have := Std.LawfulEqOrd.eq_of_compare (α := Nat) h
          have := nameCmp_eq hp
          subst this; subst ‹i₁ = i₂›; rfl
      · next => exact absurd h (by simp_all)
  | .anonymous, .str _ _, h => by simp [nameCmp] at h
  | .anonymous, .num _ _, h => by simp [nameCmp] at h
  | .str _ _, .anonymous, h => by simp [nameCmp] at h
  | .num _ _, .anonymous, h => by simp [nameCmp] at h
  | .str _ _, .num _ _, h => by simp [nameCmp] at h
  | .num _ _, .str _ _, h => by simp [nameCmp] at h

def addOffset (u : Universe) : Nat → Universe
  | 0 => u
  | n + 1 => addOffset u.succ n

structure NF where
  constant : Nat
  params : List (Name × Nat)
  mvars : List (UMVarId × Nat)
deriving Repr, DecidableEq

namespace NF

def zero : NF := ⟨0, [], []⟩

def param (n : Name) : NF := ⟨0, [(n, 0)], []⟩

def mvar (id : UMVarId) : NF := ⟨0, [], [(id, 0)]⟩

def maxOffset : List (Name × Nat) → Nat
  | [] => 0
  | (_, k) :: rest => Nat.max k (maxOffset rest)

def succ : NF → NF
  | ⟨c, L, M⟩ => ⟨c + 1, L.map fun p => (p.1, p.2 + 1), M.map fun p => (p.1, p.2 + 1)⟩

def merge : List (Name × Nat) → List (Name × Nat) → List (Name × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (n₁, k₁) :: xs, (n₂, k₂) :: ys =>
    match nameCmp n₁ n₂ with
    | .lt => (n₁, k₁) :: merge xs ((n₂, k₂) :: ys)
    | .gt => (n₂, k₂) :: merge ((n₁, k₁) :: xs) ys
    | .eq => (n₁, Nat.max k₁ k₂) :: merge xs ys

def mergeMVars : List (UMVarId × Nat) → List (UMVarId × Nat) → List (UMVarId × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (i₁, k₁) :: xs, (i₂, k₂) :: ys =>
    match compare i₁ i₂ with
    | .lt => (i₁, k₁) :: mergeMVars xs ((i₂, k₂) :: ys)
    | .gt => (i₂, k₂) :: mergeMVars ((i₁, k₁) :: xs) ys
    | .eq => (i₁, Nat.max k₁ k₂) :: mergeMVars xs ys

def maxOf : NF → NF → NF
  | ⟨c₁, L₁, M₁⟩, ⟨c₂, L₂, M₂⟩ => ⟨Nat.max c₁ c₂, merge L₁ L₂, mergeMVars M₁ M₂⟩

def ofUniverse : Universe → NF
  | .zero => zero
  | .param n => param n
  | .mvar id => mvar id
  | .succ u => succ (ofUniverse u)
  | .max u v => maxOf (ofUniverse u) (ofUniverse v)

def reifyParams : Universe → List (Name × Nat) → Universe :=
  List.foldl (fun acc (n, k) => Universe.max acc ((Universe.param n).addOffset k))

def reifyMVars : Universe → List (UMVarId × Nat) → Universe :=
  List.foldl (fun acc (id, k) => Universe.max acc ((Universe.mvar id).addOffset k))

def toUniverse : NF → Universe
  | ⟨0, [], []⟩ => Universe.zero
  | ⟨0, (n, k) :: rest, M⟩ =>
      reifyMVars (reifyParams ((Universe.param n).addOffset k) rest) M
  | ⟨0, [], (id, k) :: rest⟩ =>
      reifyMVars ((Universe.mvar id).addOffset k) rest
  | ⟨c + 1, [], []⟩ =>
      Universe.zero.addOffset (c + 1)
  | ⟨c + 1, [], (id, k) :: rest⟩ =>
      let main := reifyMVars ((Universe.mvar id).addOffset k) rest
      if k ≥ c + 1 ∨ rest.any (fun (_, k') => decide (k' ≥ c + 1)) then main
      else main.max (Universe.zero.addOffset (c + 1))
  | ⟨c + 1, (n, k) :: rest, M⟩ =>
      let main := reifyMVars (reifyParams ((Universe.param n).addOffset k) rest) M
      if k ≥ c + 1 ∨ rest.any (fun (_, k') => decide (k' ≥ c + 1))
          ∨ M.any (fun (_, k') => decide (k' ≥ c + 1)) then main
      else main.max (Universe.zero.addOffset (c + 1))

end NF

def normalise (u : Universe) : Universe := (NF.ofUniverse u).toUniverse

def mkSucc (u : Universe) : Universe :=
  normalise (.succ u)

def mkMax (u v : Universe) : Universe :=
  normalise (.max u v)

def checkParams (params : List Name) : Universe → Except Name Unit
  | .param n => do if n ∈ params then return else throw n
  | .zero => do return
  | .mvar _ => do return
  | .succ u => do u.checkParams params
  | .max u v => do u.checkParams params; v.checkParams params

def usedParams : Universe → List Name
  | .param n => [n]
  | .zero => []
  | .mvar _ => []
  | .succ u => u.usedParams
  | .max u v => u.usedParams ++ v.usedParams

def hasMVar : Universe → Bool
  | .param _ => false
  | .zero => false
  | .mvar _ => true
  | .succ u => u.hasMVar
  | .max u v => u.hasMVar || v.hasMVar

def freeMVars : Universe → List UMVarId
  | .param _ => []
  | .zero => []
  | .mvar id => [id]
  | .succ u => u.freeMVars
  | .max u v => u.freeMVars ++ v.freeMVars

def substMVars (f : UMVarId → Option Universe) : Universe → Universe
  | .param n => .param n
  | .zero => .zero
  | .mvar id => (f id).getD (.mvar id)
  | .succ u => (u.substMVars f).mkSucc
  | .max u v => (u.substMVars f).mkMax (v.substMVars f)

@[specialize] def subst (σ : Name → Option Universe) : Universe → Universe
  | .param n =>
    match σ n with
    | some u => u
    | none => panic! s!"Universe.subst: param {n} not in substitution"
  | .zero => .zero
  | .mvar id => .mvar id
  | .succ u => (u.subst σ).mkSucc
  | .max u v => (u.subst σ).mkMax (v.subst σ)

def getParamSubst : List Name → List Universe → Name → Option Universe
  | p :: ps, u :: us, p' => if p == p' then some u else getParamSubst ps us p'
  | _, _, _ => none

def instantiateParams (u : Universe) (paramNames : List Name) (vs : List Universe) : Universe :=
  u.subst (getParamSubst paramNames vs)

section Tests

open Universe

private abbrev u : Universe := .param `u
private abbrev v : Universe := .param `v

#guard normalise u == u
#guard normalise 0 == 0
#guard normalise (max u v) == max u v
#guard normalise (max v u) == max u v

end Tests

def Bounded (Γ : List Name) : Universe → Prop
  | .param n => n ∈ Γ
  | .zero => True
  | .mvar _ => True
  | .succ u => u.Bounded Γ
  | .max u v => u.Bounded Γ ∧ v.Bounded Γ

theorem Bounded.addOffset {Γ : List Name} (n : Nat) :
    ∀ {u : Universe}, u.Bounded Γ → (u.addOffset n).Bounded Γ := by
  induction n with
  | zero => intro u h; exact h
  | succ n ih => intro u h; exact ih (u := u.succ) h

namespace NF

def Bounded (Γ : List Name) (nf : NF) : Prop :=
  ∀ p ∈ nf.params, p.1 ∈ Γ

theorem Bounded.zero {Γ : List Name} : NF.Bounded Γ NF.zero := by
  intro p hp; cases hp

theorem Bounded.param {Γ : List Name} {n : Name} (h : n ∈ Γ) : NF.Bounded Γ (NF.param n) := by
  intro p hp
  cases hp with
  | head => exact h
  | tail _ ht => cases ht

theorem Bounded.succ {Γ : List Name} {nf : NF} (h : NF.Bounded Γ nf) :
    NF.Bounded Γ (NF.succ nf) := by
  cases nf with
  | mk c L =>
    intro p hp
    show p.1 ∈ Γ
    simp only [NF.succ, List.mem_map] at hp
    have ⟨p', hp', hpEq⟩ := hp
    rw [← hpEq]
    exact h p' hp'

private theorem Bounded.merge_aux {Γ : List Name} :
    ∀ (L₁ L₂ : List (Name × Nat)),
    (∀ p ∈ L₁, p.1 ∈ Γ) → (∀ p ∈ L₂, p.1 ∈ Γ) →
    ∀ p ∈ NF.merge L₁ L₂, p.1 ∈ Γ
  | [], _, _, h₂ => fun p hp => h₂ p (by simpa [NF.merge] using hp)
  | (n₁, k₁) :: _, [], h₁, _ => fun p hp =>
    h₁ p (by simpa [NF.merge] using hp)
  | (n₁, k₁) :: xs, (n₂, k₂) :: ys, h₁, h₂ => by
    intro p hp
    unfold NF.merge at hp
    split at hp
    next =>
      cases hp with
      | head => exact h₁ (n₁, k₁) List.mem_cons_self
      | tail _ ht =>
        exact Bounded.merge_aux xs ((n₂, k₂) :: ys)
          (fun p hp => h₁ p (List.mem_cons_of_mem _ hp)) h₂ p ht
    next =>
      cases hp with
      | head => exact h₂ (n₂, k₂) List.mem_cons_self
      | tail _ ht =>
        exact Bounded.merge_aux ((n₁, k₁) :: xs) ys h₁
          (fun p hp => h₂ p (List.mem_cons_of_mem _ hp)) p ht
    next =>
      cases hp with
      | head => exact h₁ (n₁, k₁) List.mem_cons_self
      | tail _ ht =>
        exact Bounded.merge_aux xs ys
          (fun p hp => h₁ p (List.mem_cons_of_mem _ hp))
          (fun p hp => h₂ p (List.mem_cons_of_mem _ hp)) p ht

theorem Bounded.maxOf {Γ : List Name} : ∀ {nf₁ nf₂ : NF},
    NF.Bounded Γ nf₁ → NF.Bounded Γ nf₂ →
    NF.Bounded Γ (NF.maxOf nf₁ nf₂)
  | ⟨_, L₁, _⟩, ⟨_, L₂, _⟩, h₁, h₂ => Bounded.merge_aux L₁ L₂ h₁ h₂

theorem Bounded.ofUniverse {Γ : List Name} : ∀ {u : Universe},
    u.Bounded Γ → NF.Bounded Γ (NF.ofUniverse u)
  | .zero, _ => Bounded.zero
  | .param _, h => Bounded.param h
  | .mvar _, _ => by intro p hp; cases hp
  | .succ u, h => Bounded.succ (Bounded.ofUniverse (u := u) h)
  | .max _ _, ⟨hu, hv⟩ =>
    Bounded.maxOf (Bounded.ofUniverse hu) (Bounded.ofUniverse hv)

private theorem Bounded.reifyParams_aux {Γ : List Name} {u : Universe}
    (hu : u.Bounded Γ) :
    ∀ (L : List (Name × Nat)), (∀ p ∈ L, p.1 ∈ Γ) →
    (NF.reifyParams u L).Bounded Γ
  | [], _ => hu
  | (n, j) :: rest, hL => by
    unfold NF.reifyParams
    simp only [List.foldl]
    apply Bounded.reifyParams_aux
    · exact ⟨hu, Universe.Bounded.addOffset j
        (hL (n, j) List.mem_cons_self : Universe.Bounded Γ (Universe.param n))⟩
    · exact fun p hp => hL p (List.mem_cons_of_mem _ hp)

private theorem Bounded.reifyMVars_aux {Γ : List Name} {u : Universe}
    (hu : u.Bounded Γ) :
    ∀ (M : List (UMVarId × Nat)), (NF.reifyMVars u M).Bounded Γ
  | [] => hu
  | (_, j) :: rest => by
    unfold NF.reifyMVars
    simp only [List.foldl]
    apply Bounded.reifyMVars_aux
    exact ⟨hu, Universe.Bounded.addOffset j (show Universe.Bounded Γ (Universe.mvar _) from trivial)⟩

theorem Bounded.toUniverse {Γ : List Name} :
    ∀ {nf : NF}, NF.Bounded Γ nf → nf.toUniverse.Bounded Γ
  | ⟨0, [], []⟩, _ => trivial
  | ⟨0, (n, j) :: rest, M⟩, h => by
    have hn : Universe.Bounded Γ (Universe.param n) := h (n, j) List.mem_cons_self
    have hRest : ∀ p ∈ rest, p.1 ∈ Γ :=
      fun p hp => h p (List.mem_cons_of_mem _ hp)
    exact Bounded.reifyMVars_aux
      (Bounded.reifyParams_aux (Universe.Bounded.addOffset j hn) rest hRest) M
  | ⟨0, [], (_, j) :: rest⟩, _ => by
    exact Bounded.reifyMVars_aux
      (Universe.Bounded.addOffset j (show Universe.Bounded Γ (Universe.mvar _) from trivial)) rest
  | ⟨c + 1, [], []⟩, _ => by
    exact Universe.Bounded.addOffset (c + 1) (show Universe.Bounded Γ Universe.zero from trivial)
  | ⟨c + 1, [], (id, k') :: rest⟩, h => by
    have bMain : Universe.Bounded Γ
        (NF.reifyMVars ((Universe.mvar id).addOffset k') rest) :=
      Bounded.reifyMVars_aux
        (Universe.Bounded.addOffset k' (show Universe.Bounded Γ (Universe.mvar id) from trivial)) rest
    show Universe.Bounded Γ _
    simp only [NF.toUniverse]
    split
    · exact bMain
    · exact ⟨bMain,
        Universe.Bounded.addOffset (c + 1) (show Universe.Bounded Γ Universe.zero from trivial)⟩
  | ⟨c + 1, (n, j) :: rest, M⟩, h => by
    have hn : Universe.Bounded Γ (Universe.param n) := h (n, j) List.mem_cons_self
    have hRest : ∀ p ∈ rest, p.1 ∈ Γ :=
      fun p hp => h p (List.mem_cons_of_mem _ hp)
    have bMain : Universe.Bounded Γ
        (NF.reifyMVars (NF.reifyParams ((Universe.param n).addOffset j) rest) M) :=
      Bounded.reifyMVars_aux
        (Bounded.reifyParams_aux (Universe.Bounded.addOffset j hn) rest hRest) M
    show Universe.Bounded Γ _
    simp only [NF.toUniverse]
    split
    · exact bMain
    · exact ⟨bMain,
        Universe.Bounded.addOffset (c + 1) (show Universe.Bounded Γ Universe.zero from trivial)⟩

end NF

theorem Bounded.normalise {Γ : List Name} {u : Universe} (h : u.Bounded Γ) :
    u.normalise.Bounded Γ :=
  NF.Bounded.toUniverse (NF.Bounded.ofUniverse h)

theorem mkSucc_bounded {Γ : List Name} {u : Universe} (h : u.Bounded Γ) :
    (Universe.mkSucc u).Bounded Γ :=
  Bounded.normalise (h : u.succ.Bounded Γ)

theorem mkMax_bounded {Γ : List Name} {u v : Universe}
    (hu : u.Bounded Γ) (hv : v.Bounded Γ) :
    (Universe.mkMax u v).Bounded Γ :=
  Bounded.normalise (⟨hu, hv⟩ : (u.max v).Bounded Γ)

end Universe

end Qdt
