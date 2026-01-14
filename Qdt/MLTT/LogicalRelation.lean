import Qdt.MLTT.Declarative

/-!
# Logical Relation for MLTT

This module defines a Kripke-style logical relation for MLTT with:
- Tarski-style universes (𝑢 and El)
- Pi types
- Constants (treated as neutral)

## Design Notes

Compared to the Coq mltt-coq formalization:
- We use Tarski universes (`𝑢` + `El`) instead of Russell universes
- We have constants (`Tm.const`) which are treated as neutral
- We use separate mutual inductives for judgements (Ctx.WF, Ty.WF, Tm.HasType, Ty.Eq, Tm.Eq)
- We don't have built-in Nat/Sigma/Empty - these would be general inductives

## Judgement Forms

| Notation           | Name         | Description                                 |
|--------------------|--------------|---------------------------------------------|
| `Γ ⊢`              | Ctx.WF       | Context well-formed (declarative)           |
| `Γ ⊢ A type`       | Ty.WF        | Type well-formed (declarative)              |
| `Γ ⊢ t : A`        | Tm.HasType   | Term has type (declarative)                 |
| `Γ ⊢ A ≡ B type`   | Ty.Eq        | Types are convertible (declarative)         |
| `Γ ⊢ t ≡ u : A`    | Tm.Eq        | Terms are convertible (declarative)         |
| `[ t ⤳ u ]`        | Tm.OneRed    | One-step weak-head reduction (untyped)      |
| `[ t ⤳* u ]`       | Tm.RedClosure| Multi-step weak-head reduction (untyped)    |
| `Γ ⊩ A ⤳* B type`  | Ty.Red       | Type weak-head reduces (algorithmic)        |
| `Γ ⊩ t ⤳* u : A`   | Tm.Red       | Term weak-head reduces (algorithmic)        |
| `Γ ⊩ n ~ n' : A`   | Neutral.Eq   | Neutral terms are convertible (algorithmic) |
-/

namespace Qdt

open Lean (Name)

/-! ## Untyped Reduction

These reductions do not depend on context or typing — they are purely syntactic.
-/

section UntypedReduction

set_option hygiene false

notation:50 t " ⤳ " u  => Tm.OneRed t u
notation:50 A " ⤳ " B " type" => Ty.OneRed A B

/-- One-step weak-head reduction for terms (untyped) -/
inductive Tm.OneRed {n} : Tm n → Tm n → Prop where
  | beta {x A b a} :
      (Tm.lam ⟨x, A⟩ b).app a ⤳ b[a]
  | zeta {x A e b} :
      (Tm.letE x A e b ⤳ b[e])
  | app {f f' a} :
      (f ⤳ f') →
      (f.app a ⤳ f'.app a)

/-- Multi-step weak-head reduction for terms (reflexive-transitive closure, untyped) -/
abbrev Tm.Reds {n} := Relation.ReflTransGen (α := Tm n) Tm.OneRed

notation:50 t " ⤳* " u  => Tm.Reds t u

/-- One-step weak-head reduction for types (untyped) -/
inductive Ty.OneRed {n} : Ty n → Ty n → Prop where
  | el {t t'} :
      (t ⤳ t') →
      (.el t ⤳ .el t' type)

/-- Multi-step weak-head reduction for types (reflexive-transitive closure, untyped) -/
abbrev Ty.Reds {n} := Relation.ReflTransGen (α := Ty n) Ty.OneRed

notation:50 A " ⤳* " B " type" => Ty.Reds A B

theorem Tm.Reds.app {n} {f f' a : Tm n} :
    (f ⤳* f') →
    (f.app a ⤳* f'.app a) :=
  Relation.ReflTransGen.lift (Tm.app · a) fun _ _ => Tm.OneRed.app

theorem Ty.Reds.el {n} {t t' : Tm n} :
    (t ⤳* t') →
    (.el t ⤳* .el t' type) :=
  Relation.ReflTransGen.lift Ty.el fun _ _ => Ty.OneRed.el

end UntypedReduction

/-! ## Syntactic Predicates -/

/-- A term is neutral (stuck on a variable or constant) -/
inductive Tm.IsNeutral {n} : Tm n → Prop where
  | var {i : Idx n} : Tm.IsNeutral (.var i)
  | const {c : Name} : Tm.IsNeutral (.const c)
  | app {f a : Tm n} : Tm.IsNeutral f → Tm.IsNeutral (.app f a)
  | proj {i : Nat} {t : Tm n} : Tm.IsNeutral t → Tm.IsNeutral (.proj i t)

/-- A type is neutral (El of a neutral term) -/
inductive Ty.IsNeutral {n} : Ty n → Prop where
  | el {t : Tm n} : Tm.IsNeutral t → Ty.IsNeutral (.el t)

/-- A term is in weak head normal form -/
inductive Tm.IsWhnf {n} : Tm n → Prop where
  | lam {p : Param n} {b : Tm (n + 1)} : Tm.IsWhnf (.lam p b)
  | pi' {x : Name} {a : Tm n} {b : Tm (n + 1)} : Tm.IsWhnf (.pi' x a b)
  | neutral {t : Tm n} : Tm.IsNeutral t → Tm.IsWhnf t

/-- A type is in weak head normal form -/
inductive Ty.IsWhnf {n} : Ty n → Prop where
  | u : Ty.IsWhnf .u
  | pi {p : Param n} {B : Ty (n + 1)} : Ty.IsWhnf (.pi p B)
  | el {t : Tm n} : Tm.IsWhnf t → Ty.IsWhnf (.el t)

/-- A term that can be a type code in the universe -/
inductive Tm.IsType {n} : Tm n → Prop where
  | pi' {x : Name} {a : Tm n} {b : Tm (n + 1)} : Tm.IsType (.pi' x a b)
  | neutral {t : Tm n} : Tm.IsNeutral t → Tm.IsType t

/-! ## Algorithmic Judgements -/

section AlgorithmicJudgements

set_option hygiene false

notation:50 Γ " ⊩ " A " ⤳* " B " type" => Ty.Red Γ A B
notation:50 Γ " ⊩ " t " ⤳* " u " : " A => Tm.Red Γ t u A

mutual

/-- Type weak-head multi-step reduction -/
inductive Ty.Red {n} : Ctx 0 n → Ty n → Ty n → Prop where
  | refl {Γ A} :
      (Γ ⊢ A type) →
      (Γ ⊩ A ⤳* A type)
  | trans {Γ A B C} :
      (Γ ⊩ A ⤳* B type) →
      (Γ ⊩ B ⤳* C type) →
      (Γ ⊩ A ⤳* C type)
  | el_step {Γ} {t u : Tm n} :
      (Γ ⊩ t ⤳* u : 𝑢) →
      (Γ ⊩ .el t ⤳* .el u type)

/-- Term weak-head multi-step reduction -/
inductive Tm.Red {n} : Ctx 0 n → Tm n → Tm n → Ty n → Prop where
  | refl {Γ t A} :
      (Γ ⊢ t : A) →
      (Γ ⊩ t ⤳* t : A)
  | trans {Γ t u v A} :
      (Γ ⊩ t ⤳* u : A) →
      (Γ ⊩ u ⤳* v : A) →
      (Γ ⊩ t ⤳* v : A)
  | beta {Γ x A B a b} :
      (Γ.snoc ⟨x, A⟩ ⊢ b : B) →
      (Γ ⊢ a : A) →
      (Γ ⊩ (Tm.lam ⟨x, A⟩ b).app a ⤳* b[a] : B[a])
  | app_cong {Γ f f' a x A B} :
      (Γ ⊩ f ⤳* f' : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a : A) →
      (Γ ⊩ f.app a ⤳* f'.app a : B[a])

end

notation:50 Γ " ⊩ " n " ~ " n' " : " A => Neutral.Eq Γ n n' A

/-- Definitional equality of neutral terms -/
inductive Neutral.Eq {n} : Ctx 0 n → Tm n → Tm n → Ty n → Prop where
  | var {Γ i} :
      (Γ ⊢) →
      (Γ ⊩ .var i ~ .var i : Γ.get i)
  | const {Γ c} :
      (Γ ⊢) →
      (Γ ⊩ .const c ~ .const c : 𝑢) -- TODO: proper constant typing
  | app {Γ f f' a a' x A B} :
      (Γ ⊩ f ~ f' : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a ≡ a' : A) →
      (Γ ⊩ f.app a ~ f'.app a' : B[a])
  | proj {Γ i t t' A} :
      (Γ ⊩ t ~ t' : A) →
      (Γ ⊩ .proj i t ~ .proj i t' : 𝑢) -- TODO: proper projection typing

end AlgorithmicJudgements

/-! ## Bundled Reduction Judgements -/

/-- Type reduction to weak head normal form: `Γ ⊩ A ↘ B type` -/
structure Ty.Red.Whnf {n} (Γ : Ctx 0 n) (A B : Ty n) : Prop where
  red : Γ ⊩ A ⤳* B type
  whnf : B.IsWhnf
notation:50 Γ " ⊩ " A " ↘ " B " type" => Ty.Red.Whnf Γ A B

/-- Term reduction to weak head normal form: `Γ ⊩ t ↘ u : A` -/
structure Tm.Red.Whnf {n} (Γ : Ctx 0 n) (t u : Tm n) (A : Ty n) : Prop where
  red : Γ ⊩ t ⤳* u : A
  whnf : u.IsWhnf
notation:50 Γ " ⊩ " t " ↘ " u " : " A => Tm.Red.Whnf Γ t u A

/-- Type reduction with well-formedness: `Γ ⊩ A :⤳*: B type` -/
structure Ty.Red.Wf {n} (Γ : Ctx 0 n) (A B : Ty n) : Prop where
  red : Γ ⊩ A ⤳* B type
  wf : Γ ⊢ B type
notation:50 Γ " ⊩ " A " :⤳*: " B " type" => Ty.Red.Wf Γ A B

/-- Term reduction with well-typedness: `Γ ⊩ t :⤳*: u : A` -/
structure Tm.Red.Wf {n} (Γ : Ctx 0 n) (t u : Tm n) (A : Ty n) : Prop where
  red : Γ ⊩ t ⤳* u : A
  wf : Γ ⊢ u : A
notation:50 Γ " ⊩ " t " :⤳*: " u " : " A => Tm.Red.Wf Γ t u A

/-! ## Weakenings (Kripke Worlds) -/

/-- Well-typed weakenings between contexts -/
inductive Ctx.Wk : {m n : Nat} → Ctx 0 m → Ctx 0 n → Type where
  | id {n} {Γ : Ctx 0 n} : Ctx.Wk Γ Γ
  | step {m n} {Γ : Ctx 0 m} {Δ : Ctx 0 n} {x : Name} {A : Ty n} :
      Ctx.Wk Δ Γ → Ctx.Wk (Δ.snoc ⟨x, A⟩) Γ
  | lift {m n} {Γ : Ctx 0 m} {Δ : Ctx 0 n} {x : Name} {A : Ty m} {B : Ty n} :
      Ctx.Wk Δ Γ → Ctx.Wk (Δ.snoc ⟨x, B⟩) (Γ.snoc ⟨x, A⟩)

def Ctx.Wk.toSubst {m n} {Δ : Ctx 0 n} {Γ : Ctx 0 m} : Ctx.Wk Δ Γ → Subst m n
  | .id => Subst.id n
  | .step ρ => ρ.toSubst.comp Subst.shift
  | .lift ρ => ρ.toSubst.up

def Ty.wk {m n} {Δ : Ctx 0 n} {Γ : Ctx 0 m} (ρ : Ctx.Wk Δ Γ) (A : Ty m) : Ty n :=
  A.subst ρ.toSubst

def Tm.wk {m n} {Δ : Ctx 0 n} {Γ : Ctx 0 m} (ρ : Ctx.Wk Δ Γ) (t : Tm m) : Tm n :=
  t.subst ρ.toSubst

def Ctx.Wk.comp {l m n} {Γ₁ : Ctx 0 l} {Γ₂ : Ctx 0 m} {Γ₃ : Ctx 0 n} :
    Ctx.Wk Γ₁ Γ₂ → Ctx.Wk Γ₂ Γ₃ → Ctx.Wk Γ₁ Γ₃
  | ρ, .id => ρ
  | .id, σ => σ
  | .step ρ, σ => .step (ρ.comp σ)
  | .lift ρ, .step σ => .step (ρ.comp σ)
  | .lift ρ, .lift σ => .lift (ρ.comp σ)
infixl:70 " ∘w " => Ctx.Wk.comp

/-! ## Reducibility Relations -/

/-- The type of reducibility relations (using Prop predicates) -/
def RedRel : Type 1 :=
  ∀ {n : Nat}, (Γ : Ctx 0 n) → (A : Ty n) →
  (eqTy : Ty n → Type) →
  (redTm : Tm n → Type) →
  (eqTm : Tm n → Tm n → Type) →
  Prop

/-! ## LRPack - Bundled Reducibility Data -/

structure LR.Pack {n} (Γ : Ctx 0 n) (A : Ty n) : Type 1 where
  eqTy : Ty n → Type
  redTm : Tm n → Type
  eqTm : Tm n → Tm n → Type

structure LR.Adequate {n} (Γ : Ctx 0 n) (A : Ty n) (R : RedRel) : Type 1 extends LR.Pack Γ A where
  adequate : R Γ A eqTy redTm eqTm
notation:50 R " | " Γ " ⊩ " A => LR.Adequate Γ A R

private def LR.Adequate.notation {n} (R : RedRel) (Γ : Ctx 0 n) (A B : Ty n) (RA : LR.Adequate Γ A R) : Type :=
  RA.toPack.eqTy B
notation:50 R " | " Γ " ⊩ " A " ≡ " B " | " RA => LR.Adequate.notation R Γ A B RA

/-! ## Reducibility of Neutral Types

For Tarski universes, a neutral type is `El(n)` where `n : 𝑢` is neutral.
Unlike Russell universes, we cannot write `ty ~ ty : U` because `ty` is a type, not a term.
Instead, we require `ty.IsNeutral` (syntactically neutral).
-/

/-- A type is reducibly neutral: reduces to a neutral whnf -/
structure NeRedTy {n} (Γ : Ctx 0 n) (A : Ty n) : Type where
  ty : Ty n
  red : Γ ⊩ A :⤳*: ty type
  neu : ty.IsNeutral

/-- Two types are equal in the neutral reducibility -/
def NeRedTyEq {n} (Γ : Ctx 0 n) (A B : Ty n) (neA : NeRedTy Γ A) : Prop :=
  ∃ ty, (Γ ⊩ B :⤳*: ty type) ∧ (Γ ⊢ neA.ty ≡ ty type)

/-- A term is reducible at a neutral type -/
def NeRedTm {n} (Γ : Ctx 0 n) (t : Tm n) (A : Ty n) (neA : NeRedTy Γ A) : Prop :=
  ∃ te, (Γ ⊩ t :⤳*: te : neA.ty) ∧ (Γ ⊩ te ~ te : neA.ty)

/-- Two terms are equal in the neutral reducibility -/
def NeRedTmEq {n} (Γ : Ctx 0 n) (t u : Tm n) (A : Ty n) (neA : NeRedTy Γ A) : Prop :=
  ∃ teL teR, (Γ ⊩ t :⤳*: teL : neA.ty) ∧ (Γ ⊩ u :⤳*: teR : neA.ty) ∧ (Γ ⊩ teL ~ teR : neA.ty)

/-! ## Reducibility of the Universe (Tarski Style) -/

/-- A type reduces to the universe -/
structure URedTy {n} (Γ : Ctx 0 n) (A : Ty n) : Prop where
  red : Γ ⊩ A :⤳*: 𝑢 type
  wfCtx : Γ ⊢

/-- Type equality at the universe -/
def URedTyEq {n} (Γ : Ctx 0 n) (B : Ty n) : Prop :=
  Γ ⊩ B :⤳*: 𝑢 type

/-- A term is reducible at the universe (must be a type code) -/
def URedTm {n} (Γ : Ctx 0 n) (t : Tm n) (A : Ty n) (UA : URedTy Γ A) (rec : RedRel) : Prop :=
  ∃ te, (Γ ⊩ t :⤳*: te : 𝑢) ∧ te.IsType ∧ (Γ ⊢ te ≡ te : 𝑢) ∧ (∃ P : LRAdequate Γ (.el t) rec, True)

/-- Two terms are equal in the universe reducibility -/
def URedTmEq {n} (Γ : Ctx 0 n) (t u : Tm n) (A : Ty n) (UA : URedTy Γ A) (rec : RedRel) : Prop :=
  ∃ teL teR,
    (Γ ⊩ t :⤳*: teL : 𝑢) ∧ teL.IsType ∧ (Γ ⊢ teL ≡ teL : 𝑢) ∧
    (Γ ⊩ u :⤳*: teR : 𝑢) ∧ teR.IsType ∧ (Γ ⊢ teR ≡ teR : 𝑢) ∧
    (Γ ⊢ teL ≡ teR : 𝑢) ∧
    (∃ PL : LRAdequate Γ (.el t) rec, ∃ PR : LRAdequate Γ (.el u) rec, PL.pack.eqTy (.el u))

/-! ## Reducibility of Pi Types (Kripke Style) -/

/-- Domain and codomain reducibility for Pi types -/
structure PolyRedPack {n} (Γ : Ctx 0 n) (dom : Ty n) (cod : Ty (n + 1)) : Type where
  domTy : Γ ⊢ dom type
  codTy : Γ.snoc ⟨.anonymous, dom⟩ ⊢ cod type
  domRed {m} {Δ : Ctx 0 m} :
      (ρ : Ctx.Wk Δ Γ) → (Δ ⊢) → LRPack Δ (dom.wk ρ)
  codRed {m} {Δ : Ctx 0 m} {a : Tm m} :
      (ρ : Ctx.Wk Δ Γ) → (h : Δ ⊢) → (domRed ρ h).redTm a → LRPack Δ (cod.subst (a .: ρ.toSubst))
  posExt {m} {Δ : Ctx 0 m} {a b : Tm m} :
      (ρ : Ctx.Wk Δ Γ) → (h : Δ ⊢) → (ha : (domRed ρ h).redTm a) →
      (domRed ρ h).redTm b → (domRed ρ h).eqTm a b →
      (codRed ρ h ha).eqTy (cod.subst (b .: ρ.toSubst))

/-- Adequacy of PolyRedPack wrt a RedRel -/
structure PolyRedPackAdequate {n} {Γ : Ctx 0 n} {dom : Ty n} {cod : Ty (n + 1)}
    (R : RedRel) (PA : PolyRedPack Γ dom cod) : Prop where
  domAd {m} {Δ : Ctx 0 m} (ρ : Ctx.Wk Δ Γ) (h : Δ ⊢) :
      (PA.domRed ρ h).Adequate R
  codAd {m} {Δ : Ctx 0 m} {a : Tm m} (ρ : Ctx.Wk Δ Γ) (h : Δ ⊢)
      (ha : (PA.domRed ρ h).redTm a) :
      (PA.codRed ρ h ha).Adequate R

/-- A type reduces to a Pi type -/
structure PiRedTy {n} (Γ : Ctx 0 n) (A : Ty n) : Type where
  dom : Ty n
  cod : Ty (n + 1)
  red : Γ ⊩ A :⤳*: .pi ⟨.anonymous, dom⟩ cod type
  eq : Γ ⊢ .pi ⟨.anonymous, dom⟩ cod ≡ .pi ⟨.anonymous, dom⟩ cod type
  polyRed : PolyRedPack Γ dom cod

/-- Adequacy of PiRedTy -/
def PiRedTyAdequate {n} {Γ : Ctx 0 n} {A : Ty n}
    (R : RedRel) (piA : PiRedTy Γ A) : Prop :=
  PolyRedPackAdequate R piA.polyRed

/-- Two types are equal in the Pi reducibility -/
def PiRedTyEq {n} (Γ : Ctx 0 n) (A B : Ty n) (piA : PiRedTy Γ A) : Prop :=
  ∃ dom cod,
    (Γ ⊩ B :⤳*: .pi ⟨.anonymous, dom⟩ cod type) ∧
    (Γ ⊢ piA.dom ≡ dom type) ∧
    (Γ.snoc ⟨.anonymous, piA.dom⟩ ⊢ piA.cod ≡ cod type)

/-- A term is reducible at a Pi type -/
def PiRedTm {n} (Γ : Ctx 0 n) (t : Tm n) (A : Ty n) (piA : PiRedTy Γ A) : Prop :=
  ∃ nf,
    (Γ ⊩ t ↘ nf : .pi ⟨.anonymous, piA.dom⟩ piA.cod) ∧
    (Γ ⊢ nf ≡ nf : .pi ⟨.anonymous, piA.dom⟩ piA.cod) ∧
    (∀ {m} {Δ : Ctx 0 m} {a : Tm m} (ρ : Ctx.Wk Δ Γ) (h : Δ ⊢)
      (ha : (piA.polyRed.domRed ρ h).redTm a),
      (piA.polyRed.codRed ρ h ha).redTm ((nf.wk ρ).app a))

/-- Two terms are equal in the Pi reducibility -/
def PiRedTmEq {n} (Γ : Ctx 0 n) (t u : Tm n) (A : Ty n) (piA : PiRedTy Γ A) : Prop :=
  ∃ nfL nfR,
    (Γ ⊩ t ↘ nfL : .pi ⟨.anonymous, piA.dom⟩ piA.cod) ∧
    (Γ ⊩ u ↘ nfR : .pi ⟨.anonymous, piA.dom⟩ piA.cod) ∧
    (Γ ⊢ nfL ≡ nfR : .pi ⟨.anonymous, piA.dom⟩ piA.cod) ∧
    (∀ {m} {Δ : Ctx 0 m} {a : Tm m} (ρ : Ctx.Wk Δ Γ) (h : Δ ⊢),
      (ha : (piA.polyRed.domRed ρ h).redTm a) →
      (piA.polyRed.codRed ρ h ha).eqTm ((nfL.wk ρ).app a) ((nfR.wk ρ).app a))

/-! ## The Main Logical Relation -/

inductive LR (rec : RedRel) : RedRel where
  | ne {n} {Γ : Ctx 0 n} {A : Ty n}
      (neA : NeRedTy Γ A) :
      LR rec Γ A
        (NeRedTyEq Γ A · neA)
        (NeRedTm Γ · A neA)
        (NeRedTmEq Γ · · A neA)
  | U {n} {Γ : Ctx 0 n} {A : Ty n}
      (UA : URedTy Γ A) :
      LR rec Γ A
        (URedTyEq Γ)
        (URedTm Γ · A UA rec)
        (URedTmEq Γ · · A UA rec)
  | Pi {n} {Γ : Ctx 0 n} {A : Ty n}
      (piA : PiRedTy Γ A)
      (piAad : PiRedTyAdequate (LR rec) piA) :
      LR rec Γ A
        (PiRedTyEq Γ A · piA)
        (PiRedTm Γ · A piA)
        (PiRedTmEq Γ · · A piA)

/-! ## Bundled Logical Relation -/

def rec0 : RedRel := fun _ _ _ _ _ => False

def LogRel0 : RedRel := LR rec0

def LRbuild {n} {Γ : Ctx 0 n} {A : Ty n} {eqTy : Ty n → Prop}
    {redTm : Tm n → Prop} {eqTm : Tm n → Tm n → Prop} :
    LR rec0 Γ A eqTy redTm eqTm → LRAdequate Γ A LogRel0 :=
  fun H => {
    pack := { eqTy := eqTy, redTm := redTm, eqTm := eqTm }
    adequate := H
  }

def LRne {n} {Γ : Ctx 0 n} {A : Ty n} (neA : NeRedTy Γ A) :
    LRAdequate Γ A LogRel0 :=
  LRbuild (LR.ne neA)

def LRU {n} {Γ : Ctx 0 n} {A : Ty n} (UA : URedTy Γ A) :
    LRAdequate Γ A LogRel0 :=
  LRbuild (LR.U UA)

def LRPi {n} {Γ : Ctx 0 n} {A : Ty n} (piA : PiRedTy Γ A)
    (piAad : PiRedTyAdequate LogRel0 piA) :
    LRAdequate Γ A LogRel0 :=
  LRbuild (LR.Pi piA piAad)

/-! ## The Fundamental Lemma (statement only) -/

/-- The fundamental lemma: every well-formed type is in the logical relation -/
theorem fundamental {n} {Γ : Ctx 0 n} {A : Ty n}
    (hA : Γ ⊢ A type) : ∃ (P : LRAdequate Γ A LogRel0), True := by
  sorry

/-- Weakening follows from the fundamental lemma -/
theorem weakening' {m n} {Γ : Ctx 0 m} {Δ : Ctx 0 n} {A : Ty m}
    (ρ : Ctx.Wk Δ Γ) (hΔ : Δ ⊢) (hA : Γ ⊢ A type) : Δ ⊢ A.wk ρ type := by
  sorry

/-- Substitution follows from the fundamental lemma -/
theorem substitution' {n} {Γ : Ctx 0 n} {x : Name} {A : Ty n} {B : Ty (n + 1)} {a : Tm n}
    (hB : Γ.snoc ⟨x, A⟩ ⊢ B type) (ha : Γ ⊢ a : A) : Γ ⊢ B[a] type := by
  sorry

end Qdt
