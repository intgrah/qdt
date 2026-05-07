module

public import Qdt.Theory.Context
public import Qdt.Theory.Global

@[expose] public section

namespace Qdt

open Lean (Name)

section Definitions

set_option hygiene false

notation:50 "⊢ " Δ => Global.WF Δ
notation:50 Δ "; " Γ " ⊢" => Ctx.WF Δ Γ
notation:50 Δ "; " Γ " ⊢ " A " type" => Ty.WF Δ Γ A
notation:50 Δ "; " Γ " ⊢ " e " : " A => Tm.HasType Δ Γ e A
notation:50 Δ "; " Γ " ⊢ " a " ≡ " b " : " C => Tm.Eq Δ Γ a b C
notation:50 Δ "; " Γ " ⊢ " A " ≡ " B " type" => Ty.Eq Δ Γ A B

mutual

/-- Well-formedness of global environments -/
inductive Global.WF : Global → Type
  | empty :
      (⊢ ∅)
  | addDef {Δ name info} :
      (name ∉ Δ) →
      (info.ty.Bounded info.numUnivParams) →
      (info.tm.Bounded info.numUnivParams) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (Δ; Tele.nil ⊢ info.tm : info.ty) →
      (⊢ Δ.insert name (.definition info))
  | addOpaque {Δ name info} :
      (name ∉ Δ) →
      (info.ty.Bounded info.numUnivParams) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (⊢ Δ.insert name (.opaque info))
  | addAxiom {Δ name info} :
      (name ∉ Δ) →
      (info.ty.Bounded info.numUnivParams) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (⊢ Δ.insert name (.axiom info))

/-- Well-formedness of contexts -/
inductive Ctx.WF : Global → {n : Nat} → Ctx 0 n → Type
  /-- HoTT book A.2.1, ctx-emp -/
  | empty {Δ} :
      (⊢ Δ) →
      (Δ; Tele.nil ⊢)
  /-- HoTT book A.2.1, ctx-ext -/
  | extend {Δ Γ x A} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢)

/-- Well-formedness of types -/
inductive Ty.WF : Global → {n : Nat} → Ctx 0 n → Ty n → Type
  /-- HoTT book A.2.3, 𝑢-intro -/
  | u_form {Δ Γ i} :
      (Δ; Γ ⊢) →
      (Δ; Γ ⊢ .u i type)
  /-- Tarski universe: if t : 𝑢 i then El(t) type -/
  | el_form {Δ Γ i t} :
      (Δ; Γ ⊢ t : .u i) →
      (Δ; Γ ⊢ .el t type)
  /-- HoTT book A.2.4, Π-form -/
  | pi_form {Δ Γ x A B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢ B type) →
      (Δ; Γ ⊢ .pi x A B type)

/-- Judgmental equality of types -/
inductive Ty.Eq : Global → {n : Nat} → Ctx 0 n → Ty n → Ty n → Type
  /-- HoTT book A.2.2, reflexivity -/
  | refl {Δ Γ A} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ ⊢ A ≡ A type)
  /-- HoTT book A.2.2, symmetry -/
  | symm {Δ Γ A B} :
      (Δ; Γ ⊢ A ≡ B type) →
      (Δ; Γ ⊢ B ≡ A type)
  /-- HoTT book A.2.2, transitivity -/
  | trans {Δ Γ A B C} :
      (Δ; Γ ⊢ A ≡ B type) →
      (Δ; Γ ⊢ B ≡ C type) →
      (Δ; Γ ⊢ A ≡ C type)
  /-- HoTT book A.2.2, Π-form-eq.  Allows different binder names
  for α-equivalence: the two Π-types share their domain/codomain
  (up to `Ty.Eq`) but may bind under different names. -/
  | pi_form_eq {Δ Γ A₁ A₂ x x' B₁ B₂} :
      (Δ; Γ ⊢ A₁ type) →
      (Δ; Γ ⊢ A₁ ≡ A₂ type) →
      (Δ; Γ.snoc ⟨x, A₁⟩ ⊢ B₁ ≡ B₂ type) →
      (Δ; Γ ⊢ .pi x A₁ B₁ ≡ .pi x' A₂ B₂ type)
  | el_form_eq {Δ Γ i t₁ t₂} :
      (Δ; Γ ⊢ t₁ ≡ t₂ : .u i) →
      (Δ; Γ ⊢ .el t₁ ≡ .el t₂ type)

/-- Judgmental equality of terms -/
inductive Tm.Eq : Global → {n : Nat} → Ctx 0 n → Tm n → Tm n → Ty n → Type
  /-- HoTT book A.2.2, reflexivity -/
  | refl {Δ Γ a A} :
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ ⊢ a ≡ a : A)
  /-- HoTT book A.2.2, symmetry -/
  | symm {Δ Γ a b A} :
      (Δ; Γ ⊢ a ≡ b : A) →
      (Δ; Γ ⊢ b ≡ a : A)
  /-- HoTT book A.2.2, transitivity -/
  | trans {Δ Γ a b c A} :
      (Δ; Γ ⊢ a ≡ b : A) →
      (Δ; Γ ⊢ b ≡ c : A) →
      (Δ; Γ ⊢ a ≡ c : A)
  /-- HoTT book A.1.1, conversion -/
  | conv {Δ Γ A B a b} :
      (Δ; Γ ⊢ a ≡ b : A) →
      (Δ; Γ ⊢ A ≡ B type) →
      (Δ; Γ ⊢ a ≡ b : B)
  /-- Definition unfolding (δ-reduction).  Same arity discipline as
  `Tm.HasType.const`: `us.length = info.numUnivParams`. -/
  | delta {Δ Γ name us info} :
      (Δ; Γ ⊢) →
      Δ.findDefinition name = some info →
      (us.length = info.numUnivParams) →
      (Δ; Γ ⊢ .const name us
              ≡ (info.tm.substLevels us).wkClosed
              : (info.ty.substLevels us).wkClosed)
  /-- HoTT book A.2.2, Π-intro-eq.  Allows different binder names
  for α-equivalence in the surface lambdas. -/
  | pi_intro_eq {Δ Γ x x' b₁ b₂ A₁ A₂ B} :
      (Δ; Γ ⊢ A₁ type) →
      (Δ; Γ ⊢ A₁ ≡ A₂ type) →
      (Δ; Γ.snoc ⟨x, A₁⟩ ⊢ b₁ ≡ b₂ : B) →
      (Δ; Γ ⊢ .lam x A₁ b₁ ≡ .lam x' A₂ b₂ : .pi x A₁ B)
  /-- Term-level Π congruence (for `.pi'` as a term living in `.u`).
  Mirrors `pi_intro_eq` but at the term level. -/
  | pi'_eq {Δ Γ x x' A₁ A₂ B₁ B₂ i j} :
      (Δ; Γ ⊢ A₁ : .u i) →
      (Δ; Γ ⊢ A₁ ≡ A₂ : .u i) →
      (Δ; Γ.snoc ⟨x, .el A₁⟩ ⊢ B₁ ≡ B₂ : .u j) →
      (Δ; Γ ⊢ .pi' x A₁ B₁ ≡ .pi' x' A₂ B₂ : .u (i.mkMax j))
  /-- HoTT book A.2.2, Π-elim-eq -/
  | pi_elim_eq {Δ Γ x f₁ f₂ a₁ a₂ A B} :
      (Δ; Γ ⊢ f₁ ≡ f₂ : .pi x A B) →
      (Δ; Γ ⊢ a₁ ≡ a₂ : A) →
      (Δ; Γ ⊢ .app f₁ a₁ ≡ .app f₂ a₂ : B[a₁])
  /-- HoTT book A.2.4, Π-comp (β-reduction) -/
  | pi_comp {Δ Γ x a b A B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢ b : B) →
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ ⊢ .app (Tm.lam x A b) a ≡ b[a] : B[a])
  /-- HoTT book A.2.4, Π-uniq (η-conversion) -/
  | pi_uniq {Δ Γ x A B f} :
      (Δ; Γ ⊢ f : .pi x A B) →
      (Δ; Γ ⊢ f ≡ .lam x A (.app (↑f) (.var 0)) : .pi x A B)
  /-- Let reduction (ζ-reduction) -/
  | zeta {Δ Γ x A e body B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ ⊢ e : A) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢ body : B) →
      (Δ; Γ ⊢ .letE x A e body ≡ body[e] : B[e])
  /-- ι-reduction: a saturated recursor application whose scrutinee is
  a constructor application reduces to the instantiated right-hand
  side of the matching recursor rule.

  The detailed recipe (shape of the rule, well-typedness of the RHS
  under the specified substitution) is packaged in
  `InductiveDecl.WF` and established in Step 10; this constructor
  requires typing of both sides as a premise. -/
  | iota {Δ n} {Γ : Ctx 0 n}
         {recName : Name} {recUs : List Universe} {info : RecursorInfo}
         {rule : RecursorRule (info.numParams + info.numMotives + info.numMinors)}
         {ctorName : Name} {ctorUs : List Universe}
         {params motives minors indices ctorParams fields : List (Tm n)}
         {A : Ty n}
         (hinfo : Δ.findRecursor recName = some info)
         (hrule : rule ∈ info.recRules.toList)
         (hctor : rule.ctorName = ctorName)
         (hParams     : params.length     = info.numParams)
         (hMotives    : motives.length    = info.numMotives)
         (hMinors     : minors.length     = info.numMinors)
         (hIndices    : indices.length    = info.numIndices)
         (hCtorParams : ctorParams.length = info.numParams)
         (hFields     : fields.length     = rule.numFields)
         (hArgs : (params ++ motives ++ minors ++ fields).length
                    = (info.numParams + info.numMotives + info.numMinors)
                      + rule.numFields) :
      (Δ; Γ ⊢ (Tm.const recName recUs).apps
                 (params ++ motives ++ minors ++ indices ++
                   [(Tm.const ctorName ctorUs).apps (ctorParams ++ fields)]) : A) →
      (Δ; Γ ⊢ (rule.rhs.substLevels (recUs)).subst
                 (Subst.fromArgs (params ++ motives ++ minors ++ fields) hArgs) : A) →
      (Δ; Γ ⊢ (Tm.const recName recUs).apps
                 (params ++ motives ++ minors ++ indices ++
                   [(Tm.const ctorName ctorUs).apps (ctorParams ++ fields)])
            ≡ (rule.rhs.substLevels (recUs)).subst
                 (Subst.fromArgs (params ++ motives ++ minors ++ fields) hArgs)
            : A)
  /-- proj-reduction: projecting the `i`-th field from a constructor
  application yields the corresponding argument. -/
  | proj {Δ n} {Γ : Ctx 0 n}
         {i : Nat} {ctorName : Name} {ctorUs : List Universe}
         {ctorInfo : ConstructorInfo} {indInfo : InductiveInfo}
         {params fields : List (Tm n)} {A : Ty n}
         (hctor : Δ.findConstructor ctorName = some ctorInfo)
         (hind  : Δ.findInductive ctorInfo.indName = some indInfo)
         (hParams : params.length = indInfo.numParams)
         (hIdx    : i < fields.length) :
      (Δ; Γ ⊢ .proj i ((Tm.const ctorName ctorUs).apps (params ++ fields)) : A) →
      (Δ; Γ ⊢ fields[i] : A) →
      (Δ; Γ ⊢ .proj i ((Tm.const ctorName ctorUs).apps (params ++ fields))
            ≡ fields[i] : A)

/-- Typing judgment -/
inductive Tm.HasType : Global → {n : Nat} → Ctx 0 n → Tm n → Ty n → Type
  /-- HoTT book A.2.2, vble -/
  | var {Δ n Γ} :
      (Δ; Γ ⊢) →
      (i : Idx n) →
      (Δ; Γ ⊢ .var i : Γ.get i)
  /-- Global constant.  Universe-polymorphic constants are stored at
  their universe-binder form in `Δ`; using a constant at universe
  arguments `us` instantiates those binders via `substLevels us`.
  The arity hypothesis `us.length = info.numUnivParams` ensures
  every `.level i` reference in `info.ty` is substituted by `us`,
  which is what makes universe-substLevels-preservation of typing
  provable (cf. `Universe.subst` composition). -/
  | const {Δ Γ name us info} :
      (Δ; Γ ⊢) →
      Δ.findConstantInfo name = some info →
      (us.length = info.numUnivParams) →
      (Δ; Γ ⊢ .const name us : (info.ty.substLevels us).wkClosed)
  /-- HoTT book A.2.4, Π-intro -/
  | pi_intro {Δ Γ x A body B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢ body : B) →
      (Δ; Γ ⊢ .lam x A body : .pi x A B)
  /-- HoTT book A.2.4, Π-elim -/
  | pi_elim {Δ Γ f a x A B} :
      (Δ; Γ ⊢ f : .pi x A B) →
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ ⊢ .app f a : B[a])
  /-- Let introduction -/
  | let_intro {Δ Γ x A a b B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ.snoc ⟨x, A⟩ ⊢ b : B) →
      (Δ; Γ ⊢ .letE x A a b : B[a])
  /-- HoTT book A.2.2, conversion -/
  | conv {Δ Γ e A B} :
      (Δ; Γ ⊢ e : A) →
      (Δ; Γ ⊢ A ≡ B type) →
      (Δ; Γ ⊢ e : B)
  /-- Universe-as-term (Russell-style): `.u' i` lives in `.u i.mkSucc`. -/
  | u' {Δ Γ i} :
      (Δ; Γ ⊢) →
      (Δ; Γ ⊢ .u' i : .u i.mkSucc)
  /-- Π-as-term (Russell-style): `.pi' x A B` is the term-level
  encoding of a Π type. Domain `A` lives in universe `i`, codomain
  `B` (over the extended context with `.el A`) lives in universe `j`,
  and the resulting Π lives in `.u (i ⊔ j)`. -/
  | pi' {Δ Γ x A B i j} :
      (Δ; Γ ⊢ A : .u i) →
      (Δ; Γ.snoc ⟨x, .el A⟩ ⊢ B : .u j) →
      (Δ; Γ ⊢ .pi' x A B : .u (i.mkMax j))

end

end Definitions

/-!
## Unexpanders for pretty printing
-/

@[app_unexpander Global.WF]
meta def Global.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ) => `(⊢ $Δ)
  | _ => throw ()

@[app_unexpander Ctx.WF]
meta def Ctx.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ) => `($Δ; $Γ ⊢)
  | _ => throw ()

@[app_unexpander Ty.WF]
meta def Ty.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $A) => `($Δ; $Γ ⊢ $A type)
  | _ => throw ()

@[app_unexpander Ty.Eq]
meta def Ty.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $A $B) => `($Δ; $Γ ⊢ $A ≡ $B type)
  | _ => throw ()

@[app_unexpander Tm.Eq]
meta def Tm.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $e₁ $e₂ $A) => `($Δ; $Γ ⊢ $e₁ ≡ $e₂ : $A)
  | _ => throw ()

@[app_unexpander Tm.HasType]
meta def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $e $A) => `($Δ; $Γ ⊢ $e : $A)
  | _ => throw ()

/-!
## Presupposition Lemmas

Every judgment presupposes context well-formedness, which presupposes global well-formedness.
-/

noncomputable def Global.WF.presupGlobal {Δ : Global} :
    Global.WF Δ → Global.WF Δ := id

mutual

noncomputable def Ctx.WF.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} :
    Ctx.WF Δ Γ → Global.WF Δ
  | .empty h
  | .extend h => h.presupGlobal

noncomputable def Ty.WF.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {A} :
    Ty.WF Δ Γ A → Global.WF Δ
  | .u_form h
  | .el_form h
  | .pi_form h _ => h.presupGlobal

noncomputable def Tm.HasType.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {e A} :
    Tm.HasType Δ Γ e A → Global.WF Δ
  | .var h _
  | .const h _ _
  | .conv h _
  | .pi_intro h _
  | .pi_elim h _
  | .u' h
  | .let_intro h _ _ => h.presupGlobal
  | .pi' h _ => h.presupGlobal

noncomputable def Ty.Eq.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {A B} :
    Ty.Eq Δ Γ A B → Global.WF Δ
  | .refl h
  | .symm h
  | .trans h _
  | .pi_form_eq h _ _
  | .el_form_eq h => h.presupGlobal

noncomputable def Tm.Eq.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {a b A} :
    Tm.Eq Δ Γ a b A → Global.WF Δ
  | .refl h
  | .symm h
  | .trans h _
  | .conv h _
  | .delta h _ _
  | .pi_intro_eq h _ _
  | .pi'_eq h _ _
  | .pi_elim_eq h _
  | .pi_comp h _ _
  | .pi_uniq h
  | .zeta h _ _ => h.presupGlobal
  | .iota _ _ _ _ _ _ _ _ _ _ h _
  | .proj _ _ _ _ h _ => h.presupGlobal

end

noncomputable def Ctx.WF.presup {Δ : Global} {n} {Γ : Ctx 0 n} :
    Ctx.WF Δ Γ → Ctx.WF Δ Γ := id

mutual

noncomputable def Ty.WF.presup {Δ : Global} {n} {Γ : Ctx 0 n} {A} :
    Ty.WF Δ Γ A → Ctx.WF Δ Γ
  | .u_form h
  | .el_form h
  | .pi_form h _ => h.presup

noncomputable def Tm.HasType.presup {Δ : Global} {n} {Γ : Ctx 0 n} {e A} :
    Tm.HasType Δ Γ e A → Ctx.WF Δ Γ
  | .var h _
  | .const h _ _
  | .conv h _
  | .pi_intro h _
  | .pi_elim h _
  | .u' h
  | .let_intro h _ _ => h.presup
  | .pi' h _ => h.presup

noncomputable def Ty.Eq.presup {Δ : Global} {n} {Γ : Ctx 0 n} {A B} :
    Ty.Eq Δ Γ A B → Ctx.WF Δ Γ
  | .refl h
  | .symm h
  | .trans h _
  | .pi_form_eq h _ _
  | .el_form_eq h => h.presup

noncomputable def Tm.Eq.presup {Δ : Global} {n} {Γ : Ctx 0 n} {a b A} :
    Tm.Eq Δ Γ a b A → Ctx.WF Δ Γ
  | .refl h
  | .symm h
  | .trans h _
  | .conv h _
  | .delta h _ _
  | .pi_intro_eq h _ _
  | .pi'_eq h _ _
  | .pi_elim_eq h _
  | .pi_comp h _ _
  | .pi_uniq h
  | .zeta h _ _ => h.presup
  | .iota _ _ _ _ _ _ _ _ _ _ h _
  | .proj _ _ _ _ h _ => h.presup

end

end Qdt
