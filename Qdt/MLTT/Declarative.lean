import Qdt.MLTT.Context
import Qdt.MLTT.Substitution.Basic
import Qdt.MLTT.Global

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
inductive Global.WF : Global → Prop
  | empty :
      (⊢ ∅)
  | addDef {Δ name info} :
      (name ∉ Δ) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (Δ; Tele.nil ⊢ info.tm : info.ty) →
      (⊢ Δ.insert name (.definition info))
  | addOpaque {Δ name info} :
      (name ∉ Δ) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (⊢ Δ.insert name (.opaque info))
  | addAxiom {Δ name info} :
      (name ∉ Δ) →
      (Δ; Tele.nil ⊢ info.ty type) →
      (⊢ Δ.insert name (.axiom info))

/-- Well-formedness of contexts -/
inductive Ctx.WF : Global → {n : Nat} → Ctx 0 n → Prop
  /-- HoTT book A.2.1, ctx-emp -/
  | empty {Δ} :
      (⊢ Δ) →
      (Δ; Tele.nil ⊢)
  /-- HoTT book A.2.1, ctx-ext -/
  | extend {Δ Γ src x A} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨src, x, A⟩ ⊢)

/-- Well-formedness of types -/
inductive Ty.WF : Global → {n : Nat} → Ctx 0 n → Ty n → Prop
  /-- HoTT book A.2.3, 𝑢-intro -/
  | u_form {Δ Γ s i} :
      (Δ; Γ ⊢) →
      (Δ; Γ ⊢ .u s i type)
  /-- Tarski universe: if t : 𝑢 i then El(t) type -/
  | el_form {Δ Γ s i t} :
      (Δ; Γ ⊢ t : .u s i) →
      (Δ; Γ ⊢ .el s t type)
  /-- HoTT book A.2.4, Π-form -/
  | pi_form {Δ Γ s ps x A B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨ps, x, A⟩ ⊢ B type) →
      (Δ; Γ ⊢ .pi s ⟨ps, x, A⟩ B type)

/-- Judgmental equality of types -/
inductive Ty.Eq : Global → {n : Nat} → Ctx 0 n → Ty n → Ty n → Prop
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
  /-- HoTT book A.2.2, Π-form-eq -/
  | pi_form_eq {Δ Γ s₁ s₂ ps₁ ps₂ A₁ A₂ x B₁ B₂} :
      (Δ; Γ ⊢ A₁ ≡ A₂ type) →
      (Δ; Γ.snoc ⟨ps₁, x, A₁⟩ ⊢ B₁ ≡ B₂ type) →
      (Δ; Γ ⊢ .pi s₁ ⟨ps₁, x, A₁⟩ B₁ ≡ .pi s₂ ⟨ps₂, x, A₂⟩ B₂ type)
  | el_form_eq {Δ Γ s₁ s₂ su i t₁ t₂} :
      (Δ; Γ ⊢ t₁ ≡ t₂ : .u su i) →
      (Δ; Γ ⊢ .el s₁ t₁ ≡ .el s₂ t₂ type)

/-- Judgmental equality of terms -/
inductive Tm.Eq : Global → {n : Nat} → Ctx 0 n → Tm n → Tm n → Ty n → Prop
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
  /-- Definition unfolding (δ-reduction) -/
  | delta {Δ Γ sc name us info} :
      (Δ; Γ ⊢) →
      Δ.findDefinition name = some info →
      (Δ; Γ ⊢ .const sc name us ≡ info.tm.wkClosed : info.ty.wkClosed)
  /-- HoTT book A.2.2, Π-intro-eq -/
  | pi_intro_eq {Δ Γ sl₁ sl₂ sp ps₁ ps₂ x b₁ b₂ A₁ A₂ B} :
      (Δ; Γ ⊢ A₁ ≡ A₂ type) →
      (Δ; Γ.snoc ⟨ps₁, x, A₁⟩ ⊢ b₁ ≡ b₂ : B) →
      (Δ; Γ ⊢ .lam sl₁ ⟨ps₁, x, A₁⟩ b₁ ≡ .lam sl₂ ⟨ps₂, x, A₂⟩ b₂ : .pi sp ⟨ps₁, x, A₁⟩ B)
  /-- HoTT book A.2.2, Π-elim-eq -/
  | pi_elim_eq {Δ Γ sp ps sa₁ sa₂ x f₁ f₂ a₁ a₂ A B} :
      (Δ; Γ ⊢ f₁ ≡ f₂ : .pi sp ⟨ps, x, A⟩ B) →
      (Δ; Γ ⊢ a₁ ≡ a₂ : A) →
      (Δ; Γ ⊢ .app sa₁ f₁ a₁ ≡ .app sa₂ f₂ a₂ : B[a₁])
  /-- HoTT book A.2.4, Π-comp (β-reduction) -/
  | pi_comp {Δ Γ sl sa sp ps x a b A B} :
      (Δ; Γ.snoc ⟨ps, x, A⟩ ⊢ b : B) →
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ ⊢ .app sa (Tm.lam sl ⟨ps, x, A⟩ b) a ≡ b[a] : B[a])
  /-- HoTT book A.2.4, Π-uniq (η-conversion) -/
  | pi_uniq {Δ Γ sl sa sp ps x A B f} :
      (Δ; Γ ⊢ f : .pi sp ⟨ps, x, A⟩ B) →
      (Δ; Γ ⊢ f ≡ .lam sl ⟨ps, x, A⟩ (.app sa (↑f) (.var none 0)) : .pi sp ⟨ps, x, A⟩ B)
  /-- Let reduction (ζ-reduction) -/
  | zeta {Δ Γ slet ps x A e body B} :
      (Δ; Γ ⊢ e : A) →
      (Δ; Γ.snoc ⟨ps, x, A⟩ ⊢ body : B) →
      (Δ; Γ ⊢ .letE slet x A e body ≡ body[e] : B[e])
  -- TODO: proj reduction
  -- TODO: ι-reduction

/-- Typing judgment -/
inductive Tm.HasType : Global → {n : Nat} → Ctx 0 n → Tm n → Ty n → Prop
  /-- HoTT book A.2.2, vble -/
  | var {Δ n Γ sv} :
      (Δ; Γ ⊢) →
      (i : Idx n) →
      (Δ; Γ ⊢ .var sv i : Γ.get i)
  /-- Global constant -/
  | const {Δ Γ sc name us ty} :
      (Δ; Γ ⊢) →
      Δ.findTy name = some ty →
      (Δ; Γ ⊢ .const sc name us : ty.wkClosed)
  /-- HoTT book A.2.4, Π-intro -/
  | pi_intro {Δ Γ sl sp ps x A body B} :
      (Δ; Γ ⊢ A type) →
      (Δ; Γ.snoc ⟨ps, x, A⟩ ⊢ body : B) →
      (Δ; Γ ⊢ .lam sl ⟨ps, x, A⟩ body : .pi sp ⟨ps, x, A⟩ B)
  /-- HoTT book A.2.4, Π-elim -/
  | pi_elim {Δ Γ sp sa ps f a x A B} :
      (Δ; Γ ⊢ f : .pi sp ⟨ps, x, A⟩ B) →
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ ⊢ .app sa f a : B[a])
  /-- Let introduction -/
  | let_intro {Δ Γ slet ps x A a b B} :
      (Δ; Γ ⊢ a : A) →
      (Δ; Γ.snoc ⟨ps, x, A⟩ ⊢ b : B) →
      (Δ; Γ ⊢ .letE slet x A a b : B[a])
  /-- HoTT book A.2.2, conversion -/
  | conv {Δ Γ e A B} :
      (Δ; Γ ⊢ e : A) →
      (Δ; Γ ⊢ A ≡ B type) →
      (Δ; Γ ⊢ e : B)

end

end Definitions

/-!
## Unexpanders for pretty printing
-/

@[app_unexpander Global.WF]
def Global.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ) => `(⊢ $Δ)
  | _ => throw ()

@[app_unexpander Ctx.WF]
def Ctx.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ) => `($Δ; $Γ ⊢)
  | _ => throw ()

@[app_unexpander Ty.WF]
def Ty.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $A) => `($Δ; $Γ ⊢ $A type)
  | _ => throw ()

@[app_unexpander Ty.Eq]
def Ty.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $A $B) => `($Δ; $Γ ⊢ $A ≡ $B type)
  | _ => throw ()

@[app_unexpander Tm.Eq]
def Tm.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $e₁ $e₂ $A) => `($Δ; $Γ ⊢ $e₁ ≡ $e₂ : $A)
  | _ => throw ()

@[app_unexpander Tm.HasType]
def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Δ $Γ $e $A) => `($Δ; $Γ ⊢ $e : $A)
  | _ => throw ()

/-!
## Presupposition Lemmas

Every judgment presupposes context well-formedness, which presupposes global well-formedness.
-/

theorem Global.WF.presupGlobal {Δ : Global} :
    Global.WF Δ → Global.WF Δ := id

mutual

theorem Ctx.WF.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} :
    Ctx.WF Δ Γ → Global.WF Δ
  | .empty h
  | .extend h => h.presupGlobal

theorem Ty.WF.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {A} :
    Ty.WF Δ Γ A → Global.WF Δ
  | .u_form h
  | .el_form h
  | .pi_form h _ => h.presupGlobal

theorem Tm.HasType.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {e A} :
    Tm.HasType Δ Γ e A → Global.WF Δ
  | .var h _
  | .const h _
  | .conv h _
  | .pi_intro h _
  | .pi_elim h _
  | .let_intro h _ => h.presupGlobal

theorem Ty.Eq.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {A B} :
    Ty.Eq Δ Γ A B → Global.WF Δ
  | .refl h
  | .symm h
  | .trans h _
  | .pi_form_eq h _
  | .el_form_eq h => h.presupGlobal

theorem Tm.Eq.presupGlobal {Δ : Global} {n} {Γ : Ctx 0 n} {a b A} :
    Tm.Eq Δ Γ a b A → Global.WF Δ
  | .refl h
  | .symm h
  | .trans h _
  | .conv h _
  | .delta h _
  | .pi_intro_eq h _
  | .pi_elim_eq h _
  | .pi_comp _ h
  | .pi_uniq h
  | .zeta h _ => h.presupGlobal

end

theorem Ctx.WF.presup {Δ : Global} {n} {Γ : Ctx 0 n} :
    Ctx.WF Δ Γ → Ctx.WF Δ Γ := id

mutual

theorem Ty.WF.presup {Δ : Global} {n} {Γ : Ctx 0 n} {A} :
    Ty.WF Δ Γ A → Ctx.WF Δ Γ
  | .u_form h
  | .el_form h
  | .pi_form h _ => h.presup

theorem Tm.HasType.presup {Δ : Global} {n} {Γ : Ctx 0 n} {e A} :
    Tm.HasType Δ Γ e A → Ctx.WF Δ Γ
  | .var h _
  | .const h _
  | .conv h _
  | .pi_intro h _
  | .pi_elim h _
  | .let_intro h _ => h.presup

theorem Ty.Eq.presup {Δ : Global} {n} {Γ : Ctx 0 n} {A B} :
    Ty.Eq Δ Γ A B → Ctx.WF Δ Γ
  | .refl h
  | .symm h
  | .trans h _
  | .pi_form_eq h _
  | .el_form_eq h => h.presup

theorem Tm.Eq.presup {Δ : Global} {n} {Γ : Ctx 0 n} {a b A} :
    Tm.Eq Δ Γ a b A → Ctx.WF Δ Γ
  | .refl h
  | .symm h
  | .trans h _
  | .conv h _
  | .delta h _
  | .pi_intro_eq h _
  | .pi_elim_eq h _
  | .pi_comp _ h
  | .pi_uniq h
  | .zeta h _ => h.presup

end

end Qdt
