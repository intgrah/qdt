import Qdt.MLTT.Context
import Qdt.MLTT.Substitution

namespace Qdt

open Lean (Name)

section Definitions

set_option hygiene false

notation:50 Γ " ⊢" => Ctx.WF Γ
notation:50 Γ " ⊢ " A " type" => Ty.WF Γ A
notation:50 Γ " ⊢ " e " : " A => Tm.HasType Γ e A
notation:50 Γ " ⊢ " a " ≡ " b " : " C => Tm.Eq Γ a b C
notation:50 Γ " ⊢ " A " ≡ " B " type" => Ty.Eq Γ A B

mutual

/-- Well-formedness of contexts -/
inductive Ctx.WF : {n : Nat} → Ctx 0 n → Prop
  /-- HoTT book A.2.1, ctx-emp -/
  | empty :
      (Tele.nil ⊢)
  /-- HoTT book A.2.1, ctx-ext -/
  | extend {Γ x A} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢)

/-- Well-formedness of types -/
inductive Ty.WF : {n : Nat} → Ctx 0 n → Ty n → Prop
  /-- HoTT book A.2.3, 𝑢-intro -/
  | u_form {Γ} :
      (Γ ⊢) →
      (Γ ⊢ 𝑢 type)
  /-- Because of Tarski universes -/
  | el_form {Γ t} :
      (Γ ⊢ t : 𝑢) →
      (Γ ⊢ .el t type)
  /-- HoTT book A.2.4, Π-form -/
  | pi_form {Γ x A B} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢ B type) →
      (Γ ⊢ .pi ⟨x, A⟩ B type)

/-- Judgmental equality of types -/
inductive Ty.Eq : {n : Nat} → Ctx 0 n → Ty n → Ty n → Prop
  /-- HoTT book A.2.2, reflexivity -/
  | refl {n Γ} {A : Ty n} :
      (Γ ⊢ A type) →
      (Γ ⊢ A ≡ A type)
  /-- HoTT book A.2.2, symmetry -/
  | symm {n Γ} {A B : Ty n} :
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ B ≡ A type)
  /-- HoTT book A.2.2, transitivity -/
  | trans {n Γ} {A B C : Ty n} :
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ B ≡ C type) →
      (Γ ⊢ A ≡ C type)
  /-- HoTT book A.2.2, Π-form-eq -/
  | pi_form_eq {n Γ} {A₁ A₂ : Ty n} {x : Name} {B₁ B₂ : Ty (n + 1)} :
      (Γ ⊢ A₁ ≡ A₂ type) →
      (Γ.snoc ⟨x, A₁⟩ ⊢ B₁ ≡ B₂ type) →
      (Γ ⊢ .pi ⟨x, A₁⟩ B₁ ≡ .pi ⟨x, A₂⟩ B₂ type)
  /-- Because of Tarski universes -/
  | el_form_eq {n Γ} {t₁ t₂ : Tm n} :
      (Γ ⊢ t₁ ≡ t₂ : 𝑢) →
      (Γ ⊢ .el t₁ ≡ .el t₂ type)

/-- Judgmental equality of terms -/
inductive Tm.Eq : {n : Nat} → Ctx 0 n → Tm n → Tm n → Ty n → Prop
  /-- HoTT book A.2.2, reflexivity -/
  | refl {n Γ} {a : Tm n}{A : Ty n} :
      (Γ ⊢ a : A) →
      (Γ ⊢ a ≡ a : A)
  /-- HoTT book A.2.2, symmetry -/
  | symm {n Γ} {a b : Tm n} {A : Ty n} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ b ≡ a : A)
  /-- HoTT book A.2.2, transitivity -/
  | trans {n Γ} {a b c : Tm n} {A : Ty n} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ b ≡ c : A) →
      (Γ ⊢ a ≡ c : A)
  /-- HoTT book A.2.2, Π-intro-eq -/
  | pi_intro_eq {n Γ} {x : Name} {b₁ b₂ : Tm (n + 1)} {A₁ A₂ : Ty n} {B : Ty (n + 1)} :
      (Γ ⊢ A₁ ≡ A₂ type) →
      (Γ.snoc ⟨x, A₁⟩ ⊢ b₁ ≡ b₂ : B) →
      (Γ ⊢ .lam ⟨x, A₁⟩ b₁ ≡ .lam ⟨x, A₂⟩ b₂ : .pi ⟨x, A₁⟩ B)
  /-- HoTT book A.2.2, Π-elim-eq -/
  | pi_elim_eq {n Γ} {x : Name} {f₁ f₂ a₁ a₂ : Tm n} {A : Ty n} {B : Ty (n + 1)} :
      (Γ ⊢ f₁ ≡ f₂ : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a₁ ≡ a₂ : A) →
      (Γ ⊢ f₁.app a₁ ≡ f₂.app a₂ : B[a₁])
  /-- HoTT book A.2.4, Π-comp (β-reduction) -/
  | pi_comp {n Γ} {x : Name} {a : Tm n} {b : Tm (n + 1)} {A : Ty n} {B : Ty (n + 1)} :
      (Γ.snoc ⟨x, A⟩ ⊢ b : B) →
      (Γ ⊢ a : A) →
      (Γ ⊢ (Tm.lam ⟨x, A⟩ b).app a ≡ b[a] : B[a])
  /-- HoTT book A.2.4, Π-uniq (η-conversion) -/
  | pi_uniq {n Γ} {x : Name} {A : Ty n} {B : Ty (n + 1)} {f : Tm n} :
      (Γ ⊢ f : .pi ⟨x, A⟩ B) →
      (Γ ⊢ f ≡ .lam ⟨x, A⟩ ((↑f).app (.var ⟨0, Nat.zero_lt_succ n⟩)) : .pi ⟨x, A⟩ B)
  /-- HoTT book A.1.1, conversion -/
  | conv {n Γ} {A B : Ty n} {a b : Tm n} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ a ≡ b : B)

/-- Typing judgment -/
inductive Tm.HasType : {n : Nat} → Ctx 0 n → Tm n → Ty n → Prop
  /-- HoTT book A.2.2, vble -/
  | var {n Γ} :
      (Γ ⊢) →
      (i : Idx n) →
      (Γ ⊢ .var i : Γ.get i)
  | const {Γ x} :
      (Γ ⊢) →
      (Γ ⊢ .const x : 𝑢) -- TODO: add support for global constants
  /-- HoTT book A.2.4, Π-intro -/
  | pi_intro {Γ x A body B} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢ body : B) →
      (Γ ⊢ .lam ⟨x, A⟩ body : .pi ⟨x, A⟩ B)
  /-- HoTT book A.2.4, Π-elim -/
  | pi_elim {Γ f a x A B} :
      (Γ ⊢ f : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a : A) →
      (Γ ⊢ f.app a : B[a])
  /-- HoTT book A.2.2, conversion -/
  | conv {Γ e A B} :
      (Γ ⊢ e : A) →
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ e : B)

end

end Definitions

@[app_unexpander Ctx.WF]
def Ctx.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ) => `($Γ ⊢)
  | _ => throw ()

@[app_unexpander Ty.WF]
def Ty.WF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $A) => `($Γ ⊢ $A type)
  | _ => throw ()

@[app_unexpander Ty.Eq]
def Ty.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $A $B) => `($Γ ⊢ $A ≡ $B type)
  | _ => throw ()

@[app_unexpander Tm.Eq]
def Tm.Eq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $e₁ $e₂ $A) => `($Γ ⊢ $e₁ ≡ $e₂ : $A)
  | _ => throw ()

@[app_unexpander Tm.HasType]
def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ $e $A) => `($Γ ⊢ $e : $A)
  | _ => throw ()

end Qdt
