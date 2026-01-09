import Qdt.MLTT.Context
import Qdt.MLTT.Substitution.Basic
import Lean.Elab.Tactic

namespace Qdt

open Lean (Name)

section Definitions

inductive Judgement (n : Nat) : Type
  | Ctx.WF : Judgement n
  | Ty.WF : Ty n → Judgement n
  | Tm.HasType : Tm n → Ty n → Judgement n
  | Tm.Eq : Tm n → Tm n → Ty n → Judgement n
  | Ty.Eq : Ty n → Ty n → Judgement n

set_option hygiene false

notation:50 Γ " ⊢ " 𝒿 => Derives Γ 𝒿
notation:50 Γ " ⊢ " => Derives Γ (Judgement.Ctx.WF)
notation:50 Γ " ⊢ " A "type" => Derives Γ (Judgement.Ty.WF A)
notation:50 Γ " ⊢ " a " : " A => Derives Γ (Judgement.Tm.HasType a A)
notation:50 Γ " ⊢ " A "≡ " B " : " C => Derives Γ (Judgement.Tm.Eq A B C)
notation:50 Γ " ⊢ " A "≡" B "type" => Derives Γ (Judgement.Ty.Eq A B)

inductive Derives : ∀ {n}, Ctx 0 n → Judgement n → Prop
  -- ## Context well-formedness
  | empty :
      (Tele.nil ⊢)
  | extend {Γ x A} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢)
  -- ## Type well-formedness
  | u_form {Γ} :
      (Γ ⊢) →
      (Γ ⊢ 𝑢 type)
  | el_form {Γ t} :
      (Γ ⊢ t : 𝑢) →
      (Γ ⊢ .el t type)
  | pi_form {Γ x A B} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢ B type) →
      (Γ ⊢ .pi ⟨x, A⟩ B type)
  -- ## Definitional equality of types
  | refl_eq_ty {Γ A} :
      (Γ ⊢ A type) →
      (Γ ⊢ A ≡ A type)
  | symm_eq_ty {Γ A B} :
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ B ≡ A type)
  | trans_eq_ty {Γ A B C} :
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ B ≡ C type) →
      (Γ ⊢ A ≡ C type)
  -- ## Definitional equality of terms
  | el_form_eq {Γ t₁ t₂} :
      (Γ ⊢ t₁ ≡ t₂ : .u) →
      (Γ ⊢ .el t₁ ≡ .el t₂ type)
  | pi_form_eq {Γ x A₁ A₂ B₁ B₂} :
      (Γ ⊢ A₁ ≡ A₂ type) →
      (Γ.snoc ⟨x, A₁⟩ ⊢ B₁ ≡ B₂ type) →
      (Γ ⊢ .pi ⟨x, A₁⟩ B₁ ≡ .pi ⟨x, A₂⟩ B₂ type)
  | refl_eq_tm {Γ a A} :
      (Γ ⊢ a : A) →
      (Γ ⊢ a ≡ a : A)
  | symm_eq_tm {Γ a b A} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ b ≡ a : A)
  | trans_eq_tm {Γ a b c A} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ b ≡ c : A) →
      (Γ ⊢ a ≡ c : A)
  | pi_intro_eq {Γ x b₁ b₂ A₁ A₂ B} :
      (Γ ⊢ A₁ ≡ A₂ type) →
      (Γ.snoc ⟨x, A₁⟩ ⊢ b₁ ≡ b₂ : B) →
      (Γ ⊢ .lam ⟨x, A₁⟩ b₁ ≡ .lam ⟨x, A₂⟩ b₂ : .pi ⟨x, A₁⟩ B)
  | pi_elim_eq {Γ x f₁ f₂ a₁ a₂ A B} :
      (Γ ⊢ f₁ ≡ f₂ : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a₁ ≡ a₂ : A) →
      (Γ ⊢ f₁.app a₁ ≡ f₂.app a₂ : B[a₁])
  | pi_comp {Γ x a b A B} :
      (Γ.snoc ⟨x, A⟩ ⊢ b : B) →
      (Γ ⊢ a : A) →
      (Γ ⊢ (Tm.lam ⟨x, A⟩ b).app a ≡ b[a] : B[a])
  | pi_uniq {Γ x A B f} :
      (Γ ⊢ f : .pi ⟨x, A⟩ B) →
      (Γ ⊢ f ≡ .lam ⟨x, A⟩ ((↑f).app (.var 0)) : .pi ⟨x, A⟩ B)
  | conv_eq_tm {Γ A B a b} :
      (Γ ⊢ a ≡ b : A) →
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ a ≡ b : B)
  -- ## Typing
  | var {n Γ} :
      (Γ ⊢) →
      (i : Idx n) →
      (Γ ⊢ .var i : Γ.get i)
  | const {Γ x} :
      (Γ ⊢) →
      (Γ ⊢ .const x : 𝑢) -- TODO: add support for global constants
  | pi_intro {Γ x A body B} :
      (Γ ⊢ A type) →
      (Γ.snoc ⟨x, A⟩ ⊢ body : B) →
      (Γ ⊢ .lam ⟨x, A⟩ body : .pi ⟨x, A⟩ B)
  | pi_elim {Γ f a x A B} :
      (Γ ⊢ f : .pi ⟨x, A⟩ B) →
      (Γ ⊢ a : A) →
      (Γ ⊢ f.app a : B[a])
  | conv_has_type {Γ e A B} :
      (Γ ⊢ e : A) →
      (Γ ⊢ A ≡ B type) →
      (Γ ⊢ e : B)

end Definitions

@[app_unexpander Derives]
def Derives.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $Γ Judgement.Ctx.WF) => `($Γ ⊢)
  | `($_ $Γ (Judgement.Ty.WF $A)) => `($Γ ⊢ $A type)
  | `($_ $Γ (Judgement.Tm.HasType $a $A)) => `($Γ ⊢ $a : $A)
  | `($_ $Γ (Judgement.Tm.Eq $a $b $A)) => `($Γ ⊢ $a ≡ $b : $A)
  | `($_ $Γ (Judgement.Ty.Eq $A $B)) => `($Γ ⊢ $A ≡ $B type)
  | _ => throw ()

open Lean Elab Tactic Meta in
/-- Try to guess the correct constructor and apply a closing tactic -/
elab "derives_constructor" closing:tacticSeq : tactic => do
  let ctors := #[
    `Derives.empty,
    `Derives.extend,
    `Derives.u_form,
    `Derives.el_form,
    `Derives.pi_form,
    `Derives.refl_eq_ty,
    `Derives.symm_eq_ty,
    `Derives.trans_eq_ty,
    `Derives.el_form_eq,
    `Derives.pi_form_eq,
    `Derives.refl_eq_tm,
    `Derives.symm_eq_tm,
    `Derives.trans_eq_tm,
    `Derives.pi_intro_eq,
    `Derives.pi_elim_eq,
    `Derives.pi_comp,
    `Derives.pi_uniq,
    `Derives.conv_eq_tm,
    `Derives.var,
    `Derives.const,
    `Derives.pi_intro,
    `Derives.pi_elim,
    `Derives.conv_has_type,
  ]
  for ctor in ctors do
    let s ← saveState
    try
      evalTactic (← `(tactic| apply $(mkIdent ctor)))
      evalTactic (← `(tactic| all_goals $closing))
      return
    catch _ =>
      restoreState s
      continue
  throwError "derives_constructor: no Derives constructor applies"

end Qdt
