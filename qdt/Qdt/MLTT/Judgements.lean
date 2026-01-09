import Qdt.MLTT.Context
import Qdt.MLTT.Substitution

namespace Qdt

open Lean (Name)

section Definitions

inductive Judgement (n : Nat) : Type
  | Ctx.WF : Judgement n
  | Ty.WF : Ty n → Judgement n
  | Tm.HasType : Tm n → Ty n → Judgement n
  | Tm.Eq : Tm n → Tm n → Ty n → Judgement n
  | Ty.Eq : Ty n → Ty n → Judgement n

def Judgement.shiftAfter {n} (m s : Nat) : Judgement n → Judgement (n + s)
  | Ctx.WF => Ctx.WF
  | Ty.WF A => Ty.WF (A.shiftAfter m s)
  | Tm.HasType a A => Tm.HasType (a.shiftAfter m s) (A.shiftAfter m s)
  | Tm.Eq a b A => Tm.Eq (a.shiftAfter m s) (b.shiftAfter m s) (A.shiftAfter m s)
  | Ty.Eq A B => Ty.Eq (A.shiftAfter m s) (B.shiftAfter m s)

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

-- @[app_unexpander Ctx.WF]
-- def Ctx.WF.unexpand : Lean.PrettyPrinter.Unexpander
--   | `($_ $Γ) => `($Γ ⊢)
--   | _ => throw ()

-- @[app_unexpander Ty.WF]
-- def Ty.WF.unexpand : Lean.PrettyPrinter.Unexpander
--   | `($_ $Γ $A) => `($Γ ⊢ $A type)
--   | _ => throw ()

-- @[app_unexpander Ty.Eq]
-- def Ty.Eq.unexpand : Lean.PrettyPrinter.Unexpander
--   | `($_ $Γ $A $B) => `($Γ ⊢ $A ≡ $B type)
--   | _ => throw ()

-- @[app_unexpander Tm.Eq]
-- def Tm.Eq.unexpand : Lean.PrettyPrinter.Unexpander
--   | `($_ $Γ $e₁ $e₂ $A) => `($Γ ⊢ $e₁ ≡ $e₂ : $A)
--   | _ => throw ()

-- @[app_unexpander Tm.HasType]
-- def Tm.HasType.unexpand : Lean.PrettyPrinter.Unexpander
--   | `($_ $Γ $e $A) => `($Γ ⊢ $e : $A)
--   | _ => throw ()

end Qdt
