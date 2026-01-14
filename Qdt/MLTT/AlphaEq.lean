import Qdt.MLTT.Syntax

namespace Qdt

open Lean (Name)

section Definitions

set_option hygiene false

infix:50 " ≡α " => Ty.AlphaEq
infix:50 " ≡α " => Tm.AlphaEq

mutual

inductive Ty.AlphaEq : ∀ {n}, Ty n → Ty n → Prop
  | refl {n} (t : Ty n) :
      t ≡α t
  | symm {n} {t₁ t₂ : Ty n} :
      t₁ ≡α t₂ →
      t₂ ≡α t₁
  | trans {n} {t₁ t₂ t₃ : Ty n} :
      t₁ ≡α t₂ →
      t₂ ≡α t₃ →
      t₁ ≡α t₃
  | congrPi {n} {x₁ x₂ : Name} {a₁ a₂ : Ty n} {b₁ b₂ : Ty (n + 1)} :
      a₁ ≡α a₂ →
      b₁ ≡α b₂ →
      .pi ⟨x₁, a₁⟩ b₁ ≡α .pi ⟨x₂, a₂⟩ b₂
  | congrEl {n} (t₁ t₂ : Tm n) : t₁ ≡α t₂ → Ty.el t₁ ≡α Ty.el t₂

inductive Tm.AlphaEq : ∀ {n}, Tm n → Tm n → Prop
  | refl {n} (t : Tm n) :
      t ≡α t
  | symm {n} {t₁ t₂ : Tm n} :
      t₁ ≡α t₂ →
      t₂ ≡α t₁
  | trans {n} {t₁ t₂ t₃ : Tm n} :
      t₁ ≡α t₂ →
      t₂ ≡α t₃ →
      t₁ ≡α t₃
  | congrApp {n} {a₁ a₂ b₁ b₂ : Tm n} :
      a₁ ≡α a₂ →
      b₁ ≡α b₂ →
      a₁.app b₁ ≡α a₂.app b₂
  | congrPiHat {n} {x₁ x₂ : Name} {a₁ a₂ : Tm n} {b₁ b₂ : Tm (n + 1)} :
      a₁ ≡α a₂ →
      b₁ ≡α b₂ →
      .pi' x₁ a₁ b₁ ≡α .pi' x₂ a₂ b₂
  | congrLam {n} {x₁ x₂ : Name} {a₁ a₂ : Ty n} {b₁ b₂ : Tm (n + 1)} :
      a₁ ≡α a₂ →
      b₁ ≡α b₂ →
      .lam ⟨x₁, a₁⟩ b₁ ≡α .lam ⟨x₂, a₂⟩ b₂
  | congrLetE {n} {x₁ x₂ : Name} {a₁ a₂ : Ty n} {b₁ b₂ : Tm n} {c₁ c₂ : Tm (n + 1)} :
      a₁ ≡α a₂ →
      b₁ ≡α b₂ →
      c₁ ≡α c₂ →
      .letE x₁ a₁ b₁ c₁ ≡α .letE x₂ a₂ b₂ c₂
end

end Definitions

theorem Ty.AlphaEq.eqv {n} : Equivalence (@Ty.AlphaEq n) where
  refl := refl
  symm := symm
  trans := trans

theorem Tm.AlphaEq.eqv {n} : Equivalence (@Tm.AlphaEq n) where
  refl := refl
  symm := symm
  trans := trans

def Ty.AlphaQuot.setoid (n : Nat) : Setoid (Ty n) where
  r := @Ty.AlphaEq n
  iseqv := Ty.AlphaEq.eqv

def Tm.AlphaQuot.setoid (n : Nat) : Setoid (Tm n) where
  r := @Tm.AlphaEq n
  iseqv := Tm.AlphaEq.eqv

def Ty.AlphaQuot (n : Nat) := Quotient (Ty.AlphaQuot.setoid n)
def Tm.AlphaQuot (n : Nat) := Quotient (Tm.AlphaQuot.setoid n)

-- TODO: decide whether setoid reasoning is worth it

end Qdt
