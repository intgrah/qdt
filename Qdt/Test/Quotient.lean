import Qdt.Test

open Qdt

/-! ## `quotient.rec` β-reduction on `quotient.class_of` -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient.{u, v} α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient.{u, v} α R → Type w)
      (Pc : (a : α) → P (quotient.class_of.{u, v} α R a))
      (Pp : Type w)
      (x : quotient.{u, v} α R) :
      P x

  def rec_class_of.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient.{u, v} α R → Type w)
      (Pc : (a : α) → P (quotient.class_of.{u, v} α R a))
      (Pp : Type w)
      (a : α) :
      Eq.{w} (P (quotient.class_of.{u, v} α R a))
        (quotient.rec.{u, v, w} α R P Pc Pp (quotient.class_of.{u, v} α R a))
        (Pc a) :=
    Eq.refl.{w} (P (quotient.class_of.{u, v} α R a)) (Pc a)
)

/-! ## Reduction under an outer function -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient.{u, v} α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient.{u, v} α R → Type w)
      (Pc : (a : α) → P (quotient.class_of.{u, v} α R a))
      (Pp : Type w)
      (x : quotient.{u, v} α R) :
      P x

  def rec_class_of_under_fn.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (g : β → β)
      (f : α → β)
      (Pp : Type w)
      (a : α) :
      Eq.{w} β
        (g (quotient.rec.{u, v, w} α R (fun (_ : quotient.{u, v} α R) => β)
              f Pp (quotient.class_of.{u, v} α R a)))
        (g (f a)) :=
    Eq.refl.{w} β (g (f a))
)

/-! ## `quotient.elim` defined via `quotient.rec` reduces on `quotient.class_of` -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient.{u, v} α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient.{u, v} α R → Type w)
      (Pc : (a : α) → P (quotient.class_of.{u, v} α R a))
      (Pp : Type w)
      (x : quotient.{u, v} α R) :
      P x

  def elim.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (Pc : α → β)
      (Pp : Type w)
      (x : quotient.{u, v} α R) :
      β :=
    quotient.rec.{u, v, w} α R (fun (_ : quotient.{u, v} α R) => β) Pc Pp x

  def elim_class_of.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (Pc : α → β)
      (Pp : Type w)
      (a : α) :
      Eq.{w} β
        (elim.{u, v, w} α R β Pc Pp (quotient.class_of.{u, v} α R a))
        (Pc a) :=
    Eq.refl.{w} β (Pc a)
)

/-! ## Reduction at concrete universe instantiations -/

#pass (
  inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
    | refl : Eq α a a

  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient.{u, v} α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient.{u, v} α R → Type w)
      (Pc : (a : α) → P (quotient.class_of.{u, v} α R a))
      (Pp : Type w)
      (x : quotient.{u, v} α R) :
      P x

  axiom triv : Nat → Nat → Type

  def succ_of_class_of (k : Nat) :
      Eq.{0} Nat
        (quotient.rec.{0, 0, 0} Nat triv (fun (_ : quotient.{0, 0} Nat triv) => Nat)
          Nat.succ Nat (quotient.class_of.{0, 0} Nat triv k))
        (Nat.succ k) :=
    Eq.refl.{0} Nat (Nat.succ k)
)
