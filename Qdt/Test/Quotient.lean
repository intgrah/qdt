import Qdt.Test

open Qdt

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient α R → Type w)
      (Pc : (a : α) → P (quotient.class_of α R a))
      (Pp : Type w)
      (x : quotient α R) :
      P x

  def rec_class_of.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient α R → Type w)
      (Pc : (a : α) → P (quotient.class_of α R a))
      (Pp : Type w)
      (a : α) :
      @quotient.rec α R P Pc Pp (quotient.class_of α R a) = Pc a :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient α R → Type w)
      (Pc : (a : α) → P (quotient.class_of α R a))
      (Pp : Type w)
      (x : quotient α R) :
      P x

  def rec_class_of_under_fn.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (g : β → β)
      (f : α → β)
      (Pp : Type w)
      (a : α) :
      g (@quotient.rec α R (fun _ => β) f Pp (quotient.class_of α R a)) = g (f a) :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient α R → Type w)
      (Pc : (a : α) → P (quotient.class_of α R a))
      (Pp : Type w)
      (x : quotient α R) :
      P x

  def elim.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (Pc : α → β)
      (Pp : Type w)
      (x : quotient α R) :
      β :=
    @quotient.rec α R (fun _ => β) Pc Pp x

  def elim_class_of.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (β : Type w)
      (Pc : α → β)
      (Pp : Type w)
      (a : α) :
      elim α R β Pc Pp (quotient.class_of α R a) = Pc a :=
    Eq.refl _
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  axiom quotient.{u, v} (α : Type u) : (α → α → Type v) → Type (max u v)
  axiom quotient.class_of.{u, v} (α : Type u) (R : α → α → Type v) (a : α) :
      quotient α R
  axiom quotient.rec.{u, v, w}
      (α : Type u)
      (R : α → α → Type v)
      (P : quotient α R → Type w)
      (Pc : (a : α) → P (quotient.class_of α R a))
      (Pp : Type w)
      (x : quotient α R) :
      P x

  axiom triv : Nat → Nat → Type

  def succ_of_class_of (k : Nat) :
    (@quotient.rec Nat triv (fun _ => Nat) Nat.succ Nat (quotient.class_of Nat triv k)) = Nat.succ k :=
    Eq.refl _
)
