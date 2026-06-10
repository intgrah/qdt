import Qdt.Test

#pass (
  inductive Unit.{u} : Type u where
    | unit

  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Unit.eta.{u} (t : Unit.{u}) : Unit.unit.{u} = t :=
    Eq.refl Unit.unit
)

#pass (
  structure Unit.{u} : Type u where

  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Unit.eta.{u} (t : Unit.{u}) : Unit.mk.{u} = t :=
    Eq.refl.{u} Unit.mk.{u}
)

#pass (
  structure Prod.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
    (fst : A)
    (snd : B)

  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Prod.eta.{u, v} (A : Type u) (B : Type v) (p : Prod A B) :
      Prod.mk (Prod.fst p) (Prod.snd p) = p :=
    Eq.refl p
)

#pass (
  structure Sigma.{u, v} (A : Type u) (B : A → Type v) : Type (max u v) where
    (fst : A)
    (snd : B fst)

  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def Sigma.eta.{u, v} (A : Type u) (B : A → Type v) (p : Sigma A B) :
      @Sigma.mk A B (Sigma.fst p) (Sigma.snd p) = p :=
    Eq.refl p
)
