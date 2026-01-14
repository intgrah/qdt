import QdtTest.Macro

#pass (
  inductive Unit.{u} : Type u where
    | unit

  inductive Eq.{u} (A : Type u) (a : A) : A → Type u where
    | refl : Eq A a a

  def Unit.eta.{u} (t : Unit.{u}) : Eq.{u} Unit.{u} Unit.unit.{u} t :=
    Eq.refl.{u} Unit.{u} Unit.unit.{u}
)

#pass (
  structure Unit.{u} : Type u where

  inductive Eq.{u} (A : Type u) (a : A) : A → Type u where
    | refl : Eq A a a

  def Unit.eta.{u} (t : Unit.{u}) : Eq.{u} Unit.{u} Unit.mk.{u} t :=
    Eq.refl.{u} Unit.{u} Unit.mk.{u}
)

#pass (
  structure Prod.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
    (fst : A)
    (snd : B)

  inductive Eq.{u} (A : Type u) (a : A) : A → Type u where
    | refl : Eq A a a

  def Prod.eta.{u, v} (A : Type u) (B : Type v) (p : Prod.{u, v} A B) :
      Eq.{max u v} (Prod.{u, v} A B) (Prod.mk.{u, v} A B (Prod.fst.{u, v} A B p) (Prod.snd.{u, v} A B p)) p :=
    Eq.refl.{max u v} (Prod.{u, v} A B) p
)

#pass (
  structure Sigma.{u, v} (A : Type u) (B : A → Type v) : Type (max u v) where
    (fst : A)
    (snd : B fst)

  inductive Eq.{u} (A : Type u) (a : A) : A → Type u where
    | refl : Eq A a a

  def Sigma.eta.{u, v} (A : Type u) (B : A → Type v) (p : Sigma.{u, v} A B) :
      Eq.{max u v} (Sigma.{u, v} A B) (Sigma.mk.{u, v} A B (Sigma.fst.{u, v} A B p) (Sigma.snd.{u, v} A B p)) p :=
    Eq.refl.{max u v} (Sigma.{u, v} A B) p
)
