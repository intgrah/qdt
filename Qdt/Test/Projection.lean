import Qdt.Test

#pass (
  structure Prod.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
    (fst : A)
    (snd : B)

  def mk.{u, v} {A : Type u} {B : Type v} (a : A) (b : B) : Prod A B :=
    Prod.mk a b

  def fst.{u, v} {A : Type u} {B : Type v} (p : Prod A B) : A :=
    Prod.fst p

  def snd.{u, v} {A : Type u} {B : Type v} (p : Prod A B) : B :=
    Prod.snd p

  def rec.{w, u, v} {A : Type u} {B : Type v}
      (motive : Prod A B → Type w)
      (mk : (fst : A) → (snd : B) → motive (Prod.mk fst snd))
      (t : Prod A B) :
      motive t :=
    Prod.rec mk t
)

#pass (
  structure Sigma.{u, v} (A : Type u) (B : A → Type v) : Type (max u v) where
    (fst : A)
    (snd : B fst)

  def mk.{u, v} {A : Type u} {B : A → Type v} (fst : A) (snd : B fst) : Sigma A B :=
    Sigma.mk fst snd

  def fst.{u, v} {A : Type u} {B : A → Type v} (p : Sigma A B) : A :=
    Sigma.fst p

  def snd.{u, v} {A : Type u} {B : A → Type v} (p : Sigma A B) : B (Sigma.fst p) :=
    Sigma.snd p

  def rec.{w, u, v} {A : Type u} {B : A → Type v}
      (motive : Sigma A B → Type w)
      (mk : (fst : A) → (snd : B fst) → motive (Sigma.mk fst snd))
      (t : Sigma A B) :
      motive t :=
    Sigma.rec mk t
)

#pass (
  structure Sigma3.{u, v, w} (A : Type u) (B : A → Type v) (C : (a : A) → B a → Type w) : Type (max (max u v) w) where
    (fst : A)
    (snd : B fst)
    (thd : C fst snd)

  def mk.{u, v, w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
      (fst : A) (snd : B fst) (thd : C fst snd) : Sigma3 A B C :=
    Sigma3.mk fst snd thd

  def fst.{u, v, w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
      (p : Sigma3 A B C) : A :=
    Sigma3.fst p

  def snd.{u, v, w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
      (p : Sigma3 A B C) : B (Sigma3.fst p) :=
    Sigma3.snd p

  def thd.{u, v, w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
      (p : Sigma3 A B C) : C (Sigma3.fst p) (Sigma3.snd p) :=
    Sigma3.thd p

  def rec.{x, u, v, w} {A : Type u} {B : A → Type v} {C : (a : A) → B a → Type w}
      (motive : Sigma3 A B C → Type x)
      (mk : (fst : A) → (snd : B fst) → (thd : C fst snd) → motive (Sigma3.mk fst snd thd))
      (t : Sigma3 A B C) :
      motive t :=
    Sigma3.rec mk t
)

#pass (
  structure Stream.{u} (A : Type u) : Type u where
    (head : A)
    (tail : Stream A)

  def mk.{u} {A : Type u} (head : A) (tail : Stream A) : Stream A :=
    Stream.mk head tail

  def head.{u} {A : Type u} (s : Stream A) : A :=
    Stream.head s

  def tail.{u} {A : Type u} (s : Stream A) : Stream A :=
    Stream.tail s

  def rec.{w, u} {A : Type u}
      (motive : Stream A → Type w)
      (mk : (head : A) → (tail : Stream A) → motive tail → motive (Stream.mk head tail))
      (s : Stream A) :
      motive s :=
    Stream.rec mk s
)
