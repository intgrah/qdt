import QdtTest.Macro

#pass (
  structure Prod.{u, v} (A : Type u) (B : Type v) : Type (max u v) where
    (fst : A)
    (snd : B)

  def mk.{u, v} : (A : Type u) → (B : Type v) → A → B → Prod.{u, v} A B :=
    Prod.mk.{u, v}

  def fst.{u, v} : (A : Type u) → (B : Type v) → Prod.{u, v} A B → A :=
    Prod.fst.{u, v}

  def snd.{u, v} : (A : Type u) → (B : Type v) → Prod.{u, v} A B → B :=
    Prod.snd.{u, v}

  def rec.{w, u, v}
      (A : Type u)
      (B : Type v)
      (motive : Prod.{u, v} A B → Type w)
      (mk : (fst : A) → (snd : B) → motive (Prod.mk.{u, v} A B fst snd))
      (t : Prod.{u, v} A B) :
      motive t :=
    Prod.rec.{w, u, v} A B motive mk t
)

#pass (
  structure Sigma.{u, v} (A : Type u) (B : A → Type v) : Type (max u v) where
    (fst : A)
    (snd : B fst)

  def mk.{u, v} : (A : Type u) → (B : A → Type v) → (fst : A) → B fst → Sigma.{u, v} A B :=
    Sigma.mk.{u, v}

  def fst.{u, v} : (A : Type u) → (B : A → Type v) → Sigma.{u, v} A B → A :=
    Sigma.fst.{u, v}

  def snd.{u, v} : (A : Type u) → (B : A → Type v) → (p : Sigma.{u, v} A B) → B (Sigma.fst.{u, v} A B p) :=
    Sigma.snd.{u, v}

  def rec.{w, u, v}
      (A : Type u)
      (B : A → Type v)
      (motive : Sigma.{u, v} A B → Type w)
      (mk : (fst : A) → (snd : B fst) → motive (Sigma.mk.{u, v} A B fst snd))
      (t : Sigma.{u, v} A B) :
      motive t :=
    Sigma.rec.{w, u, v} A B motive mk t
)

#pass (
  structure Sigma3.{u, v, w} (A : Type u) (B : A → Type v) (C : (a : A) → B a → Type w) : Type (max (max u v) w) where
    (fst : A)
    (snd : B fst)
    (thd : C fst snd)

  def mk.{u, v, w} :
      (A : Type u) →
      (B : A → Type v) →
      (C : (a : A) → B a → Type w) →
      (fst : A) → (snd : B fst) → C fst snd →
      Sigma3.{u, v, w} A B C :=
    Sigma3.mk.{u, v, w}

  def fst.{u, v, w} :
      (A : Type u) →
      (B : A → Type v) →
      (C : (a : A) → B a → Type w) →
      Sigma3.{u, v, w} A B C → A :=
    Sigma3.fst.{u, v, w}

  def snd.{u, v, w} :
      (A : Type u) →
      (B : A → Type v) →
      (C : (a : A) → B a → Type w) →
      (p : Sigma3.{u, v, w} A B C) →
      B (Sigma3.fst.{u, v, w} A B C p) :=
    Sigma3.snd.{u, v, w}

  def thd.{u, v, w} :
      (A : Type u) →
      (B : A → Type v) →
      (C : (a : A) → B a → Type w) →
      (p : Sigma3.{u, v, w} A B C) →
      C (Sigma3.fst.{u, v, w} A B C p) (Sigma3.snd.{u, v, w} A B C p) :=
    Sigma3.thd.{u, v, w}

  def rec.{x, u, v, w}
      (A : Type u)
      (B : A → Type v)
      (C : (a : A) → B a → Type w)
      (motive : Sigma3.{u, v, w} A B C → Type x)
      (mk : (fst : A) → (snd : B fst) → (thd : C fst snd) → motive (Sigma3.mk.{u, v, w} A B C fst snd thd))
      (t : Sigma3.{u, v, w} A B C) :
      motive t :=
    Sigma3.rec.{x, u, v, w} A B C motive mk t
)

#pass (
  structure Stream.{u} (A : Type u) : Type u where
    (head : A)
    (tail : Stream.{u} A)

  def mk.{u} : (A : Type u) → A → Stream.{u} A → Stream.{u} A :=
    Stream.mk.{u}

  def head.{u} : (A : Type u) → Stream.{u} A → A :=
    Stream.head.{u}

  def tail.{u} : (A : Type u) → Stream.{u} A → Stream.{u} A :=
    Stream.tail.{u}

  def rec.{w, u}
      (A : Type u)
      (motive : Stream.{u} A → Type w)
      (mk : (head : A) → (tail : Stream.{u} A) → motive tail → motive (Stream.mk.{u} A head tail))
      (s : Stream.{u} A) :
      motive s :=
    Stream.rec.{w, u} A motive mk s
)
