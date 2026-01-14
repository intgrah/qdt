import QdtTest.Macro

#pass (
  inductive Empty.{u} : Type u where

  def rec.{w, u}
      (motive : Empty.{u} → Type w)
      (p : Empty.{u}) :
      motive p :=
    Empty.rec.{w, u} motive p
)

#pass (
  inductive Unit.{u} : Type u where
    | unit

  def rec.{w, u}
      (motive : Unit.{u} → Type w)
      (unit : motive Unit.unit.{u})
      (p : Unit.{u}) :
      motive p :=
    Unit.rec.{w, u} motive unit p
)

#pass (
  inductive Bool.{u} : Type u where
    | true
    | false

  def rec.{w, u}
      (motive : Bool.{u} → Type w)
      (true : motive Bool.true.{u})
      (false : motive Bool.false.{u})
      (p : Bool.{u}) :
      motive p :=
    Bool.rec.{w, u} motive true false p
)

#pass (
  inductive W.{u, v} (C : Type u) (A : C → Type v) : Type (max u v) where
    | tree (root : C) (subtr : A root → W C A) : W C A

  def rec.{w, u, v}
      (C : Type u)
      (A : C → Type v)
      (motive : W.{u, v} C A → Type w)
      (tree : (root : C) → (subtr : A root → W.{u, v} C A) → ((a : A root) → motive (subtr a)) → motive (W.tree.{u, v} C A root subtr))
      (t : W.{u, v} C A) :
      motive t :=
    W.rec.{w, u, v} C A motive tree t
)
