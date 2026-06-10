import Qdt.Test

#pass (
  inductive Eq3.{u} {α : Type u} : α → α → α → Type u where
    | refl (a : α) : Eq3 a a a

  def rec.{w, u}
      (A : Type u)
      (x : A)
      (motive : (y z : A) → Eq3.{u} x y z → Type w)
      (refl : motive x x (Eq3.refl.{u} x))
      (y z : A)
      (t : Eq3.{u} x y z) :
      motive y z t :=
    @Eq3.rec.{w, u} A x motive refl y z t
)
