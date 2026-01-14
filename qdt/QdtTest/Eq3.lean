import QdtTest.Macro

#pass (
  inductive Eq3.{u} (A : Type u) (x : A) : A → A → Type u where
    | refl : Eq3 A x x x

  def rec.{w, u}
      (A : Type u)
      (x : A)
      (motive : (y z : A) → Eq3.{u} A x y z → Type w)
      (refl : motive x x (Eq3.refl.{u} A x))
      (y z : A)
      (t : Eq3.{u} A x y z) :
      motive y z t :=
    Eq3.rec.{w, u} A x motive refl y z t
)
