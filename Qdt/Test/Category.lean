import Qdt.Test

#pass (
  structure S.{v, u} (Ob : Type u) : Type (max u (v + 1)) where
    (Hom : Ob → Ob → Type v)
    (id (A : Ob) : Hom A A)

  def S.Types.{u} : S (Type u) :=
    S.mk (fun A B => A → B) (fun A a => a)
)
