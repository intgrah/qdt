import QdtTest.Macro

#pass (
  inductive Acc.{u, v} (A : Type u) (r : A → A → Type v) : A → Type (max u v) where
    | intro (x : A) (h : (y : A) → r y x → Acc A r y) : Acc A r x

  def rec.{w, u, v}
      (A : Type u)
      (r : A → A → Type v)
      (motive : (a : A) → Acc.{u, v} A r a → Type w)
      (intro : (x : A) → (h : (y : A) → r y x → Acc.{u, v} A r y) → ((y : A) → (a : r y x) → motive y (h y a)) → motive x (Acc.intro.{u, v} A r x h))
      (a : A)
      (t : Acc.{u, v} A r a) :
      motive a t :=
    Acc.rec.{w, u, v} A r motive intro a t
)
