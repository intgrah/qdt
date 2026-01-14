import QdtTest.Macro

/-! ## Success tests -/

#pass (
  def id.{u} (A : Type u) (x : A) : A := x
)

#pass (
  def const.{u, v} (A : Type u) (B : Type v) (a : A) (_b : B) : A := a
)

#pass (
  def swap.{u, v} (A : Type u) (B : Type v) (f : A → B → A) (b : B) (a : A) : A := f a b
)

#pass (
  def arrow.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
)

#pass (
  def pi.{u, v} (A : Type u) (B : A → Type v) : Type (max u v) := (x : A) → B x
)

#pass (
  def typeU.{u} : Type (u + 1) := Type u
)

#pass (
  def typeMax.{u, v} : Type (max u v + 1) := Type (max u v)
)

#pass (
  def typeMax'.{u, v} : Type (max (u + 1) (v + 1)) := Type (max u v)
)

#pass (
  def typeU1.{u} : Type (u + 2) := Type (u + 1)
)

#pass (
  def type1 : Type 2 := Type 1
)

#pass (
  def typeArrow.{u, v} : Type (max (u + 1) (v + 1)) := Type u → Type v
)

#pass (
  def typeArrow'.{u, v} : Type (max u v + 1) := Type u → Type v
)

#pass (
  def endo.{u} : Type (u + 1) := Type u → Type u
)

#pass (
  def comp.{u, v, w} (A : Type u) (B : Type v) (C : Type w) (f : B → C) (g : A → B) : A → C := fun x => f (g x)
)

#pass (
  def maxComm1.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def maxComm2.{u, v} (A : Type u) (B : Type v) : Type (max v u) := A → B
)

#pass (
  def maxAssoc1.{u, v, w} (A : Type u) (B : Type v) (C : Type w) : Type (max (max u v) w) := A → B → C
  def maxAssoc2.{u, v, w} (A : Type u) (B : Type v) (C : Type w) : Type (max u (max v w)) := A → B → C
)

#pass (
  def maxIdem.{u} (A : Type u) : Type (max u u) := A
)

#pass (
  def maxZeroRight.{u} (A : Type u) : Type (max u 0) := A
  def maxZeroLeft.{u} (A : Type u) : Type (max 0 u) := A
)

#pass (
  def succMax1.{u, v} : Type (max u v + 1) := Type (max u v)
  def succMax2.{u, v} : Type (max (u + 1) (v + 1)) := Type (max u v)
)

#pass (
  def ChurchNat.{u} : Type (u + 1) := (A : Type u) → (A → A) → A → A
  def churchZero.{u} : ChurchNat.{u} := fun _ _ x => x
  def churchSucc.{u} (n : ChurchNat.{u}) : ChurchNat.{u} := fun A f x => f (n A f x)
)

#pass (
  def Cont.{u, v} (R : Type v) (A : Type u) : Type (max u v) := (A → R) → R
  def contPure.{u, v} (R : Type v) (A : Type u) (a : A) : Cont.{u, v} R A := fun k => k a
)

#pass (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def instArr12 : Type 2 := arr.{1, 2} (Type 0) (Type 1)
  def instArr21 : Type 2 := arr.{2, 1} (Type 1) (Type 0)
  def instArr11 : Type 1 := arr.{1, 1} (Type 0) (Type 0)
)

#pass (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def instParam.{u} : Type (u + 1) := arr.{u + 1, u + 1} (Type u) (Type u)
  def instTwoParams.{u, v} : Type (max (u + 1) (v + 1)) := arr.{u + 1, v + 1} (Type u) (Type v)
)

/-! ## Failure tests-/

#fail (
  def failUnder.{u, v} : Type u := Type (max u v)
) with .typeMismatch ..

#fail (
  def failOver.{u} : Type u := Type u → Type u
) with .typeMismatch ..

#fail (
  def failUnbound : Type 0 := Type v
) with .typeMismatch ..

#fail (
  def failTypeSelf.{u} : Type u := Type u
) with .typeMismatch ..

#fail (
  def failTypeSuccUnder.{u} : Type u := Type (u + 1)
) with .typeMismatch ..

#fail (
  def failTypeZero : Type 0 := Type 0
) with .typeMismatch ..

#fail (
  def id.{u} (A : Type u) (x : A) : A := x
  def failInstantiation.{u} : Type (u + 1) := id.{u, u} (Type u) (fun x => x)
) with .universeArgCountMismatch ..

#fail (
  def failMaxSucc.{u} : Type u := Type (max u (u + 1))
) with .typeMismatch ..

#fail (
  def failDupUniverseParam.{u, u} : Type (u + 1) := Type u
) with .duplicateUniverseParam ..

#fail (
  def failPiResult.{u} (A : Type u) : Type u := (a : A) → Type u
) with .typeMismatch ..

#fail (
  def failArrowMixed.{u, v} : Type (max u v) := Type u → Type v
) with .typeMismatch ..

#fail (
  def failDepArrowMixed.{u, v} (A : Type u) : Type (max u v) := (a : A) → Type v
) with .typeMismatch ..

#fail (
  def failArrowHighDomain.{u} : Type u := Type (u + 1) → Type u
) with .typeMismatch ..

#fail (
  def failArrowHighCodomain.{u} : Type u := Type u → Type (u + 1)
) with .typeMismatch ..

#fail (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def failInstTooMany.{u} : Type (u + 1) := arr.{u, u, u} (Type u) (Type u)
) with .universeArgCountMismatch ..

#fail (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def failInstTooFew.{u} : Type (u + 1) := arr.{u} (Type u) (Type u)
) with .universeArgCountMismatch ..

#fail (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def failInstParamWrong.{u} : Type u := arr.{u + 1, u + 1} (Type u) (Type u)
) with .typeMismatch ..

#fail (
  def arr.{u, v} (A : Type u) (B : Type v) : Type (max u v) := A → B
  def failInstUndeclared.{u} : Type (u + 1) := arr.{u + 1, v + 1} (Type u) (Type v)
) with .unboundUniverseVariable ..
