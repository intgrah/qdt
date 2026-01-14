import QdtTest.Macro

open Qdt

#pass (
  def foo : Type 1 := Type
)

#pass (
  def id (A : Type) (x : A) : A := x
)

#fail (
  def foo : Type := bar
) with .unboundVariable ..

#fail (
  def foo : Type := Type
) with .typeMismatch ..

#fail (
  def foo : Type u := Type
) with .unboundUniverseVariable ..
