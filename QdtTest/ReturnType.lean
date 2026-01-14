import QdtTest.Macro

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive Foo : Type where
    | bar : Nat
) with .ctorMustReturnInductive ..

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive T1 : Nat → Type where
    | z1 : T1
) with .expectedType ..
