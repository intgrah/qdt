import QdtTest.Macro

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive T1 : Nat → Type where
    | z1 : T1
) with .expectedType ..

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive T1 : Nat → Type where
    | z1 : T1 Nat.zero
    | z2
) with .typeFamilyCtorReturnTypeRequired ..
