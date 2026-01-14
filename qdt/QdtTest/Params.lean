import QdtTest.Macro

#fail (
  inductive Bool where
    | true
    | false

  inductive BadParamInd (A : Type) (n : Bool) : Type where
    | mk : BadParamInd A Bool.true
) with .ctorParamMismatch ..

#fail (
  inductive Bool where
    | true
    | false

  inductive BadParamArg (A : Type) (n : Bool) : Type where
    | mk : BadParamArg A Bool.true → BadParamArg A n
) with .ctorParamMismatch ..

#fail (
  inductive T (A : Type) where
    | mk : T → T A
) with .expectedType ..

#fail (
  structure T (A : Type) where
    (val : T)
) with .expectedType ..

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  structure BadParamStruct (A : Type) (n : Nat) where
    (val : BadParamStruct A Nat.zero)
) with .ctorParamMismatch ..
