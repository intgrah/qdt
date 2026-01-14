import QdtTest.Macro

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive Contra (A : Type) where
    | mk (f : A → Nat) : Contra A

  inductive Bad where
    | wrap (c : Contra Bad) : Bad
) with .nonPositiveOccurrence ..

#fail (
  inductive Bad where
    | mk (f : Bad → Bad) : Bad
) with .nonPositiveOccurrence ..

#fail (
  inductive Endo (A : Type) where
    | mk (f : A → A) : Endo A

  inductive Bad where
    | mk (e : Endo Bad) : Bad
) with .nonPositiveOccurrence ..

#fail (
  structure Bad where
    (f : Bad → Bad)
) with .nonPositiveOccurrence ..

#fail (
  inductive Nat where
    | zero
    | succ (n : Nat)

  inductive Contra (A : Type) where
    | mk (f : A → Nat)

  structure Bad where
    (c : Contra Bad)
) with .nonPositiveOccurrence ..

#fail (
  inductive Endo (A : Type) where
    | mk (f : A → A)

  structure Bad where
    (e : Endo Bad)
) with .nonPositiveOccurrence ..

#fail (
  inductive Fix (F : Type → Type) where
    | mk : F (Fix F) → Fix F
) with .nonPositiveOccurrence ..
