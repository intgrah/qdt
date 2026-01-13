import Qdt.Tele

namespace Qdt

open Lean (Name)

/-- de Bruijn indices -/
def Idx n := Fin n
deriving Repr, Hashable, DecidableEq, BEq

/-- Allow natural number literals to be used as de Bruijn indices -/
instance {n} [NeZero n] {i} : OfNat (Idx n) i where
  ofNat := Fin.ofNat n i

mutual

/-- Types -/
inductive Ty : Nat → Type
  | u {n} : Ty n
  | pi {n} : Param n → Ty (n + 1) → Ty n
  /-- If t : 𝑢, then El(t) type -/
  | el {n} : Tm n → Ty n
deriving Repr, Hashable, DecidableEq, BEq

inductive Tm : Nat → Type
  | var {n} : Idx n → Tm n
  | const {n} : Name → Tm n
  | lam {n} : Param n → Tm (n + 1) → Tm n
  | app {n} : Tm n → Tm n → Tm n
  | pi' {n} : Name → Tm n → Tm (n + 1) → Tm n
  | proj {n} : Nat → Tm n → Tm n
  | letE {n} : Name → Ty n → Tm n → Tm (n + 1) → Tm n
deriving Repr, Hashable, DecidableEq, BEq

@[pp_using_anonymous_constructor]
inductive Param : Nat → Type
  | mk {n} (name : Name) (ty : Ty n) : Param n
deriving Repr, Hashable, DecidableEq, BEq

end

notation "𝑢" => Ty.u

abbrev Ty.arrow {n} (ty : Ty n) := Ty.pi ⟨.anonymous, ty⟩

@[match_pattern]
def Tm.apps {n} : Tm n → List (Tm n) → Tm n :=
  List.foldl Tm.app

/- Point free! Point free! -/
def Ty.pis {a b} : Tele Param a b → Ty b → Ty a
  | .nil => id
  | .snoc bs param => pis bs ∘ pi param

def Tm.lams {a b} : Tele Param a b → Tm b → Tm a
  | .nil => id
  | .snoc bs param => lams bs ∘ lam param

end Qdt
