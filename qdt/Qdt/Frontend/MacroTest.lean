import Qdt.Frontend.Macro

namespace Qdt.Frontend.Macro

#eval qdt_cst! Nat.succ 0
#eval qdt_cst! Type
#eval qdt_cst! (a : A)
#eval qdt_cst! fun x => x
#eval qdt_cst! fun x y : Nat => x
#eval qdt_cst! fun _ _ : Nat => 0
#eval qdt_cst! (x : Nat) -> Nat
#eval qdt_cst! ∀ x : Nat, Nat
#eval qdt_cst! ∀ (x y : Nat), Nat
#eval qdt_cst! let x := 0; x
#eval qdt_cst! let x : Nat := 0; x
#eval qdt_cst! (0, 1)
#eval qdt_cst! a = b
#eval qdt_cst! a + b
#eval qdt_cst! a * b
#eval qdt_cst! a × b

#eval qdt_cmd! (
def add (m n : Nat) : Nat := m
)
#eval qdt_cmd! (
axiom add (m n : Nat) : Nat
)
#eval qdt_cmd! (
example (n : Nat) : Nat := n
)

#eval qdt_cmd! (
inductive Foo where
  | mk (n : Nat) : Foo
)

#eval qdt_cmd! (
structure Foo (A : Type) where
  (foo (m n : Nat) : A)
  (bar : A)
)

#eval qdt_prog! (
inductive Nat where
  | zero
  | succ : Nat -> Nat

def Nat.add (m : Nat) := Nat.rec (fun _ => Nat) m (fun _ => Nat.succ)
def Nat.mul (m : Nat) := Nat.rec (fun _ => Nat) 0 (fun _ => Nat.add m)
def Nat.pow (m : Nat) := Nat.rec (fun _ => Nat) 1 (fun _ => Nat.mul m)

def Nat.triangle := Nat.rec (fun _ => Nat) 0 (fun k => Nat.add (Nat.succ k))
def Nat.factorial := Nat.rec (fun _ => Nat) 1 (fun k => Nat.mul (Nat.succ k))

def Nat.pred : Nat → Nat := Nat.rec (fun _ => Nat) 0 (fun k _ => k)
def Nat.sub (m : Nat) := Nat.rec (fun _ => Nat) m (fun _ => Nat.pred)

example : Nat.add 2 3 = 5 := Eq.refl Nat 5
example : Nat.mul 2 3 = 6 := Eq.refl Nat 6
example : Nat.pow 3 2 = 9 := Eq.refl Nat 9
example : Nat.triangle 3 = 6 := Eq.refl Nat 6
example : Nat.factorial 3 = 6 := Eq.refl Nat 6

example : Nat.pred 3 = 2 := Eq.refl Nat 2
example : Nat.pred 0 = 0 := Eq.refl Nat 0
example : Nat.sub 3 2 = 1 := Eq.refl Nat 1
example : Nat.sub 0 1 = 0 := Eq.refl Nat 0
)

end Qdt.Frontend.Macro
