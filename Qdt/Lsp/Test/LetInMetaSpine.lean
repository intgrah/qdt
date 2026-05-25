import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
  | refl : Eq α a a
)

setText qdt!(
import Eq

inductive Nat where
  | zero
  | succ (n : Nat)

def Nat.add (m n : Nat) : Nat :=
  Nat.rec _ m (fun _ k => Nat.succ k) n

def myLemma (n : Nat) : Nat.add n n = Nat.add n n :=
  let m := Nat.add n;
  Eq.refl _ (m n)
)

noDiagnostics
