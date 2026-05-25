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

def chain (n : Nat) : (fun (x : Nat) => x) ((fun (y : Nat) => y) n) = n :=
  Eq.refl _ _
)

noDiagnostics
