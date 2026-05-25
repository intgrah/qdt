import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
  | refl : Eq α a a
)

setText qdt!(
import Eq

def both.{u, v} (α : Type u) (β : Type v) (a : α) : Eq _ a a :=
  Eq.refl _ a
--  ^
)

noDiagnostics
hover ⟨3, 4⟩
  "both.{u, v} (α : Type u) (β : Type v) (a : α) : Eq.{u} α a a"
  ⟨3, 4⟩ ⟨3, 8⟩
