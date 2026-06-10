import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

--  v
def both.{u, v} (α : Type u) (β : Type v) (a : α) : Eq a a :=
  Eq.refl a
)

noDiagnostics
hover ⟨4, 4⟩
  "both.{u, v} (α : Type u) (β : Type v) (a : α) : Eq.{u} α a a"
  ⟨4, 4⟩ ⟨4, 8⟩
