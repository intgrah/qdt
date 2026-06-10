import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

def reflect.{u} (α : Type u) (x : α) : x = x := Eq.refl _
--  ^
)

noDiagnostics
hover ⟨3, 4⟩
  "reflect.{u} (α : Type u) (x : α) : Eq.{u} α x x"
  ⟨3, 4⟩ ⟨3, 11⟩
