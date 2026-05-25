import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
  | refl : Eq α a a
)

setText qdt!(
import Eq

inductive List.{u} (α : Type u) : Type u where
  | nil
  | cons (head : α) (tail : List α)

def listEq.{u} (α : Type u) (l : List α) : l = l := Eq.refl _ _
--  ^
)

noDiagnostics
hover ⟨7, 4⟩
  "listEq.{u} (α : Type u) (l : List.{u} α) : Eq.{u} (List.{u} α) l l"
  ⟨7, 4⟩ ⟨7, 10⟩
