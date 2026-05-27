import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
  | refl : Eq α a a
)

setText qdt!(
import Eq

inductive Box.{u} (α : Type u) : Type u where
  | mk (a : α)

def Box.lift.{u} (α : Type u) (x : α) : Box α :=
  Box.mk _ x
--  ^

def Box.eq.{u} (α : Type u) (x : α) : Box.mk _ x = Box.mk _ x :=
  Eq.refl _ _
)

noDiagnostics
hover ⟨6, 4⟩
  "Box.lift.{u} (α : Type u) (x : α) : Box.{u} α"
  ⟨6, 4⟩ ⟨6, 12⟩
hover ⟨10, 4⟩
  "Box.eq.{u} (α : Type u) (x : α) : Eq.{u} (Box.{u} α) (Box.mk.{u} α x) (Box.mk.{u} α x)"
  ⟨10, 4⟩ ⟨10, 10⟩
