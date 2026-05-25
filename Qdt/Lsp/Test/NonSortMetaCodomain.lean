import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} (α : Type u) (a : α) : α → Type u where
  | refl : Eq α a a
)

setText qdt!(
import Eq

inductive Wrap.{u} (α : Type u) : Type u where
  | mk (a : α)

def wrapRefl.{u} (α : Type u) (x : α) : Wrap.mk _ x = Wrap.mk _ x :=
  Eq.refl _ _
--  ^
)

noDiagnostics
hover ⟨6, 4⟩
  "wrapRefl.{u} (α : Type u) (x : α) : Eq.{u} (Wrap.{u} α) (Wrap.mk.{u} α x) (Wrap.mk.{u} α x)"
  ⟨6, 4⟩ ⟨6, 12⟩
