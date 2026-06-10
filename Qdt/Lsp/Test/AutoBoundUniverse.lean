import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

inductive Unit.{u} : Type u where
  | unit

--  v
def Unit.eta (t : Unit) : Unit.unit = t := @Eq.refl _ _
)

noDiagnostics
hover ⟨7, 4⟩
  "Unit.eta.{u_1} (t : Unit.{u_1}) : Eq.{u_1} Unit.{u_1} Unit.unit.{u_1} t"
  ⟨7, 4⟩ ⟨7, 12⟩
