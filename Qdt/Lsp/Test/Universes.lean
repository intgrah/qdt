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

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

--  v
def pair.{u, v} (α : Type u) (β : Type v) (a : α) (b : β) : a = a :=
  Eq.refl a
)

noDiagnostics
hover ⟨4, 4⟩
  "pair.{u, v} (α : Type u) (β : Type v) (a : α) (b : β) : Eq.{u} α a a"
  ⟨4, 4⟩ ⟨4, 8⟩

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

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

inductive List.{u} (α : Type u) : Type u where
  | nil
  | cons (head : α) (tail : List α)

def listEq.{u} (α : Type u) (l : List α) : l = l := Eq.refl _
--  ^
)

noDiagnostics
hover ⟨7, 4⟩
  "listEq.{u} (α : Type u) (l : List.{u} α) : Eq.{u} (List.{u} α) l l"
  ⟨7, 4⟩ ⟨7, 10⟩

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

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

inductive Wrap.{u} (α : Type u) : Type u where
  | mk (a : α)

--  v
def wrapRefl.{u} (α : Type u) (x : α) : Wrap.mk x = Wrap.mk x :=
  Eq.refl _
)

noDiagnostics
hover ⟨7, 4⟩
  "wrapRefl.{u} (α : Type u) (x : α) : Eq.{u} (Wrap.{u} α) (Wrap.mk.{u} α x) (Wrap.mk.{u} α x)"
  ⟨7, 4⟩ ⟨7, 12⟩

#eval! test do

setText (filepath := "Eq.qdt") qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a
)

setText qdt!(
import Eq

inductive Box.{u} (α : Type u) : Type u where
  | mk (a : α)

--  v
def Box.lift.{u} (α : Type u) (x : α) : Box α :=
  Box.mk x

def Box.eq.{u} (α : Type u) (x : α) : Box.mk x = Box.mk x :=
  Eq.refl _
)

noDiagnostics
hover ⟨7, 4⟩
  "Box.lift.{u} (α : Type u) (x : α) : Box.{u} α"
  ⟨7, 4⟩ ⟨7, 12⟩
hover ⟨10, 4⟩
  "Box.eq.{u} (α : Type u) (x : α) : Eq.{u} (Box.{u} α) (Box.mk.{u} α x) (Box.mk.{u} α x)"
  ⟨10, 4⟩ ⟨10, 10⟩
