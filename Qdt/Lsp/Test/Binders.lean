import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
structure S.{u} (T : Type u) (P : T → Type u) : Type u where
  (law (x : _) : P x)
)

noDiagnostics
hover ⟨2, 8⟩ "x : T" ⟨2, 8⟩ ⟨2, 9⟩

#eval! test do

setText qdt!(
inductive Eq.{u} {α : Type u} : α → α → Type u where
  | refl (a : α) : Eq a a

def rfl.{u} {α : Type u} {a : α} : a = a := Eq.refl a

inductive List.{u} (α : Type u) : Type u where
  | nil
  | cons (h : α) (t : List α)

def List.append.{u} {α : Type u} (xs ys : List α) : List α :=
  List.rec ys (fun h _ => List.cons h) xs

def List.flatten.{u} {α : Type u} : List (List α) → List α :=
  List.rec List.nil (fun xs _ => List.append xs)

def probe.{u} {α : Type u} (xss yss : List (List α)) :
    List.flatten (List.append xss yss) = List.append (List.flatten xss) (List.flatten yss) :=
  @List.rec
    _
    (fun zss =>
      List.flatten (List.append zss yss) = List.append (List.flatten zss) (List.flatten yss))
    rfl
    sorry
    xss
)

hover ⟨21, 32⟩ "zss : List.{u} (List.{u} α)" ⟨21, 32⟩ ⟨21, 35⟩
