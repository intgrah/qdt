import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
def foo : Type := _
--                ^
)

diagnostics (· matches #[⟨_, .unsolvedMetavariable .., _⟩])
hover ⟨1, 18⟩ "Type" ⟨1, 18⟩ ⟨1, 19⟩

setText qdt!(
def id.{u} (α : Type u) (a : α) : α := a
example (T : Type 1) (x : T) : T := id _ x
--                                     ^
)

noDiagnostics
hover ⟨2, 39⟩ "T : Type 1" ⟨2, 39⟩ ⟨2, 40⟩

setText qdt!(
inductive Bool where
  | true
  | false
def id.{u} (α : Type u) (a : α) : α := a
example (b : Bool) : Bool := id _ b
--                              ^
)

noDiagnostics
hover ⟨5, 32⟩ "Bool : Type" ⟨5, 32⟩ ⟨5, 33⟩
