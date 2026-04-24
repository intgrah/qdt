import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
def foo : Type 1 := Type
--  ^
def bar : Type 1 := foo
--  ^
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1" ⟨1, 4⟩ ⟨1, 7⟩
hover ⟨3, 4⟩ "bar : Type 1" ⟨3, 4⟩ ⟨3, 7⟩

setText qdt!(
def foo : Type 1 := (fun (A : Type 1) => A) Type
--  ^
def bar : Type 1 := foo
--  ^
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1" ⟨1, 4⟩ ⟨1, 7⟩
hover ⟨3, 4⟩ "bar : Type 1" ⟨3, 4⟩ ⟨3, 7⟩
