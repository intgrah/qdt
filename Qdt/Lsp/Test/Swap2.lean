import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval test do

setText qdt!(
def foo : Type 1 := Type
def bar : Type 1 := foo
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1"
hover ⟨2, 4⟩ "bar : Type 1"

setText qdt!(
def bar : Type 1 := foo
def foo : Type 1 := Type
)

diagnostics (· matches #[⟨_, .unboundVariable ..⟩])
hover ⟨1, 4⟩ "bar : Type 1"
hover ⟨2, 4⟩ "foo : Type 1"
