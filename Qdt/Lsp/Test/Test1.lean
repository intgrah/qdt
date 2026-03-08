import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval test do

setText qdt!(
def foo := Type
def bar := foo
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1"
hover ⟨2, 4⟩ "bar : Type 1"

setText qdt!(
def bar := foo
def foo := Type
)

diagnostics (· matches #[⟨_, .unboundVariable ..⟩])
noHover ⟨1, 4⟩
hover ⟨2, 4⟩ "foo : Type 1"
