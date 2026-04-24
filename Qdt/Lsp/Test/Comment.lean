import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
def foo := Type
def bar := foo
--  ^
)

noDiagnostics
hover ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩

setText qdt!(
-- def foo := Type
def bar := foo
)

diagnostics (· matches #[⟨_, .unboundVariable `foo⟩])

setText qdt!(
def foo := Type
def bar := foo
--  ^
)

noDiagnostics
hover ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩
