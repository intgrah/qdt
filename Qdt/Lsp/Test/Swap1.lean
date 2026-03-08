import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval test do

setText qdt!(
def foo := Type
--  ^
def bar := foo
--  ^
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1" ⟨1, 4⟩ ⟨1, 7⟩
hover ⟨3, 4⟩ "bar : Type 1" ⟨3, 4⟩ ⟨3, 7⟩

setText qdt!(
def bar := foo
--  ^
def foo := Type
--  ^
)

diagnostics (· matches #[⟨_, .unboundVariable `foo⟩])
noHover ⟨1, 4⟩
hover ⟨3, 4⟩ "foo : Type 1" ⟨3, 4⟩ ⟨3, 7⟩
