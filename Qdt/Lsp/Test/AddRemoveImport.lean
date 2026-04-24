import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "A.qdt") qdt!(
def foo := Type
)

setText (filepath := "B.qdt") qdt!(
def bar := foo
)

diagnostics (filepath := "B.qdt") (· matches #[⟨_, .unboundVariable `foo⟩])

setText (filepath := "B.qdt") qdt!(
import A
def bar := foo
--  ^
)

noDiagnostics (filepath := "B.qdt")
hover (filepath := "B.qdt") ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩

setText (filepath := "B.qdt") qdt!(
def bar := foo
)

diagnostics (filepath := "B.qdt") (· matches #[⟨_, .unboundVariable `foo⟩])
