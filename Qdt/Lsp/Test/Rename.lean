import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "A.qdt") qdt!(
def foo := Type
)

setText (filepath := "B.qdt") qdt!(
import A
def bar := foo
)

noDiagnostics (filepath := "B.qdt")

setText (filepath := "A.qdt") qdt!(
def renamed := Type
)

diagnostics (filepath := "B.qdt") (· matches #[⟨_, .unboundVariable `foo⟩])
