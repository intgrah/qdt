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

setText (filepath := "A.qdt") qdt!()

setText (filepath := "B.qdt") qdt!(
def foo := Type
def bar := foo
--  ^
)

noDiagnostics (filepath := "A.qdt")
noDiagnostics (filepath := "B.qdt")
hover (filepath := "B.qdt") ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩
