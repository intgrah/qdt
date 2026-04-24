import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "A.qdt") qdt!(
def foo := Type
)

setText (filepath := "B.qdt") qdt!(
import A
def bar := foo
--  ^
)

noDiagnostics (filepath := "A.qdt")
noDiagnostics (filepath := "B.qdt")
hover (filepath := "B.qdt") ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩

setText (filepath := "A.qdt") qdt!(
def foo := Type 1
)

noDiagnostics (filepath := "A.qdt")
noDiagnostics (filepath := "B.qdt")
hover (filepath := "B.qdt") ⟨2, 4⟩ "bar : Type 2" ⟨2, 4⟩ ⟨2, 7⟩
