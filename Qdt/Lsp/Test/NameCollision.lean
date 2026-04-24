import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "A.qdt") qdt!(
def foo := Type
)

setText (filepath := "B.qdt") qdt!(
def foo := Type 1
)

setText (filepath := "C.qdt") qdt!(
import A
import B
def bar := foo
--  ^
)

noDiagnostics (filepath := "C.qdt")
hover (filepath := "C.qdt") ⟨3, 4⟩ "bar : Type 1" ⟨3, 4⟩ ⟨3, 7⟩
