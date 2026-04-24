import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText (filepath := "A.qdt") qdt!(
import B
def a := Type
)

setText (filepath := "B.qdt") qdt!(
import A
def b := Type
)

noDiagnostics (filepath := "A.qdt")
noDiagnostics (filepath := "B.qdt")
