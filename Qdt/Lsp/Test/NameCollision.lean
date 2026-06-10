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
)

diagnostics (filepath := "C.qdt") fun ds =>
  ds.any fun d => d.error matches .duplicateImport ..
