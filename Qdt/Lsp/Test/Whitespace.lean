import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
def foo := Type
--  ^
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1" ⟨1, 4⟩ ⟨1, 7⟩

setText "\n\n  def  foo  :=  Type\n--     ^\n\n"

noDiagnostics
hover ⟨3, 7⟩ "foo : Type 1" ⟨3, 7⟩ ⟨3, 10⟩
