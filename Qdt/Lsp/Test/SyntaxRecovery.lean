import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText "def foo := !!!\n"

diagnostics (fun ds => ds.any (·.error matches .syntaxError _))

setText qdt!(
def foo := Type
--  ^
)

noDiagnostics
hover ⟨1, 4⟩ "foo : Type 1" ⟨1, 4⟩ ⟨1, 7⟩
