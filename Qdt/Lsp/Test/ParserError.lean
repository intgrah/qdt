import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText "def foo := !!!\ndef bar := Type\n"

diagnostics (fun ds => ds.any (·.error matches .syntaxError _))
hover ⟨2, 4⟩ "bar : Type 1" ⟨2, 4⟩ ⟨2, 7⟩
