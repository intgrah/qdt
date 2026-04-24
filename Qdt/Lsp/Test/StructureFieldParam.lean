import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval! test do

setText qdt!(
structure Foo : Type 1 where
--        ^
  (foo (bar : Type) : Type)
-- ^    ^     ^
)

noDiagnostics
hover ⟨1, 10⟩ "Foo : Type 1" ⟨1, 10⟩ ⟨1, 13⟩
hover ⟨3, 3⟩ "Foo.foo (self : Foo) (bar : Type) : Type" ⟨3, 3⟩ ⟨3, 6⟩
hover ⟨3, 8⟩ "bar : Type" ⟨3, 8⟩ ⟨3, 11⟩
hover ⟨3, 14⟩ "Type 1" ⟨3, 14⟩ ⟨3, 18⟩
