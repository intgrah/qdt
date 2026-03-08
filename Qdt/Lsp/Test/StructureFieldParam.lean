import Qdt.Lsp.Test

open Qdt.Lsp.Test

#eval test do

setText qdt!(
structure Foo : Type 1 where
  (foo (bar : Type) : Type)
)

noDiagnostics
hover ⟨1, 10⟩ "Foo : Type 1"
hover ⟨2, 3⟩ "Foo.foo (self : Foo) (bar : Type) : Type"
hover ⟨2, 8⟩ "bar : Type"
hover ⟨2, 14⟩ "Type 1"
