import Qdt.Lsp.Test

open Qdt.Lsp.Test
open Qdt

#eval test do
  setText "test.qdt" qdt!(
    def foo : Type 1 := Type
    def bar : Type 1 := foo
  )
  diagnostics "test.qdt" Array.isEmpty
  hover "test.qdt" ⟨1, 4⟩ "foo : Type 1"
  hover "test.qdt" ⟨2, 8⟩ "bar : Type 1"

  setText "test.qdt" qdt!(
    def bar : Type 1 := foo
    def foo : Type 1 := Type
  )
  diagnostics "test.qdt" (· matches #[⟨_, .unboundVariable ..⟩])
  hover "test.qdt" ⟨1, 4⟩ "bar : Type 1"
  hover "test.qdt" ⟨2, 8⟩ "foo : Type 1"
