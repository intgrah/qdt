import Qdt.Lsp.Test

open Qdt.Lsp.Test
open Qdt

#eval test do
  setText "test.qdt" qdt!(
    def foo := Type
    def bar := foo
  )
  diagnostics "test.qdt" Array.isEmpty
  hover "test.qdt" ⟨1, 4⟩ "foo : Type 1"
  hover "test.qdt" ⟨2, 8⟩ "bar : Type 1"

  setText "test.qdt" qdt!(
    def bar := foo
    def foo := Type
  )
  diagnostics "test.qdt" (· matches #[⟨_, .unboundVariable ..⟩])
  noHover "test.qdt" ⟨1, 4⟩
  hover "test.qdt" ⟨2, 8⟩ "foo : Type 1"
