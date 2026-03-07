import Lake

open System Lake DSL

package qdt where
  testDriver := "QdtTest"
  version := v!"0.1.0"
  description := "Query-based Dependent Type Elaborator"
  license := "Apache-2.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / mathlib @ git "v4.28.0"

lean_lib FSWatch

lean_lib Incremental

lean_lib Qdt

lean_lib QdtTest where globs := #[`QdtTest.+]

@[default_target] lean_exe qdt where root := `Main

lean_exe «qdt-lsp» where root := `Qdt.Lsp.Main

lean_exe «test-parser» where root := `TestParser

target inotify.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "inotify.o"
  let srcJob ← inputTextFile <| pkg.dir / "FSWatch" / "c" / "inotify.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

target rdcw.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "rdcw.o"
  let srcJob ← inputTextFile <| pkg.dir / "FSWatch" / "c" / "rdcw.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "cc" getLeanTrace

extern_lib libleanfswatch pkg := do
  let inotify ← inotify.o.fetch
  let rdcw ← rdcw.o.fetch
  let name := nameToStaticLib "leanfswatch"
  buildStaticLib (pkg.staticLibDir / name) #[inotify, rdcw]
