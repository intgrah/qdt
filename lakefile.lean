import Lake

open System Lake DSL

package qdt where
  version := v!"0.1.0"
  testDriver := "Qdt.Test"
  description := "Query-based Dependent Type Elaborator"
  license := "Apache-2.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require "leanprover-community" / mathlib @ git "v4.28.0"

lean_lib FSWatch
lean_lib Incremental
lean_lib Qdt
lean_lib Qdt.Test where
  globs := #[`Qdt.Test.*, `Qdt.Lsp.Test.*]

@[default_target]
lean_exe qdt where root := `Main
lean_exe «qdt-lsp» where root := `Lsp

def buildCObj (pkg : Package) (src : FilePath) : FetchM (Job FilePath) := do
  let oFile := pkg.buildDir / "c" / src.withExtension "o"
  let srcJob ← inputTextFile <| pkg.dir / src
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O3"] "cc" getLeanTrace

extern_lib libleanfswatch pkg := do
  let srcs : Array FilePath := #["FSWatch/c/inotify.c", "FSWatch/c/rdcw.c"]
  let objs ← srcs.mapM (buildCObj pkg)
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanfswatch") objs

extern_lib libleanshake pkg := do
  let srcs : Array FilePath := #["Incremental/c/shake.c"]
  let objs ← srcs.mapM (buildCObj pkg)
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leanshake") objs
