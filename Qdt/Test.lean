module

public import Qdt.Common
public import Qdt.Incremental.Rules

@[expose] public section

namespace Qdt.Test

open Qdt
open Incremental
open System (FilePath)
open Std (DHashMap)

opaque testBuild : Build config Input Qdt.tasks Id Id :=
  Shake config Input (fun _ => Hashable.toEmbedding) (fun _ => Hashable.toEmbedding) Qdt.tasks

def check (src : String) : IO (Array Diagnostic) := do
  let dummyPath : FilePath := "test.qdt"
  let inputs : DHashMap InputKey InputVal := DHashMap.emptyWithCapacity 4
  let inputs := inputs.insert (.text dummyPath) src
  let inputs := inputs.insert .inputFiles ({dummyPath} : Std.HashSet FilePath)
  let store := testBuild.init inputs
  let (diags, _) := StateT.run (s := store) <| testBuild.run (Key.checkFile dummyPath)

  return diags

def assertNoDiags (diags : Array Diagnostic) : IO Unit := do
  if !diags.isEmpty then
    throw (IO.userError s!"expected no errors, got: {diags.map (·.error)}")

def assertHasError (check : Error → Bool) (diags : Array Diagnostic) : IO Unit := do
  if diags.isEmpty then
    throw (IO.userError "expected error, got success")
  if !(diags.any (fun d => check d.error)) then
    throw (IO.userError s!"wrong error: {diags.map (·.error)}")

declare_syntax_cat qdtCmd
syntax command : qdtCmd
syntax "import " ident : qdtCmd

syntax "qdt!" "(" qdtCmd* ")" : term

macro_rules
  | `(qdt! ($[$cs:qdtCmd]*)) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `($(Lean.quote src))

syntax "#pass" "(" qdtCmd* ")" : command

macro_rules
  | `(command| #pass ($[$cs:qdtCmd]*)) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `(command| #eval! Qdt.Test.check $(Lean.quote src) >>= Qdt.Test.assertNoDiags)

syntax "#fail" "(" qdtCmd* ")" "with" term : command

macro_rules
  | `(command| #fail ($[$cs:qdtCmd]*) with $pat:term) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `(command| #eval! Qdt.Test.check $(Lean.quote src) >>= Qdt.Test.assertHasError (· matches $pat))

end Qdt.Test
