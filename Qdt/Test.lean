module

public import Qdt.Common
public import Qdt.Incremental.Rules
public import Qdt.Frontend.Parser
public import Qdt.Frontend.Format
import Incremental.Shake.Standard

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
  let inputs := inputs.insert .inputFiles ((∅ : Std.HashMap FilePath FilePath).insert dummyPath dummyPath)
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

def stripTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then s.dropEnd 1 |>.toString else s

def renderSource (src : String) (width : Nat) : IO String := do
  let (cst, errs) := Frontend.Parser.parse src
  unless errs.isEmpty do
    throw (IO.userError s!"parse error in {repr src}: {errs.map (·.msg)}")
  return stripTrailingNewline (Frontend.Format.render cst width)

def assertFmt (input expected : String) (width : Nat := 100) : IO Unit := do
  let out ← renderSource input width
  unless out == expected do
    throw (IO.userError
      s!"format mismatch\n  input:    {repr input}\n  expected: {repr expected}\n  actual:   {repr out}")
  let out' ← renderSource expected width
  unless out' == expected do
    throw (IO.userError
      s!"not idempotent\n  expected: {repr expected}\n  reformat: {repr out'}")

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

declare_syntax_cat fmtArg
syntax "(" qdtCmd* ")" : fmtArg
syntax str : fmtArg

syntax "#fmt" fmtArg "↦" fmtArg : command

meta def fmtArgToString : Lean.TSyntax `fmtArg → Lean.MacroM String
  | `(fmtArg| ($[$cs:qdtCmd]*)) =>
      return (String.join (cs.toList.filterMap (·.raw.reprint))).trimAscii.toString
  | `(fmtArg| $s:str) => return s.getString
  | _ => Lean.Macro.throwUnsupported

macro_rules
  | `(command| #fmt $i:fmtArg ↦ $o:fmtArg) => do
    let iStr ← fmtArgToString i
    let oStr ← fmtArgToString o
    `(command| #eval! Qdt.Test.assertFmt $(Lean.quote iStr) $(Lean.quote oStr))

end Qdt.Test
