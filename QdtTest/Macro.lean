import Qdt
import Qdt.Incremental.Rules
import Incremental.Basic

open Qdt
open Incremental
open Incremental.Shake (Store Memo)
open Lean (Term MacroM)
open System (FilePath)
open Std (DHashMap)

def elabProgFromString (src : String) : IO (Array Diagnostic × Global) := do
  let dummyPath : FilePath := "test.qdt"
  let memo : Memo Key Val (.text dummyPath) := { value := src, deps := ∅ }
  let inputFiles : Std.HashSet System.FilePath := {dummyPath}
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅ }
  let store : Store Key Val := DHashMap.emptyWithCapacity 64
  let store := store.insert (.text dummyPath) memo
  let store := store.insert .inputFiles inputMemo

  match Shake.build tasks (Key.checkFile dummyPath) store with
  | .ok (diags, _) => return (diags, ∅)
  | .error .cycle => return (#[{ path := [], error := .msg "cycle detected" }], ∅)
  | .error .missingInput => return (#[{ path := [], error := .msg "missing input" }], ∅)

def shouldPass (src : String) : IO Unit := do
  let (diagnostics, _) ← elabProgFromString src
  match diagnostics[0]? with
  | none => return
  | some err =>
    throw (IO.userError s!"expected success, got: {err.error}")

def shouldFail (check : Error → Bool) (src : String) : IO Unit := do
  let (diagnostics, _) ← elabProgFromString src
  match diagnostics[0]? with
  | none =>
    throw (IO.userError "expected error, got success")
  | some err =>
    let err := err.error
    if !check err then throw (IO.userError s!"wrong error: {err}")

/--
`#pass (prog)` expects `prog` to elaborate successfully.
-/
syntax "#pass" "(" command* ")" : command

macro_rules
  | `(command| #pass ($[$cs:command]*)) => do
      let src := String.intercalate "\n" (cs.toList.map (·.raw.prettyPrint.pretty))
      `(command| #eval shouldPass $(Lean.quote src))

/--
`#fail (prog) with pat` expects `prog` to fail with
an error matching `pat`.
-/
syntax "#fail" "(" command* ")" "with" term : command

macro_rules
  | `(command| #fail ($[$cs:command]*) with $pat:term) => do
      let src := String.intercalate "\n" (cs.toList.map (·.raw.prettyPrint.pretty))
      `(command| #eval shouldFail (· matches $pat) $(Lean.quote src))
