module

public import Qdt
public import Qdt.Incremental.Rules
public import Incremental.Basic

namespace Qdt.Test

open Qdt
open Incremental
open Incremental.Shake (Store Memo)
open System (FilePath)
open Std (DHashMap)

def check (src : String) : IO (Array Diagnostic) := do
  let dummyPath : FilePath := "test.qdt"
  let memo : Memo Key Val (.text dummyPath) := { value := src, deps := ∅ }
  let inputFiles : Std.HashSet System.FilePath := {dummyPath}
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅ }
  let store : Store Key Val := DHashMap.emptyWithCapacity 64
  let store := store.insert (.text dummyPath) memo
  let store := store.insert .inputFiles inputMemo

  match Shake.build tasks (Key.checkFile dummyPath) store with
  | .ok (diags, _) => return diags
  | .error .cycle => return #[⟨[], .msg "cycle detected"⟩]
  | .error .missingInput => return #[⟨[], .msg "missing input"⟩]

def assertNoDiags (diags : Array Diagnostic) : IO Unit := do
  if !diags.isEmpty then
    throw (IO.userError s!"expected no errors, got: {diags.map (·.error)}")

def assertHasError (check : Error → Bool) (diags : Array Diagnostic) : IO Unit := do
  if diags.isEmpty then
    throw (IO.userError "expected error, got success")
  if !(diags.any (fun d => check d.error)) then
    throw (IO.userError s!"wrong error: {diags.map (·.error)}")

syntax "qdt!" "(" command* ")" : term

macro_rules
  | `(qdt! ($[$cs:command]*)) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `($(Lean.quote src))

syntax "#pass" "(" command* ")" : command

macro_rules
  | `(command| #pass ($[$cs:command]*)) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `(command| #eval Qdt.Test.check $(Lean.quote src) >>= Qdt.Test.assertNoDiags)

syntax "#fail" "(" command* ")" "with" term : command

macro_rules
  | `(command| #fail ($[$cs:command]*) with $pat:term) => do
    let src := String.join (cs.toList.filterMap (·.raw.reprint))
    `(command| #eval Qdt.Test.check $(Lean.quote src) >>= Qdt.Test.assertHasError (· matches $pat))

end Qdt.Test
