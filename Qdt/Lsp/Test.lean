module

public import Qdt.Lsp
public import Qdt.Test

@[expose] public section

namespace Qdt.Lsp.Test

open Qdt
open Incremental
open Incremental.Shake (Store Memo)
open Std (DHashMap HashSet)
open System (FilePath)

structure TestState where
  store : Store Key Val
  errors : Array String := #[]

abbrev TestM := StateRefT TestState IO

def test (action : TestM Unit) : IO Unit := do
  let check : TestM Unit := do
    action
    let errors := (← get).errors
    if !errors.isEmpty then
      throw (IO.userError ("\n".intercalate errors.toList))
  check.run' { store := DHashMap.emptyWithCapacity 64 }

def fail (msg : String) : TestM Unit :=
  modify fun st => { st with errors := st.errors.push msg }

def setText (text : String) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let store := (← get).store
  let memo : Memo Key Val (.text filepath) := { value := text, deps := ∅ }
  let store := store.insert (.text filepath) memo
  let inputFiles : HashSet FilePath :=
    match store.get? .inputFiles with
    | some (m : Memo Key Val .inputFiles) => m.value.insert filepath
    | none => {filepath}
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅ }
  let store := store.insert .inputFiles inputMemo
  match Shake.build tasks (Key.checkFile filepath) store with
  | .ok (_, store) => modify fun st => { st with store }
  | .error .cycle => throw (IO.userError "cycle detected")
  | .error .missingInput => throw (IO.userError "missing input")

def diagnostics (check : Array Diagnostic → Bool) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let diags := match (← get).store.get? (Key.checkFile filepath) with
    | some memo => memo.value
    | none => #[]
  if !check diags then
    fail s!"diagnostics check failed: {diags.map (·.error)}"

def noDiagnostics (filepath : FilePath := "test.qdt") : TestM Unit :=
  diagnostics Array.isEmpty filepath

def hover (pos : Lean.Position) (expected : String) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let store := (← get).store
  let text := match store.get? (Key.text filepath) with
    | some memo => memo.value
    | none => ""
  match elaborateFile store filepath with
  | none => fail s!"no elaboration info for {filepath}"
  | some (info, sourceMap, cst) =>
    let bytePos := (Lean.FileMap.ofString text).ofPosition pos
    let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
    match lookupHoverAtPosition cst sourceMap info codepointPos with
    | none => fail s!"no hover at {repr pos}, expected '{expected}'"
    | some content =>
      let formatted := content.format
      if formatted != expected then
        fail s!"hover mismatch at {repr pos}: expected '{expected}', got '{formatted}'"

def noHover (pos : Lean.Position) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let store := (← get).store
  let text := match store.get? (Key.text filepath) with
    | some memo => memo.value
    | none => ""
  match elaborateFile store filepath with
  | none => return
  | some (info, sourceMap, cst) =>
    let bytePos := (Lean.FileMap.ofString text).ofPosition pos
    let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
    match lookupHoverAtPosition cst sourceMap info codepointPos with
    | none => return
    | some content =>
      fail s!"expected no hover at {repr pos}, got '{content.format}'"

end Qdt.Lsp.Test
