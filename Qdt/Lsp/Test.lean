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

abbrev TestM := StateRefT (Store Key Val) IO

def test (action : TestM Unit) : IO Unit :=
  action.run' (DHashMap.emptyWithCapacity 64)

def setText (file : String) (text : String) : TestM Unit := do
  let filepath : FilePath := ⟨file⟩
  let store ← get
  let memo : Memo Key Val (.text filepath) := { value := text, deps := ∅ }
  let store := store.insert (.text filepath) memo
  let inputFiles : HashSet FilePath :=
    match store.get? .inputFiles with
    | some (m : Memo Key Val .inputFiles) => m.value.insert filepath
    | none => {filepath}
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅ }
  let store := store.insert .inputFiles inputMemo
  match Shake.build tasks (Key.checkFile filepath) store with
  | .ok (_, store) => set store
  | .error .cycle => throw (IO.userError "cycle detected")
  | .error .missingInput => throw (IO.userError "missing input")

def diagnostics (file : String) (check : Array Diagnostic → Bool) : TestM Unit := do
  let filepath : FilePath := ⟨file⟩
  let store ← get
  let diags := match store.get? (Key.checkFile filepath) with
    | some memo => memo.value
    | none => #[]
  if !check diags then
    throw (IO.userError s!"diagnostics check failed: {diags.map (·.error)}")

def hover (file : String) (pos : Lean.Position) (expected : String) : TestM Unit := do
  let filepath : FilePath := ⟨file⟩
  let store ← get
  let text := match store.get? (Key.text filepath) with
    | some memo => memo.value
    | none => ""
  match elaborateFile store filepath with
  | none => throw (IO.userError s!"no elaboration info for {filepath}")
  | some (info, sourceMap, cst) =>
    let bytePos := (Lean.FileMap.ofString text).ofPosition pos
    let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
    match lookupHoverAtPosition cst sourceMap info codepointPos with
    | none => throw (IO.userError s!"no hover at {repr pos}, expected '{expected}'")
    | some content =>
      let formatted := content.format
      if formatted != expected then
        throw (IO.userError s!"hover mismatch at {repr pos}: expected '{expected}', got '{formatted}'")

def noHover (file : String) (pos : Lean.Position) : TestM Unit := do
  let filepath : FilePath := ⟨file⟩
  let store ← get
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
      throw (IO.userError s!"expected no hover at {repr pos}, got '{content.format}'")

end Qdt.Lsp.Test
