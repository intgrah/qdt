module

public import Qdt.Lsp
public import Qdt.Test

@[expose] public section

namespace Qdt.Lsp.Test

open Qdt Qdt.Test
open Incremental
open Std (DHashMap HashSet)
open System (FilePath)

structure TestState where
  inputs : DHashMap InputKey InputVal
  store : testBuild.σ
  errors : Array String := #[]

abbrev TestM := StateRefT TestState IO

def test (action : TestM Unit) : IO Unit := do
  let check : TestM Unit := do
    action
    let errors := (← get).errors
    if !errors.isEmpty then
      throw (IO.userError ("\n".intercalate errors.toList))
  let inputs := DHashMap.emptyWithCapacity 64
  check.run' { inputs, store := testBuild.init inputs }

def fail (msg : String) : TestM Unit :=
  modify fun st => { st with errors := st.errors.push msg }

def setText (text : String) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let st ← get
  let inputs := st.inputs.insert (.text filepath) text
  let inputFiles : HashSet FilePath :=
    match st.inputs.get? .inputFiles with
    | some fs => fs.insert filepath
    | none => {filepath}
  let inputs := inputs.insert .inputFiles inputFiles
  let (_, store) := (testBuild.set (.text filepath) (some text)).run st.store
  let (_, store) := (testBuild.set .inputFiles (some inputFiles)).run store
  match StateT.run (s := store) <| testBuild.build tasks (Key.checkFile filepath) with
  | .ok (_, store) => modify fun _ => { inputs, store }
  | .error .cycle => throw (IO.userError "cycle detected")

def diagnostics (check : Array Diagnostic → Bool) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let store := (← get).store
  let diags := match StateT.run (s := store) <| testBuild.build tasks (Key.checkFile filepath) with
    | .ok (v, _) => v
    | .error _ => #[]
  if !check diags then
    fail s!"diagnostics check failed: {diags.map (·.error)}"

def noDiagnostics (filepath : FilePath := "test.qdt") : TestM Unit :=
  diagnostics Array.isEmpty filepath

def hover (pos : Lean.Position) (expected : String)
    (start stop : Lean.Position) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let st ← get
  let text := (st.inputs.get? (.text filepath)).getD ""
  let fileMap := Lean.FileMap.ofString text
  match StateT.run (s := st.store) <| elaborateFile testBuild filepath with
  | .error _ => fail s!"no elaboration info for {filepath}"
  | .ok ((info, sourceMap, cst), _) =>
    let bytePos := fileMap.ofPosition pos
    let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
    match lookupHoverAtPosition cst sourceMap info codepointPos with
    | none => fail s!"no hover at {repr pos}, expected '{expected}'"
    | some (content, span) =>
      let formatted := content.format
      if formatted != expected then
        fail s!"hover mismatch at {repr pos}: expected '{expected}', got '{formatted}'"
      let expectedStart := utf8PosToCodepointPos text (fileMap.ofPosition start).byteIdx
      let expectedStop := utf8PosToCodepointPos text (fileMap.ofPosition stop).byteIdx
      if span.startPos != expectedStart || span.endPos != expectedStop then
        let actualStart := fileMap.utf8PosToLspPos ⟨codepointPosToUtf8Pos text span.startPos⟩
        let actualStop := fileMap.utf8PosToLspPos ⟨codepointPosToUtf8Pos text span.endPos⟩
        fail s!"hover span mismatch at {repr pos}: expected {repr start}..{repr stop}, got {repr actualStart}..{repr actualStop}"

def noHover (pos : Lean.Position) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let st ← get
  let text := (st.inputs.get? (.text filepath)).getD ""
  match StateT.run (s := st.store) <| elaborateFile testBuild filepath with
  | .error _ => return
  | .ok ((info, sourceMap, cst), _) =>
    let bytePos := (Lean.FileMap.ofString text).ofPosition pos
    let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
    match lookupHoverAtPosition cst sourceMap info codepointPos with
    | none => return
    | some (content, _) =>
      fail s!"expected no hover at {repr pos}, got '{content.format}'"

end Qdt.Lsp.Test
