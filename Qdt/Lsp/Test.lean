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

def testRoot : FilePath := "/qdt-test"

def key (filepath : FilePath) : FilePath := testRoot / filepath

def test (action : TestM Unit) : IO Unit := do
  let check : TestM Unit := do
    action
    let errors := (← get).errors
    if !errors.isEmpty then
      throw (IO.userError ("\n".intercalate errors.toList))
  let inputs : DHashMap InputKey InputVal :=
    (DHashMap.emptyWithCapacity 64).insert .projectRoot testRoot
  check.run' { inputs, store := testBuild.init inputs }

def fail (msg : String) : TestM Unit :=
  modify fun st => { st with errors := st.errors.push msg }

def setText (text : String) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let fp := key filepath
  let st ← get
  let inputs := st.inputs.insert (.text fp) text
  let inputFiles : Std.HashMap FilePath FilePath :=
    match st.inputs.get? .inputFiles with
    | some fs => fs.insert fp fp
    | none => (∅ : Std.HashMap FilePath FilePath).insert fp fp
  let inputs := inputs.insert .inputFiles inputFiles
  let inputs := inputs.insert .projectRoot testRoot
  let (_, store) := (testBuild.set (.text fp) (some text)).run st.store
  let (_, store) := (testBuild.set .inputFiles (some inputFiles)).run store
  let (_, store) := (testBuild.set .projectRoot (some testRoot)).run store
  let (_, store) := StateT.run (s := store) <| testBuild.run (Key.checkFile fp)
  modify fun st => { st with inputs, store }

def diagnostics (check : Array Diagnostic → Bool) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let store := (← get).store
  let (diags, _) := StateT.run (s := store) <| testBuild.run (Key.checkFile (key filepath))
  if !check diags then
    fail s!"diagnostics check failed: {diags.map (·.error)}"

def noDiagnostics (filepath : FilePath := "test.qdt") : TestM Unit :=
  diagnostics Array.isEmpty filepath

def hover (pos : Lean.Position) (expected : String)
    (start stop : Lean.Position) (filepath : FilePath := "test.qdt") : TestM Unit := do
  let st ← get
  let text := (st.inputs.get? (.text (key filepath))).getD ""
  let fileMap := Lean.FileMap.ofString text
  let ((info, sourceMap), _) := StateT.run (s := st.store) <| elaborateFile testBuild (key filepath)
  let bytePos := fileMap.ofPosition pos
  let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
  match lookupHoverAtPosition sourceMap info codepointPos with
  | none => fail s!"no hover at {repr pos}, expected '{expected}'"
  | some (content, univs, span) =>
    let formatted := content.format univs
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
  let text := (st.inputs.get? (.text (key filepath))).getD ""
  let ((info, sourceMap), _) := StateT.run (s := st.store) <| elaborateFile testBuild (key filepath)
  let bytePos := (Lean.FileMap.ofString text).ofPosition pos
  let codepointPos := utf8PosToCodepointPos text bytePos.byteIdx
  match lookupHoverAtPosition sourceMap info codepointPos with
  | none => return
  | some (content, univs, _) =>
    fail s!"expected no hover at {repr pos}, got '{content.format univs}'"

end Qdt.Lsp.Test
