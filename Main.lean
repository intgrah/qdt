module

import Cli.Extensions
import FSWatch.Manager
import Qdt.Common
import Qdt.Incremental.Rules

namespace Qdt

open Cli
open Qdt
open Incremental
open Std (DHashMap)
open System (FilePath)

def posToLineCol (text : String) (pos : Nat) : Lean.Position :=
  (Lean.FileMap.ofString text).toPosition ⟨pos⟩

def resolveSpan (sm : Frontend.SourceMap) (cst : Frontend.Cst) (path : Frontend.Path) :
    Option Frontend.Span := Id.run do
  let fwd := path.reverse
  for len in (List.range fwd.length).reverse do
    if let some cstPath := sm.astToCst[fwd.take (len + 1)]? then
      return cst.spanAtPath cstPath
  return none

def Diagnostic.format (file : FilePath) (text : String) (sm : Frontend.SourceMap)
    (cst : Frontend.Cst) (d : Diagnostic) : String :=
  match resolveSpan sm cst d.path with
  | some span =>
      let ⟨line, col⟩ := posToLineCol text span.startPos
      s!"{file}:{line}:{col}: error: {d.error}"
  | none =>
      s!"{file}: error: {d.error}"

variable {b : Build Monad config (DHashMap InputKey InputVal)}

def checkModule (inputs : DHashMap InputKey InputVal) (filepath : FilePath) :
    StateM b.σ (Array String × Nat × Nat × Nat) := do
  let transImports ← b.build tasks (Key.transitiveImports filepath)
  let mut msgs : Array String := #[]
  let mut totalBeta : Nat := 0
  let mut totalEval : Nat := 0
  let mut totalWhnf : Nat := 0
  for file in transImports.toList ++ [filepath] do
    let (declIdx, _) ← b.build tasks (Key.declarationIndex file)
    for (name, _) in declIdx.toList do
      let (_, info) ← b.build tasks (Key.elabDecl file name)
      totalBeta := totalBeta + info.betaCount
      totalEval := totalEval + info.evalCount
      totalWhnf := totalWhnf + info.whnfCount
    let diags ← b.build tasks (Key.checkFile file)
    if diags.isEmpty then continue
    let text := (inputs.get? (.text file)).getD ""
    let (_, sm, _) ← b.build tasks (Key.astSourceMap file)
    let (cst, _) ← b.build tasks (Key.cst file)
    for d in diags do
      msgs := msgs.push (d.format file text sm cst)
  return (msgs, totalBeta, totalEval, totalWhnf)

def runOnce (inputs : DHashMap InputKey InputVal) (store : b.σ) (filepath : FilePath) :
    (Array String × Nat × Nat × Nat) × b.σ :=
  StateT.run (s := store) <| checkModule inputs filepath

def watchLoop (root : FilePath) (inputs₀ : DHashMap InputKey InputVal) (store₀ : b.σ)
    (entryFile : FilePath) : IO Unit := do
  let ((msgs, _, _, _), initialStore) := runOnce inputs₀ store₀ entryFile
  for msg in msgs do println! msg
  let store ← IO.mkRef initialStore
  let inputs ← IO.mkRef inputs₀
  let pending ← IO.mkRef #[]

  FSWatch.Manager.withManager fun m => do
    let _ ← m.watchTree root (·.path.toString.endsWith ".qdt") fun e => do
      pending.modify (·.push e.path)

    while true do
      IO.sleep 50
      let pendingFiles ← pending.modifyGet (·, #[])
      if !pendingFiles.isEmpty then
        for file in pendingFiles do
          let text ← IO.FS.readFile file
          store.modify fun s => (b.set (InputKey.text file) (some text) |>.run s).2
          inputs.modify (·.insert (.text file) text)
        let ((msgs, _, _, _), s) := runOnce (← inputs.get) (← store.get) entryFile
        for msg in msgs do println! msg
        store.set s

def dumpGraph (outPath : FilePath) (inputs : DHashMap InputKey InputVal)
    (files : Array FilePath) : IO Unit := do
  let b : Build Monad config Input := Shake config Input
  let mut store : b.σ := b.init inputs
  for file in files do
    let (_, store') := runOnce (b := b) inputs store file
    store := store'
  let shakeStore : Shake.Store config Input := store
  let handle ← IO.FS.Handle.mk outPath .write
  let mut edgeCount : Nat := 0
  for ⟨q, memo⟩ in shakeStore.memos do
    let qDisplay := q.display
    for (dep, _) in memo.deps do
      handle.putStrLn s!"{qDisplay}\t{dep.display}"
      edgeCount := edgeCount + 1
    for (i, _) in memo.inputDeps do
      handle.putStrLn s!"{qDisplay}\t{i.display}"
      edgeCount := edgeCount + 1
  handle.flush
  IO.eprintln s!"dumped {edgeCount} edges from {shakeStore.memos.size} queries to {outPath}"

def run (parsed : Parsed) : IO UInt32 := do
  let config ← parseConfig parsed
  let b := selectBuild config.buildSystem

  let inputs ← scanInputs config.root
  let store := b.init inputs

  if let some outPath := config.dumpGraph then
    dumpGraph outPath inputs config.files
    return 0
  else if config.watchMode then
    watchLoop config.root inputs store config.files[0]!
    return 0
  else
    let t₀ ← IO.monoMsNow
    let mut allMsgs : Array String := #[]
    let mut store := store
    for file in config.files do
      let tFileStart ← IO.monoMsNow
      -- Phase A: transitive imports + cst + ast
      let (_transImports, s1) :=
        StateT.run (s := store) (b.build tasks (Key.transitiveImports file))
      let tImports ← IO.monoMsNow
      -- Phase B: full check
      let ((msgs, betaCount, evalCount, whnfCount), store') := runOnce inputs s1 file
      let tCheck ← IO.monoMsNow
      let dImports := tImports - tFileStart
      let dCheck := tCheck - tImports
      let dTotal := tCheck - tFileStart
      IO.eprintln s!"file {file}: imports={dImports}ms check={dCheck}ms total={dTotal}ms betas={betaCount} evals={evalCount} whnfs={whnfCount}"
      allMsgs := allMsgs ++ msgs
      store := store'
    for msg in allMsgs do println! msg
    let t₁ ← IO.monoMsNow
    let δt := t₁ - t₀
    if allMsgs.isEmpty then
      println! "OK ({δt}ms)"
      return 0
    else
      println! "{allMsgs.size} error(s) ({δt}ms)"
      return 1

def cmd : Cmd := `[Cli|
  qdt VIA run;
  "Query-based Dependent Type elaborator"

  FLAGS:
    r, root : String;              "Project root directory (default: cwd)"
    w, watch;                      "Enable watch mode"
    "build" : BuildSystem;         "Build system to use (default: shake-c)"
    profile;                       "Print query profile table after build"
    "dump-graph" : String;         "Dump Shake query graph to file (forces shake build system)"

  ARGS:
    ...modules : String;           "Modules to check"

  EXTENSIONS:
    defaultValues! #[("build", "shake-c")]
]

end Qdt

public def main : List String → IO UInt32 :=
  Qdt.cmd.validate
