module

public import Cli.Basic
public import FSWatch.Manager
public import Qdt.Incremental.Rules

@[expose] public section

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

def checkModule (inputs : DHashMap InputKey InputVal) (filepath : FilePath) :
    StateT build.σ (Except BuildError) (Array String) := do
  let transImports ← build.build tasks (Key.transitiveImports filepath)
  let mut msgs : Array String := #[]
  for file in transImports.toList ++ [filepath] do
    let diags ← build.build tasks (Key.checkFile file)
    if diags.isEmpty then continue
    let text := (inputs.get? (.text file)).getD ""
    let (_, sm, _) ← build.build tasks (Key.astSourceMap file)
    let (cst, _) ← build.build tasks (Key.cst file)
    for d in diags do
      msgs := msgs.push (d.format file text sm cst)
  return msgs

def runOnce (inputs : DHashMap InputKey InputVal) (store : build.σ) (filepath : FilePath) :
    Array String × build.σ :=
  match StateT.run (s := store) <| checkModule inputs filepath with
  | .ok (msgs, store) => (msgs, store)
  | .error .cycle => (#["[error] cycle detected"], store)

def watchLoop (root : FilePath) (inputs₀ : DHashMap InputKey InputVal) (store₀ : build.σ)
    (entryFile : FilePath) : IO Unit := do
  let (msgs, initialStore) := runOnce inputs₀ store₀ entryFile
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
          store.modify fun s => (build.set (InputKey.text file) (some text) |>.run s).2
          inputs.modify (·.insert (.text file) text)
        let (msgs, s) := runOnce (← inputs.get) (← store.get) entryFile
        for msg in msgs do println! msg
        store.set s

def resolveFile (root : FilePath) (arg : String) : FilePath :=
  if arg.endsWith ".qdt" then
    ⟨arg⟩
  else
    root / Config.moduleToPath arg

def run (parsed : Parsed) : IO UInt32 := do
  let root ← IO.FS.realPath (parsed.flag? "root" |>.map (·.as! String) |>.getD ".")
  let watchMode := parsed.hasFlag "watch"

  let args := parsed.variableArgsAs! String
  if args.isEmpty then
    throw (IO.userError "No files specified. Usage: qdt <module>...")

  let files ← args.mapM fun arg => IO.FS.realPath (resolveFile root arg)

  let inputs ← scanInputs root
  let store := build.init inputs

  if watchMode then
    watchLoop root inputs store files[0]!
    return 0
  else
    let t₀ ← IO.monoMsNow
    let mut allMsgs : Array String := #[]
    let mut store := store
    for file in files do
      let (msgs, store') := runOnce inputs store file
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

def cmd : Cmd :=
  Cmd.mk
    (name := "qdt")
    (version? := none)
    (description := "Query-based Dependent Type elaborator")
    (flags := #[
      ⟨some "r", "root", "project root directory (default: cwd)", String⟩,
      Flag.paramless (longName := "watch") (description := "Enable watch mode"),
      Flag.paramless (longName := "profile") (description := "Print query profile table after build")
    ])
    (variableArg? := some { name := "module", description := "Modules to check", type := String })
    (run := run)

end Qdt

def main : List String → IO UInt32 :=
  Qdt.cmd.validate
