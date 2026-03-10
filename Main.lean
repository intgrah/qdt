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

def checkModule (store : QStore) (filepath : FilePath) : Array String := Id.run do
  let some transImports := store.cache.get? (Key.transitiveImports filepath)
    | return #[s!"{filepath}: error: missing transitive imports"]
  let allFiles := transImports.value.toList ++ [filepath]
  let mut msgs : Array String := #[]
  for file in allFiles do
    let some diagsMemo := store.cache.get? (Key.checkFile file) | continue
    let diags := diagsMemo.value
    if diags.isEmpty then continue
    let text := (store.inputs.get? (.text file)).getD ""
    let some asmMemo := store.cache.get? (Key.astSourceMap file) | continue
    let (_, sm, _) := asmMemo.value
    let some cstMemo := store.cache.get? (Key.cst file) | continue
    let (cst, _) := cstMemo.value
    for d in diags do
      msgs := msgs.push (d.format file text sm cst)
  return msgs

def runOnce (root : FilePath) (store : QStore) (filepath : FilePath) :
    IO (Array String × QStore) := do
  let store ← QStore.populate root store
  let (transImports, store) ← match build.build tasks (Key.transitiveImports filepath) store with
    | .ok (v, s) => pure (v, s)
    | .error .cycle => return (#["[error] cycle detected"], store)
  let allFiles := transImports.toList ++ [filepath]
  let keys := allFiles.map Key.checkFile
  match keys.foldlM (fun s k => Prod.snd <$> build.build tasks k s) store with
  | .ok store =>
      let msgs := checkModule store filepath
      return (msgs, store)
  | .error .cycle => return (#["[error] cycle detected"], store)

def watchLoop (root : FilePath) (store : QStore) (entryFile : FilePath) : IO Unit := do
  let (msgs, initialStore) ← runOnce root store entryFile
  for msg in msgs do println! msg
  let store ← IO.mkRef initialStore
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
          store.modify fun s => { s with inputs := s.inputs.insert (.text file) text }
        let (msgs, s) ← runOnce root (← store.get) entryFile
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

  let store := build.init (DHashMap.emptyWithCapacity 64)

  if watchMode then
    watchLoop root store files[0]!
    return 0
  else
    let t₀ ← IO.monoMsNow
    let mut allMsgs : Array String := #[]
    let mut store := store
    for file in files do
      let (msgs, store') ← runOnce root store file
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
