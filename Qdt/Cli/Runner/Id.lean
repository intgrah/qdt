module

public import Qdt.Cli.Format
public import Qdt.Common
public import FSWatch.Manager

@[expose] public section

namespace Qdt.Cli.Runner

open Qdt
open Qdt.Cli
open Incremental
open Std (DHashMap)
open System (FilePath)

variable {b : Build Monad config (DHashMap InputKey InputVal) tasks Id Id}

def checkModule (inputs : DHashMap InputKey InputVal) (filepath : FilePath) :
    StateM b.σ (Array String) := do
  let transImports := Id.run (← b.run (Key.transitiveImports filepath))
  let mut msgs : Array String := #[]
  for file in transImports.toList ++ [filepath] do
    let diags := Id.run (← b.run (Key.checkFile file))
    if diags.isEmpty then continue
    let text := (inputs.get? (.text file)).getD ""
    let (_, sm, _) := Id.run (← b.run (Key.astSourceMap file))
    for d in diags do
      msgs := msgs.push (Diagnostic.format file text sm d)
  return msgs

def runOnce (inputs : DHashMap InputKey InputVal) (store : b.σ) (filepath : FilePath) :
    Array String × b.σ :=
  StateT.run (s := store) <| checkModule inputs filepath

def watchLoop (root : FilePath) (inputs₀ : DHashMap InputKey InputVal) (store₀ : b.σ)
    (entryFile : FilePath) : IO Unit := do
  let t₀ ← IO.monoMsNow
  let (msgs, initialStore) := runOnce inputs₀ store₀ entryFile
  let t₁ ← IO.monoMsNow
  for msg in msgs do println! msg
  if msgs.isEmpty then
    println! "OK ({t₁ - t₀}ms)"
  else
    println! "{msgs.size} error(s) ({t₁ - t₀}ms)"
  let store ← IO.mkRef initialStore
  let inputs ← IO.mkRef inputs₀
  let pending ← IO.mkRef #[]

  FSWatch.Manager.withManager fun m => do
    let pred (e : FSWatch.Event) : Bool :=
      e.path.toString.endsWith ".qdt" &&
        (e.kind == .closeWrite || e.kind == .movedIn)
    let _ ← m.watchTree root pred fun e => do
      pending.modify (·.push e.path)

    while true do
      IO.sleep 50
      let pendingFiles ← pending.modifyGet (·, #[])
      if !pendingFiles.isEmpty then
        for file in pendingFiles do
          let absPath ← IO.FS.realPath file
          let text ← IO.FS.readFile absPath
          store.modify fun s => (b.set (InputKey.text absPath) (some text) |>.run s).2
          inputs.modify (·.insert (.text absPath) text)
        let t₀ ← IO.monoMsNow
        let (msgs, s) := runOnce (← inputs.get) (← store.get) entryFile
        let t₁ ← IO.monoMsNow
        for msg in msgs do println! msg
        store.set s
        if msgs.isEmpty then
          println! "OK ({t₁ - t₀}ms)"
        else
          println! "{msgs.size} error(s) ({t₁ - t₀}ms)"

def runId (cfg : Config) (b : Build Monad config Input tasks Id Id) : IO UInt32 := do
  let inputs ← scanInputs cfg.root
  let store := b.init inputs

  if cfg.watchMode then
    watchLoop cfg.root inputs store cfg.files[0]!
    return 0
  else
    let t₀ ← IO.monoMsNow
    let mut allMsgs : Array String := #[]
    let mut store := store
    for file in cfg.files do
      let (msgs, store') := runOnce inputs store file
      allMsgs := allMsgs ++ msgs
      store := store'
    let t₁ ← IO.monoMsNow
    for msg in allMsgs do println! msg
    if allMsgs.isEmpty then
      println! "OK ({t₁ - t₀}ms)"
      return 0
    else
      println! "{allMsgs.size} error(s) ({t₁ - t₀}ms)"
      return 1

end Qdt.Cli.Runner
