module

public import Qdt.Cli.Format
public import Qdt.Common
public import Incremental.Shake.Trace
public import Incremental.LawfulEST
public import FSWatch.Manager

@[expose] public section

namespace Qdt.Cli.Runner

open Qdt
open Qdt.Cli
open Incremental
open Std (DHashMap)
open System (FilePath)

partial def DepNode.lines : Trace.DepNode Key → String → String → List String
  | ⟨q, dt, children⟩, prefixHere, prefixRest =>
    let head := prefixHere ++ s!"{q.display} ({dt / 1000}µs)"
    let n := children.size
    let childLines := children.toList.zipIdx.flatMap fun (c, i) =>
      let isLast := i + 1 == n
      let here := prefixRest ++ (if isLast then "└─ " else "├─ ")
      let rest := prefixRest ++ (if isLast then "   " else "│  ")
      DepNode.lines c here rest
    head :: childLines

instance : ToString (Trace.Forest Key) where
  toString f := String.intercalate "\n" (f.toList.flatMap fun root => DepNode.lines root "" "")

def traceBuild : Build Monad config Input tasks (Trace.TraceT Key BaseIO) Id :=
  ShakeTrace config Input (fun _ => Hashable.toEmbedding)
    (fun _ => Hashable.toEmbedding) tasks

def traceOnce (store : traceBuild.σ) (file : FilePath) :
    BaseIO (Array Diagnostic × traceBuild.σ × Trace.Forest Key) := do
  let ((diags, store'), forest) ←
    Trace.run (StateT.run (s := store) (traceBuild.run (Key.checkFile file)))
  let diags : Array Diagnostic := diags
  return (diags, store', forest)

def reportOnce (file : FilePath) (diags : Array Diagnostic) (forest : Trace.Forest Key) :
    IO Unit := do
  IO.eprintln s!"=== {file} ==="
  IO.eprintln (toString forest)
  for d in diags do
    println! s!"{file}: error: {d.error}"

def runTraceOnce (cfg : Config) : IO UInt32 := do
  let inputs ← scanInputs cfg.root
  let mut store := traceBuild.init inputs
  let mut exitCode : UInt32 := 0
  for file in cfg.files do
    let (diags, store', forest) ← traceOnce store file
    store := store'
    reportOnce file diags forest
    if !diags.isEmpty then exitCode := 1
  return exitCode

def watchLoopTrace (root : FilePath) (inputs₀ : DHashMap InputKey InputVal)
    (store₀ : traceBuild.σ) (entryFile : FilePath) : IO Unit := do
  let (diags, initialStore, forest) ← traceOnce store₀ entryFile
  reportOnce entryFile diags forest
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
          store.modify fun s => (traceBuild.set (InputKey.text absPath) (some text) |>.run s).2
          inputs.modify (·.insert (.text absPath) text)
        let (diags, s, forest) ← traceOnce (← store.get) entryFile
        reportOnce entryFile diags forest
        store.set s

def runTrace (cfg : Config) : IO UInt32 := do
  if cfg.watchMode then
    let inputs ← scanInputs cfg.root
    let store := traceBuild.init inputs
    watchLoopTrace cfg.root inputs store cfg.files[0]!
    return 0
  else
    runTraceOnce cfg

end Qdt.Cli.Runner
