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

def maxDepth : Nat := 3

def relativize (root : FilePath) (s : String) : String :=
  s.replace (root.toString ++ "/") ""

partial def DepNode.lines : FilePath → Nat → Trace.DepNode Key →
    String → String → List String
  | root, 0, ⟨q, dt, _⟩, prefixHere, _ =>
    [prefixHere ++ s!"{relativize root q.display} ({dt / 1000000}.{(dt / 100000) % 10}ms) …"]
  | root, depth + 1, ⟨q, dt, children⟩, prefixHere, prefixRest =>
    let head := prefixHere ++ s!"{relativize root q.display} ({dt / 1000000}.{(dt / 100000) % 10}ms)"
    let n := children.size
    let childLines := children.toList.zipIdx.flatMap fun (c, i) =>
      let isLast := i + 1 == n
      let here := prefixRest ++ (if isLast then "└─ " else "├─ ")
      let rest := prefixRest ++ (if isLast then "   " else "│  ")
      DepNode.lines root depth c here rest
    head :: childLines

def renderForest (root : FilePath) (f : Trace.Forest Key) : String :=
  String.intercalate "\n" (f.toList.flatMap fun n => DepNode.lines root maxDepth n "" "")

def traceBuild : Build config Input tasks (Trace.TraceT Key BaseIO) Id :=
  ShakeTrace config Input (fun _ => Hashable.toEmbedding)
    (fun _ => Hashable.toEmbedding) tasks

def traceOnce (store : traceBuild.σ) (file : FilePath) :
    BaseIO (Array (FilePath × Array Diagnostic) × traceBuild.σ × Trace.Forest Key) := do
  let ((transImports, store₁), forestImports) ←
    Trace.run (StateT.run (s := store) (traceBuild.run (Key.transitiveImports file)))
  let mut store := store₁
  let mut forests := forestImports
  let mut perFile : Array (FilePath × Array Diagnostic) := #[]
  for f in transImports.toList ++ [file] do
    let ((diags, store'), forest) ←
      Trace.run (StateT.run (s := store) (traceBuild.run (Key.checkFile f)))
    let diags : Array Diagnostic := diags
    store := store'
    forests := forests ++ forest
    perFile := perFile.push (f, diags)
  return (perFile, store, forests)

def reportOnce (root entry : FilePath) (perFile : Array (FilePath × Array Diagnostic))
    (forest : Trace.Forest Key) : IO Unit := do
  IO.eprintln s!"=== {relativize root entry.toString} ==="
  IO.eprintln (renderForest root forest)
  for (file, diags) in perFile do
    for d in diags do
      println! s!"{relativize root file.toString}: error: {d.error}"

def runTraceOnce (cfg : Config) : IO UInt32 := do
  let inputs ← scanInputs cfg.root
  let mut store := traceBuild.init inputs
  let mut exitCode : UInt32 := 0
  for file in cfg.files do
    let (perFile, store', forest) ← traceOnce store file
    store := store'
    reportOnce cfg.root file perFile forest
    if perFile.any (fun (_, ds) => !ds.isEmpty) then exitCode := 1
  return exitCode

def watchLoopTrace (root : FilePath) (inputs₀ : DHashMap InputKey InputVal)
    (store₀ : traceBuild.σ) (entryFile : FilePath) : IO Unit := do
  let (perFile, initialStore, forest) ← traceOnce store₀ entryFile
  reportOnce root entryFile perFile forest
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
        let (perFile, s, forest) ← traceOnce (← store.get) entryFile
        reportOnce root entryFile perFile forest
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
