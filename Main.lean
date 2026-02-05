import Cli
import FSWatch
import Qdt
import Qdt.Incremental

open Cli
open Qdt
open Incremental (Engine TaskM Key Val)
open System (FilePath)

partial def forceElaborateModule (visited : Std.HashSet FilePath) (filepath : FilePath) :
    TaskM Error Val (Nat × Std.HashSet FilePath) := do
  if visited.contains filepath then
    return (0, visited)
  let mut count := 0
  let mut visited := visited.insert filepath
  let importNames ← fetchQ (Key.moduleImports filepath)
  for modName in importNames.toArray do
    match ← fetchQ (Key.moduleFile modName) with
    | none => throw (.msg s!"Import not found: {modName}")
    | some depFile =>
        let (c, v) ← forceElaborateModule visited depFile
        count := count + c
        visited := v
  let ordering : List Incremental.TopDecl ← fetchQ (Key.declOrdering filepath)
  for decl in ordering do
    let localEnv ← fetchQ (Key.elabTop filepath decl)
    count := count + localEnv.size
  return (count, visited)

private def countModuleEntries (filepath : FilePath) :
    TaskM Error Val Nat := do
  let (count, _) ← forceElaborateModule (Std.HashSet.emptyWithCapacity 256) filepath
  return count

private def runModuleOnce (ctx : Incremental.Context) (engine : Engine Error Val) (filepath : FilePath) : IO (Engine Error Val) := do
  let t0 ← IO.monoMsNow
  match ← (Incremental.run ctx engine (countModuleEntries filepath)).toIO' with
  | .ok (count, engine') =>
      let t1 ← IO.monoMsNow
      println!"{count} entries, {t1 - t0}ms"
      pure engine'
  | .error err =>
      let t1 ← IO.monoMsNow
      println!"[error] {err}"
      println!"{t1 - t0}ms"
      pure engine

def watchLoop (ctx : Incremental.Context) (engine : Engine Error Val) (entryFile : FilePath) : IO Unit := do
  let engine ← IO.mkRef (← runModuleOnce ctx engine entryFile)
  let pending ← IO.mkRef []

  FSWatch.Manager.withManager fun m => do
    for dir in ctx.config.watchDirs do
      let _ ← m.watchTree dir (predicate := fun e => e.path.toString.endsWith ".qdt") fun e => do
        pending.modify (e.path :: ·)

    while true do
      IO.sleep 50
      let pending ← pending.modifyGet (·, [])
      if !pending.isEmpty then
        let eng ← engine.get
        let eng' ← runModuleOnce ctx eng entryFile
        engine.set eng'

def resolveEntryFile (config : Config) (cliArg : Option String) : IO FilePath := do
  let projectRoot := config.projectRoot.getD "."

  if let some arg := cliArg then
    if arg.endsWith ".qdt" then
      return arg
    else
      return projectRoot / Config.moduleToPath arg

  if let some entry := config.entry then
    return projectRoot / Config.moduleToPath entry

  throw (IO.userError "No entry point specified. Use 'qdt <module>' or set 'entry' in qdt.toml")

def runQdt (parsed : Parsed) : IO UInt32 := do
  let sourceDir := parsed.flag? "source" |>.map (·.as! String)
  let watchMode := parsed.hasFlag "watch"
  let watchDir := parsed.flag? "watch-dir" |>.map (·.as! String)

  let cliArg := parsed.variableArgsAs? String |>.bind (·[0]?)

  let mut config ← Config.load

  if let some dir := sourceDir then
    config := { config with sourceDirectories := [⟨dir⟩] }
  if watchMode then
    config := { config with watchMode := true }
  if let some dir := watchDir then
    config := { config with watchDirs := [⟨dir⟩] }

  let filePath ← resolveEntryFile config cliArg

  println!"[config] Entry: {filePath}"
  println!"[config] Source directories: {config.sourceDirectories}"

  let engine : Engine Error Val := Incremental.newEngine

  let ctx : Incremental.Context := ⟨config, ∅⟩

  if config.watchMode then
    println!"[watch] Watching {config.watchDirs}"
    watchLoop ctx engine filePath
  else
    let _ ← runModuleOnce ctx engine filePath
  return 0

def qdtCmd : Cmd :=
  Cmd.mk
    (name := "qdt")
    (version? := none)
    (description := "Query-based Dependent Type elaborator")
    (flags := #[
      ⟨some "s", "source", "source directory", String⟩,
      Flag.paramless (longName := "watch") (description := "Enable watch mode"),
      { longName := "watch-dir", description := "Add directory to watch", «type» := String }
    ])
    (positionalArgs := #[])
    (run := runQdt)

def main (args : List String) : IO UInt32 :=
  qdtCmd.validate args
