import Cli
import FSWatch
import Qdt
import Qdt.IncrementalElab

open Cli
open Qdt
open Incremental (Engine TaskM Key Val GlobalEnv)
open System (FilePath)

private def countModuleEntries (file : FilePath) :
    TaskM Error Val Nat := do
  let env : GlobalEnv ← TaskM.fetch (Key.elabModule file)
  return env.size

private def runModuleOnce (config : Config) (engine : Engine Error Val) (file : FilePath) : IO (Engine Error Val) := do
  let t0 ← IO.monoMsNow
  match ← Incremental.run config engine (countModuleEntries file) with
  | .ok (count, engine') =>
      let t1 ← IO.monoMsNow
      println!"{count} entries, {t1 - t0}ms"
      pure engine'
  | .error err =>
      let t1 ← IO.monoMsNow
      println!"[error] {err}"
      println!"{t1 - t0}ms"
      pure engine

partial def watchLoop (config : Config) (engine : Engine Error Val) (entryFile : FilePath) : IO Unit := do
  let engineRef ← IO.mkRef engine
  let pendingRef ← IO.mkRef ([] : List FilePath)

  let engine' ← runModuleOnce config engine entryFile
  engineRef.set engine'

  FSWatch.Manager.withManager fun m => do
    for dir in config.watchDirs do
      let _ ← m.watchTree dir (predicate := fun e => e.path.toString.endsWith ".qdt") fun e => do
        pendingRef.modify (e.path :: ·)

    while true do
      IO.sleep 50
      let pending ← pendingRef.modifyGet (·, [])
      if !pending.isEmpty then
        let eng ← engineRef.get
        let eng' ← runModuleOnce config eng entryFile
        engineRef.set eng'

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
  let stdlibPath := parsed.flag? "stdlib" |>.map (·.as! String)
  let noStdlib := parsed.hasFlag "no-stdlib"
  let watchMode := parsed.hasFlag "watch"
  let watchDir := parsed.flag? "watch-dir" |>.map (·.as! String)

  let cliArg := parsed.variableArgsAs? String |>.bind (·[0]?)

  let mut config ← Config.load

  if let some dir := sourceDir then
    config := { config with sourceDirectories := [⟨dir⟩] }
  if let some path := stdlibPath then
    config := { config with
      dependencies := config.dependencies.filter (·.name != "std") ++ [{ name := "std", path }]
    }
  if noStdlib then
    config := { config with dependencies := config.dependencies.filter (·.name != "std") }
  if watchMode then
    config := { config with watchMode := true }
  if let some dir := watchDir then
    config := { config with watchDirs := [⟨dir⟩] }

  let filePath ← resolveEntryFile config cliArg

  println!"[config] Entry: {filePath}"
  println!"[config] Source directories: {config.sourceDirectories}"
  if !config.dependencies.isEmpty then
    println!"[config] Dependencies: {config.dependencies.map (·.name)}"

  let engine : Engine Error Val := Incremental.newEngine

  if config.watchMode then
    println!"[watch] Watching {config.watchDirs}"
    watchLoop config engine filePath
  else
    let _ ← runModuleOnce config engine filePath
  return 0

def qdtCmd : Cmd :=
  Cmd.mk
    (name := "qdt")
    (version? := none)
    (description := "QDT - Query-based Dependent Types compiler")
    (flags := #[
      ⟨some "s", "source", "source directory", String⟩,
      ⟨none, "stdlib", "stdlib path", String⟩,
      Flag.paramless (longName := "no-stdlib") (description := "Do not include stdlib"),
      Flag.paramless (longName := "watch") (description := "Enable watch mode"),
      ⟨none, "watch-dir", "Add directory to watch", String⟩
    ])
    (positionalArgs := #[])
    (run := runQdt)

def main (args : List String) : IO UInt32 :=
  qdtCmd.validate args
