import Cli
import FSWatch
import Qdt
import Qdt.Incremental

open Cli
open Qdt
open Incremental (Engine TaskM Key Val)
open System (FilePath)

partial def forceElaborateModule (visited : Std.HashSet FilePath) (filepath : FilePath) :
    TaskM Val (Nat × Std.HashSet FilePath) := do
  if filepath ∈ visited then
    return (0, visited)
  let mut count := 0
  let mut visited := visited.insert filepath
  let importNames ← fetchQ (Key.moduleImports filepath)
  for modName in importNames.toArray do
    match ← fetchQ (Key.moduleFile modName) with
    | none =>
        IO.toEIO (fun _ => ()) <| IO.eprintln s!"[warn] Module not found: {modName}"
    | some depFile =>
        let (c, v) ← forceElaborateModule visited depFile
        count := count + c
        visited := v
  let (env, _info) ← fetchQ (Key.elabModule filepath)
  let importedEnv ← fetchQ (Key.importedEnv filepath)
  let fileCount := env.size - importedEnv.size
  IO.toEIO (fun _ => ()) <| IO.eprintln s!"[count] {filepath}: {fileCount} entries"
  count := count + fileCount
  return (count, visited)

private def countModuleEntries (filepath : FilePath) :
    TaskM Val Nat := do
  let (count, _) ← forceElaborateModule (Std.HashSet.emptyWithCapacity 256) filepath
  return count

private def runModuleOnce (ctx : Incremental.BaseContext) (engine : Engine Val) (filepath : FilePath) : IO (Engine Val) := do
  let t0 ← IO.monoMsNow
  match ← (Incremental.run ctx engine (countModuleEntries filepath)).toIO' with
  | .ok (count, engine') =>
      let t1 ← IO.monoMsNow
      println!"{count} entries, {t1 - t0}ms"
      pure engine'
  | .error () =>
      let t1 ← IO.monoMsNow
      println!"[error] cycle detected"
      println!"{t1 - t0}ms"
      pure engine

def watchLoop (ctx : Incremental.BaseContext) (engine : Engine Val) (entryFile : FilePath) : IO Unit := do
  let engine ← IO.mkRef (← runModuleOnce ctx engine entryFile)
  let pending ← IO.mkRef []

  FSWatch.Manager.withManager fun m => do
    for dir in ctx.config.sourceDirectories do
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

def run (parsed : Parsed) : IO UInt32 := do
  let sourceDir := parsed.flag? "source" |>.map (·.as! String)
  let watchMode := parsed.hasFlag "watch"

  let cliArg := parsed.variableArgsAs? String |>.bind (·[0]?)

  let mut config ← Config.load

  if let some dir := sourceDir then
    config := { config with sourceDirectories := #[⟨dir⟩] }
  if watchMode then
    config := { config with watchMode := true }

  let filePath ← resolveEntryFile config cliArg

  println!"[config] Entry: {filePath}"
  println!"[config] Source directories: {config.sourceDirectories}"

  let engine : Engine Val := Incremental.newEngine

  let ctx : Incremental.BaseContext := { config, overrides := ∅ }

  if config.watchMode then
    watchLoop ctx engine filePath
  else
    let _ ← runModuleOnce ctx engine filePath
  return 0

def cmd : Cmd :=
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
    (run := run)

def main : List String → IO UInt32 :=
  cmd.validate
