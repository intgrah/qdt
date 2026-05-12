module

public import Cli.Basic
public import Mathlib.Tactic.Basic

@[expose] public section

namespace Qdt

open Cli
open System (FilePath)

inductive BuildSystem where
  | busy
  | lessBusy
  | salsa
  | salsaC
  | shake
  | shakeC
deriving Repr, Inhabited

instance : Cli.ParseableType BuildSystem where
  name := "BuildSystem"
  parse?
    | "busy" => some .busy
    | "less-busy" => some .lessBusy
    | "salsa" => some .salsa
    | "salsa-c" => some .salsaC
    | "shake" => some .shake
    | "shake-c" => some .shakeC
    | _ => none

structure Config where
  root : FilePath
  watchMode : Bool
  buildSystem : BuildSystem
  files : Array FilePath
  dumpGraph : Option FilePath

def moduleToPath (modName : String) : FilePath :=
  let parts := modName.splitOn "."
  FilePath.mk (String.intercalate "/" parts) |>.addExtension "qdt"

def resolveFile (root : FilePath) (arg : String) : FilePath :=
  if arg.endsWith ".qdt" then ⟨arg⟩
  else root / moduleToPath arg

def parseConfig (parsed : Parsed) : IO Config := do
  let root ← IO.FS.realPath (parsed.flag? "root" |>.map (·.as! String) |>.getD ".")
  let watchMode := parsed.hasFlag "watch"
  let buildSystem := parsed.flag? "build" |>.map (·.as! BuildSystem) |>.getD .shakeC
  let dumpGraph : Option FilePath := parsed.flag? "dump-graph" |>.map fun f => ⟨f.as! String⟩
  let args := parsed.variableArgsAs! String
  if args.isEmpty then
    throw (IO.userError "No files specified. Usage: qdt <module>...")
  let files ← args.mapM fun arg => IO.FS.realPath (resolveFile root arg)
  return { root, watchMode, buildSystem, files, dumpGraph }

end Qdt
