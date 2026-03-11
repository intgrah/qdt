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
  | shake
  | shakeNative
deriving Repr, Inhabited

instance : Cli.ParseableType BuildSystem where
  name := "BuildSystem"
  parse?
    | "busy" => some .busy
    | "less-busy" => some .lessBusy
    | "salsa" => some .salsa
    | "shake" => some .shake
    | "shake-native" => some .shakeNative
    | _ => none

structure Config where
  root : FilePath
  watchMode : Bool
  buildSystem : BuildSystem
  files : Array FilePath

def moduleToPath (modName : String) : FilePath :=
  let parts := modName.splitOn "."
  FilePath.mk (String.intercalate "/" parts) |>.addExtension "qdt"

def resolveFile (root : FilePath) (arg : String) : FilePath :=
  if arg.endsWith ".qdt" then ⟨arg⟩
  else root / moduleToPath arg

def parseConfig (parsed : Parsed) : IO Config := do
  let root ← IO.FS.realPath (parsed.flag? "root" |>.map (·.as! String) |>.getD ".")
  let watchMode := parsed.hasFlag "watch"
  let buildSystem := parsed.flag? "build" |>.map (·.as! BuildSystem) |>.getD .shakeNative
  let args := parsed.variableArgsAs! String
  if args.isEmpty then
    throw (IO.userError "No files specified. Usage: qdt <module>...")
  let files ← args.mapM fun arg => IO.FS.realPath (resolveFile root arg)
  return { root, watchMode, buildSystem, files }

end Qdt
