module

public import Cli.Basic
public import Mathlib.Tactic.Basic

@[expose] public section

namespace Qdt

open Cli
open System (FilePath)

inductive BuildSystem
  | busy
  | lessBusy
  | salsa
  | salsaC
  | shake
  | shakeC
  | shakeRdeps
  | shakeStandardRdeps
  | shakeTrace
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
    | "shake-rdeps" => some .shakeRdeps
    | "shake-standard-rdeps" => some .shakeStandardRdeps
    | "shake-trace" => some .shakeTrace
    | _ => none

structure Config where
  root : FilePath
  watchMode : Bool
  buildSystem : BuildSystem
  files : Array FilePath

def moduleToPath (modName : String) : FilePath :=
  let parts := modName.splitOn "."
  FilePath.mk (String.intercalate "/" parts) |>.addExtension "qdt"

def validateModuleName (arg : String) : Except String Unit := do
  if arg.isEmpty then
    throw "module name is empty"
  if arg.contains '/' then
    throw s!"module name must not contain '/': {arg}"
  if arg.endsWith ".qdt" then
    throw s!"module name must not end in '.qdt': {arg}"
  for part in arg.splitOn "." do
    if part.isEmpty then
      throw s!"module name has empty component: {arg}"

def parseConfig (parsed : Parsed) : IO Config := do
  let root ← IO.FS.realPath (parsed.flag? "root" |>.map (·.as! String) |>.getD ".")
  let watchMode := parsed.hasFlag "watch"
  let buildSystem := parsed.flag? "build" |>.map (·.as! BuildSystem) |>.getD .shakeC
  let args := parsed.variableArgsAs! String
  if args.isEmpty then
    throw (IO.userError "No modules specified. Usage: qdt [--root DIR] <module>...")
  for arg in args do
    match validateModuleName arg with
    | .ok () => pure ()
    | .error msg => throw (IO.userError msg)
  let files ← args.mapM fun arg => IO.FS.realPath (root / moduleToPath arg)
  return { root, watchMode, buildSystem, files }

end Qdt
