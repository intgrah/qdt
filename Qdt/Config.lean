import Lake.Toml

namespace Qdt

open System (FilePath)
open Lake.Toml

structure Config where
  entry : Option String
  sourceDirectories : Array FilePath
  watchMode : Bool := false
  projectRoot : Option FilePath := none
deriving Repr

namespace Config

def empty : Config where
  entry := none
  sourceDirectories := #["."]
  watchMode := false
  projectRoot := none

def fromTomlTable (table : Table) : Config where
  entry :=
    match table.find? `entry with
    | some (Value.string _ s) => some s
    | _ => none
  sourceDirectories :=
    match table.find? `«source-directories» with
    | some (Value.array _ vs) =>
        vs.filterMap fun v =>
          match v with
          | Value.string _ s => some s
          | _ => none
    | _ => #["."]
  watchMode := false
  projectRoot := none

def fromTomlFile (path : FilePath) : IO Config := do
  let contents ← IO.FS.readFile path
  let fileMap := Lean.FileMap.ofString contents
  let ictx : Lean.Parser.InputContext := {
    inputString := contents
    fileName := path.toString
    fileMap := fileMap
  }
  match ← loadToml ictx |>.toBaseIO with
  | .ok table =>
      let config := fromTomlTable table
      let projectRoot := path.parent
      return { config with projectRoot }
  | .error log =>
      let msgs ← log.toList.mapM fun m => m.data.toString
      throw <| IO.userError s!"Failed to parse {path}: {String.intercalate "\n" msgs}"

def load : IO Config := do
  let cwd ← IO.currentDir
  let rec findToml (dir : FilePath) : Nat → IO (Option FilePath)
    | 0 => return none
    | fuel + 1 => do
        let candidate := dir / "qdt.toml"
        if ← candidate.pathExists then
          return some candidate
        let parent := dir / ".."
        let parentNorm ← IO.FS.realPath parent
        let dirNorm ← IO.FS.realPath dir
        if parentNorm == dirNorm then
          return none
        findToml parent fuel
  match ← findToml cwd 100 with
  | some tomlPath =>
      IO.eprintln s!"[config] Loading {tomlPath}"
      fromTomlFile tomlPath
  | none => pure Config.empty

def moduleToPath (modName : String) : FilePath :=
  let parts := modName.splitOn "."
  let pathStr := String.intercalate "/" parts
  FilePath.mk pathStr |>.addExtension "qdt"

end Config

end Qdt
