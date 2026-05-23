module

public import Cli.Basic
public import Lean.Data.Position
public import Qdt.Frontend.Parser
public import Qdt.Frontend.Format

@[expose] public section

open Cli
open System (FilePath)

namespace Qdt

inductive FmtResult where
  | unchanged
  | changed (output : String)
  | parseErrors (errs : Array Frontend.Parser.ParseError)

def formatString (input : String) (width : Nat) : FmtResult :=
  let (cst, errs) := Frontend.Parser.parse input
  if !errs.isEmpty then .parseErrors errs
  else
    let output := Frontend.Format.render cst width
    if input == output then .unchanged else .changed output

def reportParseErrors (label : String) (input : String) (errs : Array Frontend.Parser.ParseError) : IO Unit := do
  let fileMap := Lean.FileMap.ofString input
  for e in errs do
    let ⟨line, col⟩ := fileMap.toPosition ⟨e.pos⟩
    IO.eprintln s!"{label}:{line}:{col}: parse error: {e.msg}"

def atomicWrite (path : FilePath) (content : String) : IO Unit := do
  let dir := path.parent.getD (FilePath.mk ".")
  let base := path.fileName.getD "out"
  let tmp := dir / (s!".{base}.qdt-fmt.tmp")
  IO.FS.writeFile tmp content
  IO.FS.rename tmp path

partial def collectFiles (path : FilePath) : IO (Array FilePath) := do
  let md ← path.metadata
  match md.type with
  | .file => return #[path]
  | .dir =>
      let entries ← path.readDir
      let mut acc : Array FilePath := #[]
      for entry in entries do
        let child := entry.path
        let cmd ← child.metadata
        match cmd.type with
        | .dir =>
            acc := acc ++ (← collectFiles child)
        | .file =>
            if child.extension == some "qdt" then
              acc := acc.push child
        | _ => continue
      return acc
  | _ => return #[]

structure RunStats where
  changed : Nat := 0
  parseErrors : Nat := 0
  ioErrors : Nat := 0

def processFile
    (path : FilePath) (inPlace check diff : Bool) (width : Nat)
    (stats : RunStats) : IO RunStats := do
  let input ← try IO.FS.readFile path catch e =>
    IO.eprintln s!"{path}: {e}"
    return { stats with ioErrors := stats.ioErrors + 1 }
  match formatString input width with
  | .parseErrors errs =>
      reportParseErrors path.toString input errs
      return { stats with parseErrors := stats.parseErrors + 1 }
  | .unchanged => return stats
  | .changed output =>
      if check then
        IO.eprintln s!"{path}: would reformat"
      else if diff then
        IO.println s!"--- {path}"
        IO.println s!"+++ {path}"
        IO.println output
      else if inPlace then
        try atomicWrite path output catch e =>
          IO.eprintln s!"{path}: {e}"
          return { stats with ioErrors := stats.ioErrors + 1 }
      else
        IO.print output
      return { stats with changed := stats.changed + 1 }

def runFmtCmd (parsed : Parsed) : IO UInt32 := do
  let inPlace := parsed.hasFlag "in-place"
  let check := parsed.hasFlag "check"
  let diff := parsed.hasFlag "diff"
  let width := parsed.flag? "width" |>.map (·.as! Nat) |>.getD 100
  let pathArgs := parsed.variableArgsAs! String
  if pathArgs.isEmpty then
    let input ← IO.getStdin >>= IO.FS.Stream.readToEnd
    let label := parsed.flag? "stdin-filepath" |>.map (·.as! String) |>.getD "<stdin>"
    match formatString input width with
    | .parseErrors errs =>
        reportParseErrors label input errs
        return 2
    | .changed out => IO.print out; return 0
    | .unchanged   => IO.print input; return 0
  let mut files : Array FilePath := #[]
  for arg in pathArgs do
    files := files ++ (← collectFiles (FilePath.mk arg))
  let mut stats : RunStats := {}
  for f in files do
    stats ← processFile f inPlace check diff width stats
  if stats.ioErrors > 0 then return 3
  if stats.parseErrors > 0 then return 2
  if check && stats.changed > 0 then return 1
  return 0

def fmtCmd : Cmd := `[Cli|
  fmt VIA runFmtCmd;
  "Format QDT source files"

  FLAGS:
    i, "in-place";                       "Rewrite files in place (atomic)"
    "check";                             "Exit non-zero if any file would change; do not write"
    d, diff;                             "Print a diff-like preview instead of writing"
    w, width : Nat;                      "Target column width (default 100)"
    "stdin-filepath" : String;           "Filename to use when reading from stdin (for error messages)"

  ARGS:
    ...paths : String;                   "Files or directories to format (omit to read from stdin)"
]

end Qdt
