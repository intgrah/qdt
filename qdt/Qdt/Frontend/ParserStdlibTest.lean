import Qdt.Frontend.Parser

open Qdt.Frontend.Parser
open System (FilePath)

private def stdlibRoot : IO FilePath := do
  let cwd ← IO.currentDir
  let root := cwd.parent.getD cwd
  return root / "stdlib"

private partial def qdtFilesIn (dir : FilePath) : IO (Array FilePath) := do
  let entries ← dir.readDir
  let mut acc : Array FilePath := #[]
  for entry in entries do
    let p := entry.path
    let md ← p.metadata
    if md.type == IO.FS.FileType.dir then
      let files ← qdtFilesIn p
      acc := acc ++ files
    else if p.extension == some "qdt" then
      acc := acc.push p
    else
      pure ()
  return acc

private def parseFile (path : FilePath) : IO Unit := do
  let content ← IO.FS.readFile path
  match parse content with
  | .ok _ignored => pure ()
  | .error e =>
      throw <| IO.userError s!"{path}: {e.msg} (byte {e.pos.byteIdx})"

def main : IO Unit := do
  let root ← stdlibRoot
  let entry := root / "Std.qdt"
  let files ← qdtFilesIn (root / "Std")
  for p in files.push entry do
    parseFile p
  println!"parsed {files.size + 1} files successfully"
