module

public import Cli.Basic
public import FSWatch.Manager
public import Qdt.Incremental.Rules

@[expose] public section

namespace Qdt

open Cli
open Qdt
open Incremental
open Incremental.Shake (Store Memo)
open System (FilePath)

def posToLineCol (text : String) (pos : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut col := 1
  let mut i := 0
  for c in text.toList do
    if i ≥ pos then return (line, col)
    i := i + 1
    if c == '\n' then
      line := line + 1
      col := 1
    else
      col := col + 1
  return (line, col)

def resolveSpan (sm : Frontend.SourceMap) (cst : Frontend.Cst) (path : Frontend.Path) :
    Option Frontend.Span := Id.run do
  let fwd := path.reverse
  for len in (List.range fwd.length).reverse do
    if let some cstPath := sm.astToCst[fwd.take (len + 1)]? then
      return cst.spanAtPath cstPath
  return none

def Diagnostic.format (file : FilePath) (text : String) (sm : Frontend.SourceMap)
    (cst : Frontend.Cst) (d : Diagnostic) : String :=
  match resolveSpan sm cst d.path with
  | some span =>
      let (line, col) := posToLineCol text span.startPos
      s!"{file}:{line}:{col}: error: {d.error}"
  | none =>
      s!"{file}: error: {d.error}"

def checkModule (store : Store Key Val) (filepath : FilePath) : Array String := Id.run do
  let some transImports := store.cache.get? (Key.transitiveImports filepath)
    | return #[s!"{filepath}: error: missing transitive imports"]
  let allFiles := transImports.value.toList ++ [filepath]
  let mut msgs : Array String := #[]
  for file in allFiles do
    let some diagsMemo := store.cache.get? (Key.checkFile file) | continue
    let diags := diagsMemo.value
    if diags.isEmpty then continue
    let some textMemo := store.cache.get? (Key.text file) | continue
    let some asmMemo := store.cache.get? (Key.astSourceMap file) | continue
    let text := textMemo.value
    let (_, sm, _) := asmMemo.value
    let some cstMemo := store.cache.get? (Key.cst file) | continue
    let (cst, _) := cstMemo.value
    for d in diags do
      msgs := msgs.push (d.format file text sm cst)
  return msgs

def runOnce (config : Config) (store : Store Key Val) (filepath : FilePath) :
    IO (Array String × Store Key Val) := do
  let store ← match ← (populateStore config store).toIO' with
    | .ok s => pure s
    | .error () => pure store
  let (transImports, store) ← match Shake.build tasks (Key.transitiveImports filepath) store with
    | .ok (v, s) => pure (v, s)
    | .error _ => return (#["[error] cycle detected"], store)
  let allFiles := transImports.toList ++ [filepath]
  let keys := allFiles.map Key.checkFile
  match keys.foldlM (fun s k => Prod.snd <$> Shake.build tasks k s) store with
  | .ok store =>
      let msgs := checkModule store filepath
      return (msgs, store)
  | .error _ => return (#["[error] cycle detected"], store)

def watchLoop (config : Config) (store : Store Key Val) (entryFile : FilePath) : IO Unit := do
  let (msgs, initialStore) ← runOnce config store entryFile
  for msg in msgs do IO.println msg
  let storeRef ← IO.mkRef initialStore
  let pending ← IO.mkRef #[]

  FSWatch.Manager.withManager fun m => do
    for dir in config.sourceDirectories do
      let _ ← m.watchTree dir (predicate := fun e => e.path.toString.endsWith ".qdt") fun e => do
        pending.modify (·.push e.path)

    while true do
      IO.sleep 50
      let pendingFiles ← pending.modifyGet (·, #[])
      if !pendingFiles.isEmpty then
        let mut s ← storeRef.get
        let mut changedKeys : Std.HashSet Key := ∅
        for file in pendingFiles do
          let text ← IO.FS.readFile file
          let memo : Memo Key Val (.text file) := { value := text, deps := ∅ }
          s := { s with cache := s.cache.insert (.text file) memo }
          changedKeys := changedKeys.insert (.text file)
        s := Shake.invalidate s changedKeys
        let (msgs, s') ← runOnce config s entryFile
        for msg in msgs do IO.println msg
        storeRef.set s'

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

  let cliArg := parsed.variableArgsAs? String >>= (·[0]?)

  let profileMode := parsed.hasFlag "profile"
  let mut config ← Config.load

  if let some dir := sourceDir then
    config := { config with sourceDirectories := #[⟨dir⟩] }
  if watchMode then
    config := { config with watchMode := true }

  let mut filePath ← resolveEntryFile config cliArg
  filePath ← IO.FS.realPath filePath

  IO.eprintln s!"[config] Entry: {filePath}"
  IO.eprintln s!"[config] Source directories: {config.sourceDirectories}"

  let store : Store Key Val := {}

  if config.watchMode then
    watchLoop config store filePath
    return 0
  else
    let t0 ← IO.monoMsNow
    let (msgs, _) ← runOnce config store filePath
    for msg in msgs do
      IO.println msg
    let t1 ← IO.monoMsNow
    if msgs.isEmpty then
      IO.eprintln s!"OK ({t1 - t0}ms)"
      return 0
    else
      IO.eprintln s!"{msgs.size} error(s) ({t1 - t0}ms)"
      return 1

def cmd : Cmd :=
  Cmd.mk
    (name := "qdt")
    (version? := none)
    (description := "Query-based Dependent Type elaborator")
    (flags := #[
      ⟨some "s", "source", "source directory", String⟩,
      Flag.paramless (longName := "watch") (description := "Enable watch mode"),
      { longName := "watch-dir", description := "Add directory to watch", «type» := String },
      Flag.paramless (longName := "profile") (description := "Print query profile table after build")
    ])
    (variableArg? := some { name := "module", description := "Entry module", «type» := String })
    (run := run)

end Qdt

def main : List String → IO UInt32 :=
  Qdt.cmd.validate
