module

public import Std.Data.HashMap
public import Std.Data.HashSet

public import Qdt.Config
public import Qdt.Control
public import Qdt.Elab
public import Qdt.Error
public import Qdt.Frontend.Desugar
public import Qdt.Frontend.Parser
public import Qdt.Incremental.Query
public import Incremental.Basic

@[expose] public section

namespace Qdt

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)
open Frontend (Ast Cst Path SourceMap)
open Frontend.Parser (ParseError)
open Incremental

def getFieldString (_structName fieldName : Name) : Option String :=
  if !fieldName.isAtomic then none
  else match fieldName with
  | .str .anonymous s => some s
  | _ => none

open Qdt (parseDefinition parseExample parseAxiom parseImport parseInductive parseStructure)

def buildOwnerIndex (prog : Ast) : HashMap Name Nat := Id.run do
  let .node _ progCs := prog | return HashMap.emptyWithCapacity 0
  let mut m : HashMap Name Nat := HashMap.emptyWithCapacity 4096
  for idx in [:progCs.size] do
    let cmd := progCs[idx]!
    if let some d := parseDefinition cmd then
      m := m.insert d.name idx
    else if let some a := parseAxiom cmd then
      m := m.insert a.name idx
    else if let some ind := parseInductive cmd then
      m := m.insert ind.name idx
      m := m.insert (ind.name.str "rec") idx
      for ctor in ind.ctors do
        m := m.insert (ind.name.append ctor.name) idx
    else if let some s := parseStructure cmd then
      m := m.insert s.name idx
      m := m.insert (s.name.str "mk") idx
      m := m.insert (s.name.str "rec") idx
      for field in s.fields do
        if let some fname := getFieldString s.name field.name then
          m := m.insert (s.name.str fname) idx
    else if let some _ := parseExample cmd then
      let exName := (`_example).num idx
      m := m.insert exName idx
    else
      continue
  return m

partial def listSrcFiles (dir : FilePath) : IO (List FilePath) := do
  let mut result : List FilePath := []
  if ← dir.isDir then
    let entries ← dir.readDir
    for entry in entries do
      let path := entry.path
      if ← path.isDir then
        result := result ++ (← listSrcFiles path)
      else if path.extension == some "qdt" then
        result := path :: result
  return result

open Qdt (CoreContext MetaContext MetaM elabRun elabDefinition elabExample elabAxiom elabInductiveCmd elabStructureCmd)

def getDeclName (cmd : Ast) (idx : Nat) : Name :=
  if let some d := parseDefinition cmd then d.name
  else if let some a := parseAxiom cmd then a.name
  else if let some i := parseInductive cmd then i.name
  else if let some s := parseStructure cmd then s.name
  else if (parseExample cmd).isSome then (`_example).num idx
  else .anonymous

def getCommandUnivParams (cmd : Ast) : List Name :=
  if let some d := parseDefinition cmd then d.univParams
  else if let some a := parseAxiom cmd then a.univParams
  else if let some i := parseInductive cmd then i.univParams
  else if let some s := parseStructure cmd then s.univParams
  else []

def elabAction (cmd : Ast) : OptionT MetaM Unit :=
  if let some d := parseDefinition cmd then elabDefinition d
  else if let some e := parseExample cmd then elabExample e
  else if let some a := parseAxiom cmd then elabAxiom a
  else if let some i := parseInductive cmd then elabInductiveCmd i
  else if let some s := parseStructure cmd then elabStructureCmd s
  else pure ()

def resolveModule (modName : Name) (inputFiles : HashSet FilePath) : Option FilePath :=
  let expectedPath : FilePath :=
    modName.componentsRev.reverse.map toString
    |> String.intercalate "/"
    |> FilePath.mk
    |>.addExtension "qdt"
  inputFiles.toList.find? fun file =>
    file.toString.endsWith expectedPath.toString

def toDiagnostic (cst : Cst) (err : ParseError) : Diagnostic :=
  { path := cst.pathAtPosition err.pos, error := .msg err.msg }

partial def topoSort (files : List FilePath) (adj : HashMap FilePath (List FilePath)) : List FilePath :=
  let rec visit (f : FilePath) (visited : HashSet FilePath) (sorted : List FilePath) : (HashSet FilePath × List FilePath) :=
    if visited.contains f then (visited, sorted)
    else
      let visited := visited.insert f
      let deps := adj.getD f []
      let (visited, sorted) := deps.foldl (fun (v, s) d => visit d v s) (visited, sorted)
      (visited, f :: sorted)

  let (_, sorted) := files.foldl (fun (v, s) f => visit f v s) (HashSet.emptyWithCapacity 0, [])
  sorted.reverse

def tasks : Tasks Monad Key Val
  | .text _ => none
  | .inputFiles => none
  | .cst filepath => some do
    let text ← fetch (Key.text filepath)
    return Frontend.Parser.parse text
  | .astSourceMap filepath => some do
    let (cst, parseErrors) ← fetch (Key.cst filepath)
    let (ast, sourceMap) := Frontend.desugarProgram cst
    let diagnostics := parseErrors.map (toDiagnostic cst)
    return (ast, sourceMap, diagnostics)
  | .ast filepath => some do
    let (ast, _, _) ← fetch (Key.astSourceMap filepath)
    return ast
  | .sourceMap filepath => some do
    let (_, sourceMap, _) ← fetch (Key.astSourceMap filepath)
    return sourceMap
  | .imports filepath => some do
    let prog ← fetch (Key.ast filepath)
    let .node _ progCs := prog | return #[]
    let mut result : Array Name := #[]
    for idx in [:progCs.size] do
      let cmd := progCs[idx]!
      if let some imp := parseImport cmd then
        result := result.push imp.moduleName
    return result
  | .moduleFile modName => some do
    let inputFiles ← fetch Key.inputFiles
    return resolveModule modName inputFiles
  | .transitiveImports filepath => some do
    let imports ← fetch (Key.imports filepath)
    let mut result : HashSet FilePath := HashSet.emptyWithCapacity 0
    for modName in imports do
      if let some path ← fetch (Key.moduleFile modName) then
        result := result.insert path
        let subImports ← fetch (Key.transitiveImports path)
        for p in subImports do
          result := result.insert p
    return result
  | .declarationIndex filepath => some do
    let prog ← fetch (Key.ast filepath)
    return buildOwnerIndex prog
  | .declAst filepath name => some do
    let indexMap ← fetch (Key.declarationIndex filepath)
    match indexMap[name]? with
    | some idx =>
        let prog ← fetch (Key.ast filepath)
        let .node _ progCs := prog | return none
        return some (progCs[idx]!, idx)
    | none => return none
  | .elabCmdAt filepath idx => some do
    let prog ← fetch (Key.ast filepath)
    let ast := match prog with | .node _ cs => cs[idx]! | _ => .missing
    let name := getDeclName ast idx
    let univParams := getCommandUnivParams ast
    let coreCtx : CoreContext := { filepath, univParams, collectHovers := true }
    let metaCtx : MetaContext := { currentDecl := name, path := [idx] }
    let (_, globalEnv, info) ← elabRun coreCtx metaCtx (elabAction ast)
    return (globalEnv, info)
  | .elabDecl filepath name => some do
    let indexMap ← fetch (Key.declarationIndex filepath)
    match indexMap[name]? with
    | some idx =>
        let (env, info) ← fetch (Key.elabCmdAt filepath idx)
        let origin : Origin := { filepath, idx }
        match env[name]? with
        | some constant => return (some (constant, origin), info)
        | none => return (none, info)
    | none => return (none, 1)
  | .lookup filepath name => some do
    let (result, _) ← fetch (Key.elabDecl filepath name)
    return result
  | .lookupInfo filepath name => some do
    let (_, info) ← fetch (Key.elabDecl filepath name)
    return info
  | .constant filepath name => some do
    match ← fetch (Key.lookup filepath name) with
    | some res => return some res
    | none =>
        let transImports ← fetch (Key.transitiveImports filepath)
        for path in transImports do
           match ← fetch (Key.lookup path name) with
           | some res => return some res
           | none => continue
        return none
  | .type filepath name => some do
    match ← fetch (Key.constant filepath name) with
    | some (constant, _) => return constant.ty
    | none => return none
  | .checkFile filepath => some do
    let (_, _, parseDiags) ← fetch (Key.astSourceMap filepath)
    let decls ← fetch (Key.declarationIndex filepath)
    let mut allDiags := parseDiags
    let mut seenIdx : HashSet Nat := HashSet.emptyWithCapacity decls.size
    for (name, idx) in decls.toList do
      if seenIdx.contains idx then continue
      seenIdx := seenIdx.insert idx
      let info ← fetch (Key.lookupInfo filepath name)
      allDiags := allDiags ++ info.diagnostics
    return allDiags
  | .checkProject => some do
      let inputFiles ← fetch Key.inputFiles
      let files := inputFiles.toList

      let mut adj : HashMap FilePath (List FilePath) := HashMap.emptyWithCapacity 0
      for file in files do
        let imports ← fetch (Key.imports file)
        let mut fileDeps := []
        for modName in imports do
          if let some path ← fetch (Key.moduleFile modName) then
            fileDeps := path :: fileDeps
        adj := adj.insert file fileDeps

      let sortedFiles := topoSort files adj

      let mut allDiags : Array Diagnostic := #[]
      for file in sortedFiles do
        let diags ← fetch (Key.checkFile file)
        allDiags := allDiags ++ diags

      return allDiags

def populateStore (config : Config) (store : Store Key Val) : EIO Unit (Store Key Val) := do
  let mut rawFiles : List FilePath := []
  for dir in config.sourceDirectories do
    rawFiles := rawFiles ++ (← (listSrcFiles dir).toEIO (fun _ => ()))
  let mut inputFiles : HashSet FilePath := HashSet.emptyWithCapacity rawFiles.length
  let mut store := store
  for file in rawFiles do
    let absPath ← (IO.FS.realPath file).toEIO (fun _ => ())
    inputFiles := inputFiles.insert absPath
    match store.cache.get? (.text absPath) with
    | some _ => continue
    | none =>
        let text ← (IO.FS.readFile absPath).toEIO (fun _ => ())
        let memo : Memo Key Val (.text absPath) :=
          { value := text, deps := ∅, hash := hash text }
        store := { store with cache := store.cache.insert (.text absPath) memo }
  let inputMemo : Memo Key Val .inputFiles :=
    { value := inputFiles, deps := ∅, hash := hash inputFiles }
  store := { store with cache := store.cache.insert .inputFiles inputMemo }
  return store

def runTask {α : Type} (build : Build Monad Key Val) :
    Store Key Val →
    Task Monad Key Val α →
    EIO Unit (α × Store Key Val) :=
  build tasks

def runWithProfile {α : Type} (store : Store Key Val)
    (task : Task Monad Key Val α) : IO (α × Store Key Val) := do
  let prof ← IO.mkRef (Std.HashMap.emptyWithCapacity 32)
  let result ← (Shake.build Key Val Key.tag prof (onBuildEvent := none) tasks store task).toIO'
  Profile.print prof
  match result with
  | .ok r => return r
  | .error () => throw (IO.Error.userError "cycle detected")

end Qdt
