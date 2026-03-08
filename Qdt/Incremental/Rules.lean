module

public import Qdt.Config
public import Qdt.Elab
public import Qdt.Frontend.Desugar
public import Incremental.Shake

@[expose] public section

namespace Qdt

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)
open Frontend (Ast Cst Path SourceMap)
open Frontend.Parser (ParseError)
open Incremental
open Incremental.Shake (Store Memo)

def getFieldString (_structName fieldName : Name) : Option String :=
  if !fieldName.isAtomic then none
  else match fieldName with
  | .str .anonymous s => some s
  | _ => none

open Qdt (parseDefinition parseExample parseAxiom parseImport parseInductive parseStructure)

def buildOwnerIndex (prog : Ast) : HashMap Name Nat × Array Diagnostic := Id.run do
  let .node _ progCs := prog | return (HashMap.emptyWithCapacity 0, #[])
  let mut m : HashMap Name Nat := HashMap.emptyWithCapacity 4096
  let mut diags : Array Diagnostic := #[]
  for h : idx in [:progCs.size] do
    let cmd := progCs[idx]
    let names : List Name :=
      if let some d := parseDefinition cmd then [d.name]
      else if let some a := parseAxiom cmd then [a.name]
      else if let some ind := parseInductive cmd then
        ind.name :: ind.name.str "rec" :: ind.ctors.map (ind.name.append ·.name)
      else if let some s := parseStructure cmd then
        s.name :: s.name.str "mk" :: s.name.str "rec" ::
          s.fields.filterMap fun field => (s.name.str ·) <$> getFieldString s.name field.name
      else if (parseExample cmd).isSome then [(`_example).num idx]
      else []
    for name in names do
      if m.contains name then
        diags := diags.push ⟨[0, idx], .alreadyDefined name⟩
      else
        m := m.insert name idx
  return (m, diags)

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

open Qdt (ElabContext ElabM ElabM.run elabDefinition elabExample elabAxiom elabInductiveCmd elabStructureCmd)

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

def elabAction (cmd : Ast) : ElabM (Option Unit) :=
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
    let diagnostics : Array Diagnostic := parseErrors.map fun err =>
      ⟨cst.pathAtPosition err.pos, .syntaxError err⟩
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
    for cmd in progCs do
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
    let (indexMap, _) ← fetch (Key.declarationIndex filepath)
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
    let elabCtx : ElabContext := {
      filepath
      univParams
      collectHovers := true
      currentDecl := name
      path := [idx]
    }
    let (_, globalEnv, info) ← (elabAction ast).run elabCtx
    return (globalEnv, info)
  | .elabDecl filepath name => some do
    let (indexMap, _) ← fetch (Key.declarationIndex filepath)
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
    let (decls, dupDiags) ← fetch (Key.declarationIndex filepath)
    let mut allDiags := parseDiags ++ dupDiags
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

def populateStore (config : Config) (store : Store Key Val) : IO (Store Key Val) := do
  let mut rawFiles : List FilePath := []
  for dir in config.sourceDirectories do
    rawFiles := rawFiles ++ (← listSrcFiles dir)
  let mut inputFiles : HashSet FilePath := HashSet.emptyWithCapacity rawFiles.length
  let mut store := store
  for file in rawFiles do
    let absPath ← IO.FS.realPath file
    inputFiles := inputFiles.insert absPath
    match store.get? (.text absPath) with
    | some _ => continue
    | none =>
        let text ← IO.FS.readFile absPath
        let memo : Memo Key Val (.text absPath) :=
          { value := text, deps := ∅ }
        store := store.insert (.text absPath) memo
  let inputMemo : Memo Key Val .inputFiles := { value := inputFiles, deps := ∅ }
  store := store.insert .inputFiles inputMemo
  return store

end Qdt
