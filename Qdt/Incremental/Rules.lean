module

public import Qdt.Elab
public import Qdt.Frontend.Desugar
public import Incremental.Parametric

namespace Qdt

set_option warn.sorry false

open Lean (Name)
open Std (DHashMap HashMap HashSet)
open System (FilePath)
open Frontend (Ast SourceMap)
open Frontend.Parser (ParseError)
open Incremental

def getFieldString (_structName fieldName : Name) : Option String :=
  if !fieldName.isAtomic then none
  else match fieldName with
  | .str .anonymous s => some s
  | _ => none

def buildOwnerIndex (prog : Ast) : HashMap Name Nat × Array Diagnostic := Id.run do
  let .node _ progCs := prog | return (HashMap.emptyWithCapacity 0, #[])
  let mut m : HashMap Name Nat := HashMap.emptyWithCapacity 4096
  let mut diags : Array Diagnostic := #[]
  for h : idx in [:progCs.size] do
    let cmd := progCs[idx]
    let names : List Name :=
      if let some d := Definition.parse cmd then [d.name]
      else if let some a := Axiom.parse cmd then [a.name]
      else if let some ind := Inductive.parse cmd then
        ind.name :: ind.recName :: ind.ctors.map (ind.name.append ·.name)
      else if let some s := Structure.parse cmd then
        s.name :: s.mkName :: s.recName ::
          s.fields.filterMap fun field => (s.name.str ·) <$> getFieldString s.name field.name
      else if (Example.parse cmd).isSome then [(`_example).num idx]
      else []
    for name in names do
      if m.contains name then
        diags := diags.push ⟨[0, idx], .alreadyDefined name⟩
      else
        m := m.insert name idx
  return (m, diags)

def getDeclName (cmd : Ast) (idx : Nat) : Name :=
  if let some d := Definition.parse cmd then d.name
  else if let some a := Axiom.parse cmd then a.name
  else if let some i := Inductive.parse cmd then i.name
  else if let some s := Structure.parse cmd then s.name
  else if (Example.parse cmd).isSome then (`_example).num idx
  else .anonymous

def getOwner (cmd : Ast) : Option Name :=
  if let some d := Definition.parse cmd then some d.name
  else if let some a := Axiom.parse cmd then some a.name
  else if let some i := Inductive.parse cmd then some i.name
  else if let some s := Structure.parse cmd then some s.name
  else none

def getCommandUnivParams (cmd : Ast) : List Name :=
  if let some d := Definition.parse cmd then d.univParams
  else if let some e := Example.parse cmd then e.univParams
  else if let some a := Axiom.parse cmd then a.univParams
  else if let some i := Inductive.parse cmd then i.univParams
  else if let some s := Structure.parse cmd then s.univParams
  else []

def elabAction (q₀ : Key) (cmd : Ast) : ElabM q₀ (Option Unit) :=
  if let some d := Definition.parse cmd then d.elab q₀
  else if let some e := Example.parse cmd then e.elab q₀
  else if let some a := Axiom.parse cmd then a.elab q₀
  else if let some i := Inductive.parse cmd then i.elab q₀
  else if let some s := Structure.parse cmd then s.elab q₀
  else return

def resolveModule (modName : Name) (inputFiles : HashSet FilePath) : Option FilePath :=
  let expectedPath : FilePath :=
    modName.componentsRev.reverse.map toString
    |> String.intercalate "/"
    |> FilePath.mk
    |>.addExtension "qdt"
  let expectedStr := expectedPath.toString
  let isStrictSuffix (path : String) : Bool :=
    path == expectedStr ||
    path.endsWith ("/" ++ expectedStr)
  inputFiles.toList.find? fun file =>
    isStrictSuffix file.toString

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

public def tasks : MTasks config
  | .astSourceMap filepath => do
    let some text ← (MTask.input (ℭ := config) (q₀ := Key.astSourceMap filepath) (InputKey.text filepath) : MTask config (Key.astSourceMap filepath) _) | do
      let (ast, sourceMap) := Frontend.desugarProgram (Frontend.Parser.parse "").1
      return (ast, sourceMap, #[])
    let (cst, parseErrors) := Frontend.Parser.parse text
    let (ast, sourceMap) := Frontend.desugarProgram cst
    let diagnostics : Array Diagnostic := parseErrors.map fun err =>
      let path := match sourceMap.astPathAtPosition err.pos with
        | some p => p
        | none => []
      ⟨path, .syntaxError err⟩
    return (ast, sourceMap, diagnostics)
  | .ast filepath => do
    let (ast, _, _) ← (MTask.fetch (ℭ := config) (q₀ := Key.ast filepath) (Key.astSourceMap filepath) sorry : MTask config (Key.ast filepath) _)
    return ast
  | .sourceMap filepath => do
    let (_, sourceMap, _) ← (MTask.fetch (ℭ := config) (q₀ := Key.sourceMap filepath) (Key.astSourceMap filepath) sorry : MTask config (Key.sourceMap filepath) _)
    return sourceMap
  | .imports filepath => do
    let prog ← (MTask.fetch (ℭ := config) (q₀ := Key.imports filepath) (Key.ast filepath) sorry : MTask config (Key.imports filepath) _)
    let .node _ progCs := prog | return #[]
    let mut result : Array Name := #[]
    for cmd in progCs do
      if let some imp := Import.parse cmd then
        result := result.push imp.moduleName
    return result
  | .moduleFile modName => do
    let some inputFiles ← (MTask.input (ℭ := config) (q₀ := Key.moduleFile modName) InputKey.inputFiles : MTask config (Key.moduleFile modName) _) | return none
    return resolveModule modName inputFiles
  | .transitiveImports filepath => do
    let imports ← (MTask.fetch (ℭ := config) (q₀ := Key.transitiveImports filepath) (Key.imports filepath) sorry : MTask config (Key.transitiveImports filepath) _)
    let mut result : HashSet FilePath := HashSet.emptyWithCapacity 0
    for modName in imports do
      if let some path ← (MTask.fetch (ℭ := config) (q₀ := Key.transitiveImports filepath) (Key.moduleFile modName) sorry : MTask config (Key.transitiveImports filepath) _) then
        result := result.insert path
        let subImports ← (MTask.fetch (ℭ := config) (q₀ := Key.transitiveImports filepath) (Key.transitiveImports path) sorry : MTask config (Key.transitiveImports filepath) _)
        for p in subImports do
          result := result.insert p
    return result
  | .declarationIndex filepath => do
    let prog ← (MTask.fetch (ℭ := config) (q₀ := Key.declarationIndex filepath) (Key.ast filepath) sorry : MTask config (Key.declarationIndex filepath) _)
    return buildOwnerIndex prog
  | .declScope filepath name currentDecl => do
    let (indexMap, _) ← (MTask.fetch (ℭ := config) (q₀ := Key.declScope filepath name currentDecl) (Key.declarationIndex filepath) sorry : MTask config (Key.declScope filepath name currentDecl) _)
    match indexMap[name]?, indexMap[currentDecl]? with
    | some nameIdx, some currentIdx => return nameIdx < currentIdx
    | _, _ => return true
  | .declAst filepath name => do
    let (indexMap, _) ← (MTask.fetch (ℭ := config) (q₀ := Key.declAst filepath name) (Key.declarationIndex filepath) sorry : MTask config (Key.declAst filepath name) _)
    match indexMap[name]? with
    | some idx =>
        let prog ← (MTask.fetch (ℭ := config) (q₀ := Key.declAst filepath name) (Key.ast filepath) sorry : MTask config (Key.declAst filepath name) _)
        let .node _ progCs := prog | return none
        return progCs[idx]?
    | none => return none
  | .elabOwner filepath owner => do
    let some ast ← (MTask.fetch (ℭ := config) (q₀ := Key.elabOwner filepath owner) (Key.declAst filepath owner) sorry : MTask config (Key.elabOwner filepath owner) _)
      | return (∅, 1)
    let univParams := getCommandUnivParams ast
    let elabCtx : ElabContext := {
      filepath
      univParams
      collectHovers := true
      currentDecl := owner
      path := []
    }
    let (_, globalEnv, info) ← (elabAction (Key.elabOwner filepath owner) ast).run (Key.elabOwner filepath owner) elabCtx
    return (globalEnv, info)
  | .elabDecl filepath name => do
    let some ast ← (MTask.fetch (ℭ := config) (q₀ := Key.elabDecl filepath name) (Key.declAst filepath name) sorry : MTask config (Key.elabDecl filepath name) _)
      | return (none, 1)
    match getOwner ast with
    | some owner =>
        let (globalEnv, info) ← (MTask.fetch (ℭ := config) (q₀ := Key.elabDecl filepath name) (Key.elabOwner filepath owner) sorry : MTask config (Key.elabDecl filepath name) _)
        return (globalEnv[name]?, info)
    | none =>
        let univParams := getCommandUnivParams ast
        let elabCtx : ElabContext := {
          filepath
          univParams
          collectHovers := true
          currentDecl := name
          path := []
        }
        let (_, globalEnv, info) ← (elabAction (Key.elabDecl filepath name) ast).run (Key.elabDecl filepath name) elabCtx
        return (globalEnv[name]?, info)
  | .lookup filepath name => do
    let (result, _) ← (MTask.fetch (ℭ := config) (q₀ := Key.lookup filepath name) (Key.elabDecl filepath name) sorry : MTask config (Key.lookup filepath name) _)
    return result
  | .lookupInfo filepath name => do
    let (_, info) ← (MTask.fetch (ℭ := config) (q₀ := Key.lookupInfo filepath name) (Key.elabDecl filepath name) sorry : MTask config (Key.lookupInfo filepath name) _)
    return info
  | .constant filepath name => do
    match ← (MTask.fetch (ℭ := config) (q₀ := Key.constant filepath name) (Key.lookup filepath name) sorry : MTask config (Key.constant filepath name) _) with
    | some res => return some res
    | none =>
        let transImports ← (MTask.fetch (ℭ := config) (q₀ := Key.constant filepath name) (Key.transitiveImports filepath) sorry : MTask config (Key.constant filepath name) _)
        for path in transImports do
           match ← (MTask.fetch (ℭ := config) (q₀ := Key.constant filepath name) (Key.lookup path name) sorry : MTask config (Key.constant filepath name) _) with
           | some res => return some res
           | none => continue
        return none
  | .type filepath name => do
    match ← (MTask.fetch (ℭ := config) (q₀ := Key.type filepath name) (Key.constant filepath name) sorry : MTask config (Key.type filepath name) _) with
    | some constant => return some constant.toConstantInfo
    | none => return none
  | .eval _filepath _name _univs => do
    return none
  | .checkFile filepath => do
    let (_, _, parseDiags) ← (MTask.fetch (ℭ := config) (q₀ := Key.checkFile filepath) (Key.astSourceMap filepath) sorry : MTask config (Key.checkFile filepath) _)
    let (decls, dupDiags) ← (MTask.fetch (ℭ := config) (q₀ := Key.checkFile filepath) (Key.declarationIndex filepath) sorry : MTask config (Key.checkFile filepath) _)
    let mut allDiags := parseDiags ++ dupDiags
    let mut seenIdx : HashSet Nat := HashSet.emptyWithCapacity decls.size
    for (name, idx) in decls.toList do
      if seenIdx.contains idx then continue
      seenIdx := seenIdx.insert idx
      let info ← (MTask.fetch (ℭ := config) (q₀ := Key.checkFile filepath) (Key.lookupInfo filepath name) sorry : MTask config (Key.checkFile filepath) _)
      allDiags := allDiags ++ info.diagnostics.map fun d => { d with path := d.path ++ [idx] }
    return allDiags
  | .checkProject => do
      let some inputFiles ← (MTask.input (ℭ := config) (q₀ := Key.checkProject) InputKey.inputFiles : MTask config Key.checkProject _) | return #[]
      let files := inputFiles.toList

      let mut adj : HashMap FilePath (List FilePath) := HashMap.emptyWithCapacity 0
      for file in files do
        let imports ← (MTask.fetch (ℭ := config) (q₀ := Key.checkProject) (Key.imports file) sorry : MTask config Key.checkProject _)
        let mut fileDeps := []
        for modName in imports do
          if let some path ← (MTask.fetch (ℭ := config) (q₀ := Key.checkProject) (Key.moduleFile modName) sorry : MTask config Key.checkProject _) then
            fileDeps := path :: fileDeps
        adj := adj.insert file fileDeps

      let sortedFiles := topoSort files adj

      let mut allDiags : Array Diagnostic := #[]
      for file in sortedFiles do
        let diags ← (MTask.fetch (ℭ := config) (q₀ := Key.checkProject) (Key.checkFile file) sorry : MTask config Key.checkProject _)
        allDiags := allDiags ++ diags

      return allDiags

end Qdt
