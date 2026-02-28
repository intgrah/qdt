import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Config
import Qdt.Control
import Qdt.Elab
import Qdt.Error
import Qdt.Frontend.Desugar
import Qdt.Frontend.Parser
import Qdt.Incremental.Basic
import Qdt.Incremental.Query

namespace Qdt.Incremental

open Lean (Name)
open Std (HashMap HashSet)
open System (FilePath)

private def getFieldString (_structName fieldName : Name) : Option String :=
  if !fieldName.isAtomic then none
  else match fieldName with
  | .str .anonymous s => some s
  | _ => none

open Frontend (Ast SourceMap)
open Qdt (parseDefinition parseExample parseAxiom parseImport parseInductive parseStructure)

private def buildOwnerIndex (prog : Array Ast) : HashMap Name Name := Id.run do
  let mut m : HashMap Name Name := HashMap.emptyWithCapacity 4096
  for h : idx in [:prog.size] do
    let cmd := prog[idx]
    if let some d := parseDefinition cmd then
      m := m.insert d.name d.name
    else if let some a := parseAxiom cmd then
      m := m.insert a.name a.name
    else if let some ind := parseInductive cmd then
      m := m.insert ind.name ind.name
      m := m.insert (ind.name.str "rec") ind.name
      for ctor in ind.ctors do
        m := m.insert (ind.name.append ctor.name) ind.name
    else if let some s := parseStructure cmd then
      m := m.insert s.name s.name
      m := m.insert (s.name.str "mk") s.name
      m := m.insert (s.name.str "rec") s.name
      for field in s.fields do
        if let some fname := getFieldString s.name field.name then
          m := m.insert (s.name.str fname) s.name
    else if let some _ := parseExample cmd then
      let exName := (`_example).num idx
      m := m.insert exName exName
    else
      continue
  return m

private def getDeclNames (prog : Array Ast) : List Name := Id.run do
  let mut result : List Name := []
  for h : idx in [:prog.size] do
    let cmd := prog[idx]
    if let some d := parseDefinition cmd then
      result := d.name :: result
    else if let some a := parseAxiom cmd then
      result := a.name :: result
    else if let some i := parseInductive cmd then
      result := i.name :: result
    else if let some s := parseStructure cmd then
      result := s.name :: result
    else if let some _ := parseExample cmd then
      result := (`_example).num idx :: result
  return result.reverse

private def findDeclAst (prog : Array Ast) (declName : Name) : Option (Nat × Ast) := Id.run do
  for h : idx in [:prog.size] do
    let cmd := prog[idx]
    if let some d := parseDefinition cmd then
      if d.name == declName then return some (idx, cmd)
    else if let some a := parseAxiom cmd then
      if a.name == declName then return some (idx, cmd)
    else if let some i := parseInductive cmd then
      if i.name == declName then return some (idx, cmd)
    else if let some s := parseStructure cmd then
      if s.name == declName then return some (idx, cmd)
    else if let some _ := parseExample cmd then
      if (`_example).num idx == declName then return some (idx, cmd)
  return none

private def getSelfNames (cmd : Ast) : List Name :=
  if let some d := parseDefinition cmd then [d.name]
  else if let some a := parseAxiom cmd then [a.name]
  else if let some i := parseInductive cmd then
    i.name
      :: (i.name.str "rec")
      :: (i.ctors.map fun c => i.name.append c.name)
  else if let some s := parseStructure cmd then
    let projNames := s.fields.filterMap fun f =>
      (getFieldString s.name f.name).map (s.name.str ·)
    s.name
      :: (s.name.str "mk")
      :: (s.name.str "rec")
      :: projNames
  else []

private def prefixElabInfo (cmdIdx : Nat) (info : ElabInfo) : ElabInfo :=
  { diagnostics := info.diagnostics.map fun d => { d with path := d.path ++ [cmdIdx] }
    types := info.types.map fun t => { t with path := t.path ++ [cmdIdx] } }

instance {α} [Hashable α] : Hashable (HashMap Name α) where
  hash m := hash <| m.toList.map fun (n, d) => mixHash (hash n) (hash d)

def fingerprint : ∀ k, Val k → UInt64
  | .inputFiles, (s : HashSet FilePath) =>
    hash <| s.toList.map FilePath.toString |>.mergeSort (· ≤ ·)
  | .moduleFile .., (p : Option FilePath) => hash p
  | .moduleImports .., (ns : List Name) => hash ns
  | .importedEnv .., (env : Global) => hash env
  | .fileText .., (s : String) => hash s
  | .astProgram .., (p : Array Ast) => hash p
  | .sourceMap .., (sm : SourceMap) => hash sm
  | .declOwner .., (m : HashMap Name Name) => hash m
  | .elabCmd .., ((m, info) : HashMap Name Entry × ElabInfo) => mixHash (hash m) (hash info)
  | .elabModule .., ((env, info) : Global × ElabInfo) => mixHash (hash env) (hash info)
  | .entry .., (r : Option Entry) => hash r

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

def moduleNameToPath (modName : Name) : FilePath :=
  let segments := modName.componentsRev.reverse.map toString
  FilePath.mk (String.intercalate "/" segments) |>.addExtension "qdt"

def extractImports (prog : Array Ast) : List Name :=
  prog.toList.filterMap fun cmd =>
    if let some i := parseImport cmd then some i.moduleName else none

partial def collectTransitiveImports (visited : HashSet FilePath) (modName : Name) : TaskM Val (HashSet FilePath) := do
  match ← fetchQ (.moduleFile modName) with
  | none => return visited
  | some depFile =>
      if visited.contains depFile then
        return visited
      else
        let visited := visited.insert depFile
        let depImports ← fetchQ (.moduleImports depFile)
        depImports.toArray.foldlM (init := visited) fun vis nm =>
          collectTransitiveImports vis nm

def rules : ∀ k, TaskM Val (Val k)
  | .inputFiles => do
      let ctx ← readThe BaseContext
      let config := ctx.config
      let mut files : HashSet FilePath := HashSet.emptyWithCapacity 1024
      for dir in config.sourceDirectories do
        let dirFiles ← IO.toEIO (fun _ => ()) <| listSrcFiles dir
        for f in dirFiles do
          let absPath ← IO.toEIO (fun _ => ()) <| IO.FS.realPath f
          files := files.insert absPath
      return files

  | .moduleFile modName => do
      let ctx ← readThe BaseContext
      let config := ctx.config
      let files : HashSet FilePath ← fetchQ .inputFiles
      let relPath := moduleNameToPath modName
      for dir in config.sourceDirectories do
        let candidate := dir / relPath
        if ← IO.toEIO (fun _ => ()) candidate.pathExists then
          let absPath ← IO.toEIO (fun _ => ()) <| IO.FS.realPath candidate
          if files.contains absPath then
            return some absPath
      return none

  | .moduleImports filepath => do
      let prog ← fetchQ (.astProgram filepath)
      return extractImports prog

  | .importedEnv filepath => do
      let imports ← fetchQ (.moduleImports filepath)
      let mut globalEnv : Global := HashMap.emptyWithCapacity 4096
      for modName in imports.toArray do
        match ← fetchQ (.moduleFile modName) with
        | none => continue
        | some depFile =>
            let (depEnv, _) ← fetchQ (.elabModule depFile)
            for (name, entry) in depEnv.toList.toArray do
              globalEnv := globalEnv.insert name entry
      return globalEnv

  | .fileText filepath => do
      let ctx ← readThe BaseContext
      match ctx.overrides[filepath]? with
      | some text => return text
      | none => IO.toEIO (fun _ => ()) <| IO.FS.readFile filepath

  | .astProgram filepath => do
      let content ← fetchQ (.fileText filepath)
      match Frontend.Parser.parse content with
      | .error _err => return #[]
      | .ok cstProg =>
          let (astProg, _sourceMap) := Frontend.desugarProgram cstProg
          return astProg

  | .sourceMap filepath => do
      let content ← fetchQ (.fileText filepath)
      match Frontend.Parser.parse content with
      | .error _err => return ⟨{}, {}⟩
      | .ok cstProg =>
          let (_astProg, sourceMap) := Frontend.desugarProgram cstProg
          return sourceMap

  | .declOwner filepath => do
      let prog ← fetchQ (.astProgram filepath)
      return buildOwnerIndex prog

  | .elabCmd filepath declName => do
      let prog ← fetchQ (.astProgram filepath)
      let some (_, cmd) := findDeclAst prog declName
        | return (∅, { diagnostics := #[], types := #[] })
      IO.toEIO (fun _ => ()) <|
        IO.eprintln s!"[elab] {declName}"
      let selfNames := getSelfNames cmd
      let moduleImports ← fetchQ (.moduleImports filepath)
      let mut importFiles : HashSet FilePath := HashSet.emptyWithCapacity 64
      let mut missingImports : Array Name := #[]
      for modName in moduleImports.toArray do
        match ← fetchQ (.moduleFile modName) with
        | none => missingImports := missingImports.push modName
        | some _ => importFiles ← collectTransitiveImports importFiles modName
      let importedEnv : Global ← fetchQ (.importedEnv filepath)
      let coreCtx : CoreContext := { file := some filepath, selfNames, imports := importFiles, sourceMap := ⟨{}, {}⟩ }
      let init : CoreState :=
        {
          modules := HashMap.emptyWithCapacity 8
          localEnv := HashMap.emptyWithCapacity 128
          importedEnv
          errors := #[]
        }
      let action : CoreM CoreState := do
        for modName in missingImports do
          tell ({ diagnostics := #[{ path := [], error := .msg s!"Import not found: {modName}" }], types := #[] } : ElabInfo)
        if let some d := parseDefinition cmd then elabDefinition d
        else if let some a := parseAxiom cmd then elabAxiom a
        else if let some i := parseInductive cmd then elabInductiveCmd i
        else if let some s := parseStructure cmd then elabStructureCmd s
        else if let some ex := parseExample cmd then elabExample ex
        else pure ()
        get
      let ((result, elabInfo), st) ← ((action.run coreCtx).run.run).run init
      let localEnv := match result with
        | .ok s => s.localEnv
        | .error _ => st.localEnv
      return (localEnv, elabInfo)

  | .elabModule filepath => do
      let prog ← fetchQ (.astProgram filepath)
      let declNames := getDeclNames prog
      let mut globalEnv ← fetchQ (.importedEnv filepath)
      let mut allInfo : ElabInfo := { diagnostics := #[], types := #[] }
      for declName in declNames do
        let (localEnv, info) ← fetchQ (.elabCmd filepath declName)
        for (n, e) in localEnv.toList.toArray do
          globalEnv := globalEnv.insert n e
        let some (cmdIdx, _) := findDeclAst prog declName | continue
        allInfo := allInfo * prefixElabInfo cmdIdx info
      return (globalEnv, allInfo)

  | .entry filepath name => do
      let owners : HashMap Name Name ← fetchQ (.declOwner filepath)
      match owners[name]? with
      | none => return none
      | some ownerName =>
          let (env, _) ← fetchQ (.elabCmd filepath ownerName)
          return env[name]?


def newEngine : Engine Val where
  fingerprint
  isInput k :=
    match k with
    | .fileText _ => true
    | .inputFiles => true
    | _ => false

protected def run {α} :=
  runWithEngine (α := α) rules

end Qdt.Incremental
