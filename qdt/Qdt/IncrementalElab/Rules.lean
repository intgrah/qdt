import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Control
import Qdt.Config
import Qdt.Elab
import Qdt.Frontend.Desugar
import Qdt.Frontend.Parser
import Qdt.Incremental
import Qdt.IncrementalElab.Query

namespace Qdt.Incremental

open Lean (Name)
open Std (HashSet)
open System (FilePath)
open Frontend

abbrev IT := TaskM Error Val
abbrev IFetch := Fetch Error Val

@[inline] private def fetchQ : ∀ k, IT (Val k) := TaskM.fetch

structure RulesContext where
  config : Config
  importedEnv : GlobalEnv := Std.HashMap.emptyWithCapacity 0
deriving Inhabited

initialize rulesContextRef : IO.Ref RulesContext ← IO.mkRef default

private def getRulesContext : IO RulesContext :=
  rulesContextRef.get

private def setRulesContext (ctx : RulesContext) : IO Unit :=
  rulesContextRef.set ctx

private def setImportedEnv (env : GlobalEnv) : IO Unit := do
  let ctx ← rulesContextRef.get
  rulesContextRef.set { ctx with importedEnv := env }

private def getImportedEnv : IO GlobalEnv := do
  let ctx ← rulesContextRef.get
  return ctx.importedEnv

private def getFieldString (structName fieldName : Name) : EIO Error String := do
  if !fieldName.isAtomic then
    throw (.msg s!"{structName}: field name must be atomic")
  match fieldName with
  | .str .anonymous s => pure s
  | _ => throw (.msg s!"{structName}: field name must be a string identifier")

private def insertOwner
    (m : Std.HashMap Name TopDecl)
    (n : Name)
    (owner : TopDecl) :
    EIO Error (Std.HashMap Name TopDecl) := do
  if m.contains n then
    throw (.msg s!"Duplicate global name: {n}")
  return m.insert n owner

private def buildOwnerIndex (prog : Frontend.Ast.Program) : EIO Error (Std.HashMap Name TopDecl) := do
  let mut m : Std.HashMap Name TopDecl := Std.HashMap.emptyWithCapacity 4096
  for h : idx in [:prog.length] do
    let cmd := prog[idx]
    match cmd with
    | .definition d =>
        let owner := ⟨.definition, d.name⟩
        m ← insertOwner m d.name owner
    | .axiom a =>
        let owner := ⟨.axiom, a.name⟩
        m ← insertOwner m a.name owner
    | .inductive ind =>
        let owner := ⟨.inductive, ind.name⟩
        m ← insertOwner m ind.name owner
        m ← insertOwner m (ind.name.str "rec") owner
        for ctor in ind.ctors do
          m ← insertOwner m (ind.name.append ctor.name) owner
    | .structure s =>
        let owner := ⟨.structure, s.name⟩
        m ← insertOwner m s.name owner
        m ← insertOwner m (s.name.str "mk") owner
        m ← insertOwner m (s.name.str "rec") owner
        for field in s.fields do
          let fname ← getFieldString s.name field.name
          m ← insertOwner m (s.name.str fname) owner
    | .example _ =>
        let owner : TopDecl := ⟨.example, .mkSimple s!"_example_{idx}"⟩
        m ← insertOwner m owner.name owner
    | .import _ => continue
  return m

private def findTopDeclCmd (prog : Frontend.Ast.Program) (decl : TopDecl) : EIO Error Frontend.Ast.Command.Cmd := do
  for h : idx in [:prog.length] do
    let cmd := prog[idx]
    match prog[idx] with
    | .definition d => if decl.kind = .definition && decl.name = d.name then return cmd
    | .axiom a => if decl.kind = .axiom && decl.name = a.name then return cmd
    | .inductive i => if decl.kind = .inductive && decl.name = i.name then return cmd
    | .structure s => if decl.kind = .structure && decl.name = s.name then return cmd
    | .example _ => if decl.kind = .example && decl.name = .mkSimple s!"_example_{idx}" then return cmd
    | .import _ => continue
  throw (.msg s!"Top-level declaration not found: {repr decl}")

private def hashNameTopDeclPairs (m : Std.HashMap Name TopDecl) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, d) => mixHash (hash n) (hash d)

private def hashNameEntryPairs (m : Std.HashMap Name Entry) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, e) => mixHash (hash n) (hash e)

private def hashFilePaths (s : HashSet FilePath) : UInt64 :=
  let paths := s.toList.map (·.toString) |>.mergeSort (· <= ·)
  hash paths

private def hashNames (ns : List Name) : UInt64 :=
  hash <| ns.map hash

def fingerprint : ∀ k, Val k → UInt64
  | .inputFiles, (s : HashSet FilePath) => hashFilePaths s
  | .moduleFile _, (p : Option FilePath) => hash (p.map (·.toString))
  | .moduleImports _, (ns : List Name) => hashNames ns
  | .elabModule _, (env : GlobalEnv) => hashNameEntryPairs env

  | .fileText _, (s : String) => hash s
  | .astProgram _, (p : Frontend.Ast.Program) => hash p
  | .declOwner _, (m : Std.HashMap Name TopDecl) => hashNameTopDeclPairs m
  | .topDeclCmd _ _, (cmd : Frontend.Ast.Command.Cmd) => hash cmd
  | .elabTop _ _, (m : Std.HashMap Name Entry) => hashNameEntryPairs m
  | .entry _ _, (r : Option Entry) => hash r
  | .constTy _ _, (r : Option (Ty 0)) => hash r
  | .constantInfo _ _, (r : Option ConstantInfo) => hash r
  | .constDef _ _, (r : Option (Tm 0)) => hash r
  | .recursorInfo _ _, (r : Option RecursorInfo) => hash r
  | .constructorInfo _ _, (r : Option ConstructorInfo) => hash r
  | .inductiveInfo _ _, (r : Option InductiveInfo) => hash r

private def logElab (decl : TopDecl) : IT PUnit :=
  IO.toEIO Error.ioError <|
    println!"[elab] {repr decl.kind} {decl.name}"

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

def extractImports (prog : Frontend.Ast.Program) : List Name :=
  prog.filterMap fun cmd =>
    match cmd with
    | .import i => some i.moduleName
    | _ => none

def rules : ∀ k, TaskM Error Val (Val k)
  | .inputFiles => do
      let ctx ← IO.toEIO Error.ioError getRulesContext
      let config := ctx.config
      let mut files : HashSet FilePath := HashSet.emptyWithCapacity 1024
      -- Project source directories
      for dir in config.sourceDirectories do
        let dirFiles ← IO.toEIO Error.ioError <| listSrcFiles dir
        for f in dirFiles do
          let absPath ← IO.toEIO Error.ioError <| IO.FS.realPath f
          files := files.insert absPath
      -- Dependencies
      for dep in config.dependencies do
        let depFiles ← IO.toEIO Error.ioError <| listSrcFiles dep.path
        for f in depFiles do
          let absPath ← IO.toEIO Error.ioError <| IO.FS.realPath f
          files := files.insert absPath
      return files

  | .moduleFile modName => do
      let ctx ← IO.toEIO Error.ioError getRulesContext
      let config := ctx.config
      let files : HashSet FilePath ← fetchQ .inputFiles
      let relPath := moduleNameToPath modName
      -- Project source directories
      for dir in config.sourceDirectories do
        let candidate := dir / relPath
        if ← IO.toEIO Error.ioError candidate.pathExists then
          let absPath ← IO.toEIO Error.ioError <| IO.FS.realPath candidate
          if files.contains absPath then
            return some absPath
      -- Dependencies
      for dep in config.dependencies do
        let candidate := dep.path / relPath
        if ← IO.toEIO Error.ioError candidate.pathExists then
          let absPath ← IO.toEIO Error.ioError <| IO.FS.realPath candidate
          if files.contains absPath then
            return some absPath
      return none

  | .moduleImports file => do
      let prog ← fetchQ (.astProgram file)
      return extractImports prog

  | .elabModule file => do
      let imports ← fetchQ (.moduleImports file)
      -- Build up environment from all imports
      let mut globalEnv : GlobalEnv := Std.HashMap.emptyWithCapacity 4096
      for modName in imports.toArray do
        match ← fetchQ (.moduleFile modName) with
        | none =>
            throw (.msg s!"Import not found: {modName}")
        | some depFile =>
            let depEnv ← fetchQ (.elabModule depFile)
            for (name, entry) in depEnv.toList.toArray do
              globalEnv := globalEnv.insert name entry
      IO.toEIO Error.ioError (setImportedEnv globalEnv)
      let owners ← fetchQ (.declOwner file)
      for (_, owner) in owners.toList.toArray do
        let localEnv ← fetchQ (.elabTop file owner)
        for (n, e) in localEnv.toList.toArray do
          globalEnv := globalEnv.insert n e
        IO.toEIO Error.ioError (setImportedEnv globalEnv)
      return globalEnv

  | .fileText file =>
      IO.toEIO Error.ioError <| IO.FS.readFile file
  | .astProgram file => do
      let content ← fetchQ (.fileText file)
      match Frontend.Parser.parse content with
      | .error err =>
          throw (.msg s!"Parse error: {err.msg} at position {err.pos.byteIdx}")
      | .ok cstProg =>
          return Frontend.Cst.Program.desugar cstProg
  | .declOwner file => do
      buildOwnerIndex (← fetchQ (.astProgram file))
  | .topDeclCmd file decl => do
      findTopDeclCmd (← fetchQ (.astProgram file)) decl
  | .elabTop file decl => do
      logElab decl
      let cmd ← fetchQ (.topDeclCmd file decl)
      let selfNames : List Name ←
        match cmd with
        | .definition d => pure [d.name]
        | .axiom a => pure [a.name]
        | .inductive i => pure <|
            i.name
              :: (i.name.str "rec")
              :: (i.ctors.map fun c => i.name.append c.name)
        | .structure s =>
            let projNames ← s.fields.mapM fun f => do
              let fname ← getFieldString s.name f.name
              return s.name.str fname
            pure <|
              s.name
                :: (s.name.str "mk")
                :: (s.name.str "rec")
                :: projNames
        | .example _ => pure []
        | .import _ => pure []
      let coreCtx : CoreContext := { file := some file, selfNames }
      let importedEnv ← IO.toEIO Error.ioError getImportedEnv
      let init : CoreState :=
        {
          modules := Std.HashMap.emptyWithCapacity 8
          importedEnv
          localEnv := Std.HashMap.emptyWithCapacity 128
          errors := #[]
        }
      let action : CoreM CoreState := do
        match cmd with
        | .definition d => elabDefinition d
        | .axiom a => elabAxiom a
        | .inductive i => elabInductiveCmd i
        | .structure s => elabStructureCmd s
        | .example ex => elabExample ex
        | .import _ => pure ()
        get
      let st ← (action.run coreCtx).run' init
      return st.localEnv
  | .entry file name => do
      let owners : Std.HashMap Name TopDecl ← fetchQ (.declOwner file)
      match owners[name]? with
      | none => return none
      | some owner =>
          let env : Std.HashMap Name Entry ← fetchQ (.elabTop file owner)
          return env[name]?
  | .constTy file name =>
      return match ← fetchQ (.entry file name) with
      | some e =>
          match e with
          | .definition info
          | .opaque info
          | .axiom info
          | .recursor info
          | .constructor info
          | .inductive info =>
              some info.ty
      | none => none
  | .constantInfo file name =>
      return match ← fetchQ (.entry file name) with
      | some e =>
          match e with
          | .definition info => some info.toConstantInfo
          | .opaque info => some info.toConstantInfo
          | .axiom info => some info.toConstantInfo
          | .recursor info => some info.toConstantInfo
          | .constructor info => some info.toConstantInfo
          | .inductive info => some info.toConstantInfo
      | none => none
  | .constDef file name =>
      return match ← fetchQ (.entry file name) with
      | some (.definition info) => some info.tm
      | _ => none
  | .recursorInfo file name =>
      return match ← fetchQ (.entry file name) with
      | some (.recursor info) => some info
      | _ => none
  | .constructorInfo file name =>
      return match ← fetchQ (.entry file name) with
      | some (.constructor info) => some info
      | _ => none
  | .inductiveInfo file name =>
      return match ← fetchQ (.entry file name) with
      | some (.inductive info) => some info
      | _ => none

def newEngine : Engine Error Val where
  mkCycleError k := .msg s!"Cycle detected: {repr k}"
  fingerprint
  isInput k :=
    match k with
    | .fileText _ => true
    | .inputFiles => true
    | _ => false

def run
    {α : Type}
    (config : Config)
    (engine : Engine Error Val)
    (task : TaskM Error Val α) :
    IO (Except Error (α × Engine Error Val)) := do
  setRulesContext { config }
  (runWithEngine engine rules task).toIO'

end Qdt.Incremental
