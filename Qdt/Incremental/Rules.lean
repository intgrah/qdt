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
open Frontend

abbrev fetchQ : ∀ k, TaskM Error Val (Val k) := TaskM.fetch

private initialize rulesContextRef : IO.Ref Config ← IO.mkRef default

private initialize fileTextOverridesRef : IO.Ref (HashMap FilePath String) ←
  IO.mkRef (HashMap.emptyWithCapacity 32)

def setFileTextOverride (filepath : FilePath) (text : String) : IO Unit :=
  fileTextOverridesRef.modify (·.insert filepath text)

def eraseFileTextOverride (filepath : FilePath) : IO Unit :=
  fileTextOverridesRef.modify (·.erase filepath)

def getFileTextOverride? (filepath : FilePath) : IO (Option String) :=
  fileTextOverridesRef.get >>= fun m => return m[filepath]?

def getFileText (filepath : FilePath) : IO String := do
  match ← getFileTextOverride? filepath with
  | some text => return text
  | none => IO.FS.readFile filepath

private def getFieldString (structName fieldName : Name) : EIO Error String := do
  if !fieldName.isAtomic then
    throw (.msg s!"{structName}: field name must be atomic")
  match fieldName with
  | .str .anonymous s => pure s
  | _ => throw (.msg s!"{structName}: field name must be a string identifier")

private def insertOwner
    (m : HashMap Name TopDecl)
    (n : Name)
    (owner : TopDecl) :
    EIO Error (HashMap Name TopDecl) := do
  if m.contains n then
    throw (.msg s!"Duplicate global name: {n}")
  return m.insert n owner

private def buildOwnerIndex (prog : Frontend.Ast.Program) : EIO Error (HashMap Name TopDecl) := do
  let mut m : HashMap Name TopDecl := HashMap.emptyWithCapacity 4096
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
        let owner : TopDecl := ⟨.example, (`_example).num idx⟩
        m ← insertOwner m owner.name owner
    | .import _ => continue
  return m

private def buildDeclOrdering (prog : Frontend.Ast.Program) : List TopDecl :=
  let rec go (cmds : List Frontend.Ast.Command.Cmd) (idx : Nat) (acc : List TopDecl) : List TopDecl :=
    match cmds with
    | [] => acc.reverse
    | cmd :: rest =>
        let acc' := match cmd with
          | .definition d => ⟨.definition, d.name⟩ :: acc
          | .axiom a => ⟨.axiom, a.name⟩ :: acc
          | .inductive i => ⟨.inductive, i.name⟩ :: acc
          | .structure s => ⟨.structure, s.name⟩ :: acc
          | .example _ => ⟨.example, (`_example).num idx⟩ :: acc
          | .import _ => acc
        go rest (idx + 1) acc'
  go prog 0 []

private def hashNameTopDeclPairs (m : HashMap Name TopDecl) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, d) => mixHash (hash n) (hash d)

private def hashNameEntryPairs (m : HashMap Name Entry) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, e) => mixHash (hash n) (hash e)

def fingerprint : ∀ k, Val k → UInt64
  | .inputFiles, (s : HashSet FilePath) =>
    hash <| s.toList.map (·.toString) |>.mergeSort (· <= ·)
  | .moduleFile .., (p : Option FilePath) => hash (p.map (·.toString))
  | .moduleImports .., (ns : List Name) =>
    hash <| ns.map hash
  | .importedEnv .., (env : Global) => hashNameEntryPairs env
  | .elabModule .., (env : Global) => hashNameEntryPairs env

  | .fileText .., (s : String) => hash s
  | .astProgram .., (p : Frontend.Ast.Program) => hash p
  | .declOwner .., (m : HashMap Name TopDecl) => hashNameTopDeclPairs m
  | .declOrdering .., (ds : List TopDecl) => hash ds
  | .topDeclCmd .., (cmd : Frontend.Ast.Command.Cmd) => hash cmd
  | .elabTop .., (m : HashMap Name Entry) => hashNameEntryPairs m
  | .entry .., (r : Option Entry) => hash r
  | .constTy .., (r : Option (Ty 0)) => hash r
  | .constantInfo .., (r : Option ConstantInfo) => hash r
  | .constDef .., (r : Option (Tm 0)) => hash r
  | .recursorInfo .., (r : Option RecursorInfo) => hash r
  | .constructorInfo .., (r : Option ConstructorInfo) => hash r
  | .inductiveInfo .., (r : Option InductiveInfo) => hash r


private def logElab (decl : TopDecl) : TaskM Error Val PUnit :=
  IO.toEIO Error.ioError <|
    IO.eprintln s!"[elab] {repr decl.kind} {decl.name}"

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
      let config ← IO.toEIO Error.ioError rulesContextRef.get
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
      let config ← IO.toEIO Error.ioError rulesContextRef.get
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

  | .moduleImports filepath => do
      let prog ← fetchQ (.astProgram filepath)
      return extractImports prog

  | .importedEnv filepath => do
      let imports ← fetchQ (.moduleImports filepath)
      let mut globalEnv : Global := HashMap.emptyWithCapacity 4096
      for modName in imports.toArray do
        match ← fetchQ (.moduleFile modName) with
        | none =>
            throw (.msg s!"Import not found: {modName}")
        | some depFile =>
            let depEnv ← fetchQ (.elabModule depFile)
            for (name, entry) in depEnv.toList.toArray do
              globalEnv := globalEnv.insert name entry
      return globalEnv

  | .elabModule filepath => do
      let mut globalEnv ← fetchQ (.importedEnv filepath)
      let ordering : List TopDecl ← fetchQ (.declOrdering filepath)
      for decl in ordering do
        let localEnv ← fetchQ (.elabTop filepath decl)
        for (n, e) in localEnv.toList.toArray do
          globalEnv := globalEnv.insert n e
      return globalEnv

  | .fileText filepath => do
      match ← IO.toEIO Error.ioError (getFileTextOverride? filepath) with
      | some text => return text
      | none => IO.toEIO Error.ioError <| IO.FS.readFile filepath
  | .astProgram filepath => do
      let content ← fetchQ (.fileText filepath)
      match Frontend.Parser.parse content with
      | .error err =>
          throw (.msg s!"Parse error: {err.msg} at position {err.pos.byteIdx}")
      | .ok cstProg =>
          return Frontend.Cst.Program.desugar cstProg
  | .declOwner filepath => do
      let a : Frontend.Ast.Program ← fetchQ (.astProgram filepath)
      buildOwnerIndex a
  | .declOrdering filepath => do
      let a : Frontend.Ast.Program ← fetchQ (.astProgram filepath)
      return buildDeclOrdering a
  | .topDeclCmd filepath decl => do
      let prog : Frontend.Ast.Program ← fetchQ (.astProgram filepath)
      for h : idx in [:prog.length] do
        let cmd := prog[idx]
        match cmd with
        | .definition d => if decl.kind = .definition && decl.name = d.name then return cmd
        | .axiom a => if decl.kind = .axiom && decl.name = a.name then return cmd
        | .inductive i => if decl.kind = .inductive && decl.name = i.name then return cmd
        | .structure s => if decl.kind = .structure && decl.name = s.name then return cmd
        | .example _ => if decl.kind = .example && decl.name = (`_example).num idx then return cmd
        | .import _ => continue
      throw (.msg s!"Top-level declaration not found: {repr decl}")
  | .elabTop filepath decl => do
      logElab decl
      let cmd ← fetchQ (.topDeclCmd filepath decl)
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
      let coreCtx : CoreContext := { file := some filepath, selfNames }
      -- Build importedEnv from imports and prior declarations
      let mut importedEnv : Global ← fetchQ (.importedEnv filepath)
      let ordering : List TopDecl ← fetchQ (.declOrdering filepath)
      for priorDecl in ordering do
        if priorDecl == decl then break
        let priorEnv ← fetchQ (.elabTop filepath priorDecl)
        for (n, e) in priorEnv.toList.toArray do
          importedEnv := importedEnv.insert n e
      let init : CoreState :=
        {
          modules := HashMap.emptyWithCapacity 8
          importedEnv
          localEnv := HashMap.emptyWithCapacity 128
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
  | .entry filepath name => do
      let owners : HashMap Name TopDecl ← fetchQ (.declOwner filepath)
      match owners[name]? with
      | none => return none
      | some owner =>
          let env : HashMap Name Entry ← fetchQ (.elabTop filepath owner)
          return env[name]?
  | .constTy filepath name =>
      return match ← fetchQ (.entry filepath name) with
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
  | .constantInfo filepath name => do
      let e? : Option Entry ← fetchQ (.entry filepath name)
      return e?.map fun
        | .definition info
        | .opaque info
        | .axiom info
        | .recursor info
        | .constructor info
        | .inductive info =>
            info.toConstantInfo
  | .constDef filepath name => do
      return match ← fetchQ (.entry filepath name) with
      | some (.definition info) => some info.tm
      | _ => none
  | .recursorInfo filepath name =>
      return match ← fetchQ (.entry filepath name) with
      | some (.recursor info) => some info
      | _ => none
  | .constructorInfo filepath name =>
      return match ← fetchQ (.entry filepath name) with
      | some (.constructor info) => some info
      | _ => none
  | .inductiveInfo filepath name =>
      return match ← fetchQ (.entry filepath name) with
      | some (.inductive info) => some info
      | _ => none

def newEngine : Engine Error Val where
  recover k := throw (.ioError (IO.userError s!"Cycle detected: {repr k}"))
  fingerprint
  isInput k :=
    match k with
    | .fileText _ => true
    | .inputFiles => true
    | _ => false

protected def run
    {α : Type}
    (config : Config)
    (engine : Engine Error Val)
    (task : TaskM Error Val α) :
    IO (Except Error (α × Engine Error Val)) := do
  rulesContextRef.set config
  (runWithEngine engine rules task).toIO'

end Qdt.Incremental
