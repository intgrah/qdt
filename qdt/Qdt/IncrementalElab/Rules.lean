import Std.Data.HashMap

import Qdt.Control
import Qdt.Elab
import Qdt.Frontend.Desugar
import Qdt.Frontend.Parser
import Qdt.Incremental
import Qdt.IncrementalElab.Query

namespace Qdt.Incremental

open Lean (Name)
open Frontend

abbrev IT := TaskM Error Val
abbrev IFetch := Fetch Error Val

@[inline] private def fetchQ : ∀ k, IT (Val k) := TaskM.fetch

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
  for cmd in prog do
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
    | .example _
    | .import _ => continue
  return m

private def findTopDeclCmd (prog : Frontend.Ast.Program) (decl : TopDecl) : EIO Error Frontend.Ast.Command.Cmd := do
  for cmd in prog do
    match cmd with
    | .definition d =>
        if decl.kind = .definition && decl.name = d.name then
          return cmd
    | .axiom a =>
        if decl.kind = .axiom && decl.name = a.name then
          return cmd
    | .inductive i =>
        if decl.kind = .inductive && decl.name = i.name then
          return cmd
    | .structure s =>
        if decl.kind = .structure && decl.name = s.name then
          return cmd
    | .example _ => continue
    | .import _ => continue
  throw (.msg s!"Top-level declaration not found: {repr decl}")

private def hashNameTopDeclPairs (m : Std.HashMap Name TopDecl) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, d) => mixHash (hash n) (hash d)

private def hashNameEntryPairs (m : Std.HashMap Name Entry) : UInt64 :=
  let pairs := m.toList.mergeSort (fun a b => a.fst.toString <= b.fst.toString)
  hash <| pairs.map fun (n, e) => mixHash (hash n) (hash e)

def fingerprint : ∀ k, Val k → UInt64
  | .fileText _, (s : String) =>
      hash s
  | .astProgram _, (p : Frontend.Ast.Program) =>
      hash p
  | .declOwner _, (m : Std.HashMap Name TopDecl) =>
      hashNameTopDeclPairs m
  | .topDeclCmd _ _, (cmd : Frontend.Ast.Command.Cmd) =>
      hash cmd
  | .elabTop _ _, (m : Std.HashMap Name Entry) =>
      hashNameEntryPairs m
  | .entry _ _, (r : Option Entry)
  | .constTy _ _, (r : Option (Ty 0))
  | .constDef _ _, (r : Option (Tm 0))
  | .recursorInfo _ _, (r : Option RecursorInfo)
  | .constructorInfo _ _, (r : Option ConstructorInfo)
  | .inductiveInfo _ _, (r : Option InductiveInfo) =>
      hash r

private def logElab (decl : TopDecl) : IT PUnit :=
  IO.toEIO Error.ioError <|
    IO.println s!"[elab] {repr decl.kind} {decl.name}"

def rules : ∀ k, TaskM Error Val (Val k)
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
      let coreCtx : CoreContext := { file, selfNames }
      let init : CoreState :=
        {
          modules := Std.HashMap.emptyWithCapacity 8
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
          | .definition ⟨ty, _⟩
          | .opaque ⟨ty⟩
          | .axiom ⟨ty⟩ =>
              some ty
          | .recursor info
          | .constructor info
          | .inductive info =>
              some info.ty
      | none => none
  | .constDef file name =>
      return match ← fetchQ (.entry file name) with
      | some (.definition ⟨_, tm⟩) => some tm
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
  isInput k := k matches .fileText _

def run
    {α : Type}
    (engine : Engine Error Val) :
    TaskM Error Val α →
    EIO Error (α × Engine Error Val) :=
  runWithEngine engine rules

end Qdt.Incremental
