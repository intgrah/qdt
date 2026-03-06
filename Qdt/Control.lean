module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import Mathlib.Control.Monad.Writer

public import Qdt.Frontend.Cst
public import Qdt.Error
public import Qdt.MLTT.Global
public import Qdt.TermContext
public import Qdt.Incremental.Basic
public import Qdt.Incremental.Query

@[expose] public section

namespace Qdt

open Lean (Name)
open Incremental (Key Val Task)
open Frontend (Path SourceMap)
open System (FilePath)

open Std (HashMap HashSet)

instance {ω M} [Monad M] [Monoid ω] [MonadWriter ω M] : MonadWriter ω (OptionT M) where
  tell w := OptionT.lift (tell w)
  listen m := do
    let (result, w) ← OptionT.lift (listen m)
    match result with
    | some a => return (a, w)
    | none => failure
  pass m := do
    let (a, f) ← m
    OptionT.lift (tell (f 1))
    return a

instance {ρ ω M} [Monad M] [MonadWriter ω M] : MonadWriter ω (ReaderT ρ M) where
  tell w := fun _ => tell w
  listen m := fun r => listen (m r)
  pass m := fun r => pass (m r)

structure CoreContext where
  filepath : FilePath
  univParams : List Name
  selfNames : List Name := []
  collectHovers : Bool

structure MetaContext where
  currentDecl : Name
  path : Path := []
deriving Repr, Inhabited

structure MetaState where
  localEnv : Global
  sorryId : Nat := 0
  entryCache : Std.HashMap Lean.Name (Option Constant) := {}
deriving Inhabited

abbrev CoreM := ReaderT CoreContext (WriterT ElabInfo (Task Key Val))
abbrev MetaM := ReaderT MetaContext (StateT MetaState CoreM)
abbrev TermM (n : Nat) := ReaderT (TermContext n) MetaM
abbrev SemM (n c : Nat) := ReaderT (Env n c) MetaM

instance {n} : MonadLiftT (SemM n n) (TermM n) where
  monadLift m n := m n.env

def currentDecl : MetaM Name := do
  return (← read).currentDecl

def currentPath : MetaM Path := do
  return (← read).path

def withChild {α : Type} (i : Nat) : MetaM α → MetaM α :=
  ReaderT.adapt (fun ctx => { ctx with path := i :: ctx.path })

def getUnivParams : MetaM (List Name) := do
  return (← readThe CoreContext).univParams

def emitDiagnostic (err : Error) : MetaM Unit := do
  let path ← currentPath
  tell { diagnostics := #[{ path, error := err }], hovers := #[] }

def raiseError {α : Type} (err : Error) : OptionT MetaM α := do
  emitDiagnostic err
  failure

def emitHover (hover : HoverContent) : MetaM Unit := do
  if !(← readThe CoreContext).collectHovers then return
  let path ← currentPath
  tell { diagnostics := #[], hovers := #[{ path, hover }] }

def getLocalEnv : MetaM Global := do
  return (← get).localEnv

def fetchConstant (name : Name) : MetaM (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  let ctx ← readThe CoreContext
  if name ∈ ctx.selfNames then
    return none
  if let some result := st.entryCache[name]? then
    return result
  let declIndex : Std.HashMap Lean.Name Nat ←
    liftM (Task.fetch (Key.declarationIndex ctx.filepath) : Task Key Val _)
  let currentDeclName := (← read).currentDecl
  if let some idx := declIndex[name]? then
    if let some currentIdx := declIndex[currentDeclName]? then
      if idx >= currentIdx then
        modify fun st => { st with entryCache := st.entryCache.insert name none }
        return none
  let result : Val (Key.constant ctx.filepath name) ←
    liftM (Task.fetch (Key.constant ctx.filepath name) : Task Key Val _)
  let result : Option Constant := result.map Prod.fst
  modify fun st => { st with entryCache := st.entryCache.insert name result }
  return result

def fetchTy (name : Name) : MetaM (Option (Ty 0)) := do
  let some e ← fetchConstant name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.ty)

def fetchConstantInfo (name : Name) : MetaM (Option ConstantInfo) := do
  let some e ← fetchConstant name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.toConstantInfo)

def fetchDefinition (name : Name) : MetaM (Option (Tm 0)) := do
  let some (.definition info) ← fetchConstant name | return none
  return some info.tm

def fetchInductive (name : Name) : MetaM (Option InductiveInfo) := do
  let some (.inductive info) ← fetchConstant name | return none
  return some info

def fetchRecursor (name : Name) : MetaM (Option RecursorInfo) := do
  let some (.recursor info) ← fetchConstant name | return none
  return some info

def fetchConstructor (name : Name) : MetaM (Option ConstructorInfo) := do
  let some (.constructor info) ← fetchConstant name | return none
  return some info

def addConstant (name : Name) (constant : Constant) : MetaM Bool := do
  let st ← get
  if name ∈ st.localEnv then
    emitDiagnostic (.msg s!"{name} is already defined")
    return false
  let ctx ← readThe CoreContext
  let currentDeclName := (← read).currentDecl
  let declIndex : Std.HashMap Lean.Name Nat ←
    liftM (Task.fetch (Key.declarationIndex ctx.filepath) : Task Key Val _)
  match declIndex[name]? with
  | some nameIdx =>
      match declIndex[currentDeclName]? with
      | some currentIdx =>
          if nameIdx != currentIdx then
            emitDiagnostic (.msg s!"{name} is already defined")
            return false
      | none => pure ()
  | none =>
      let existing : Val (Key.constant ctx.filepath name) ←
        liftM (Task.fetch (Key.constant ctx.filepath name) : Task Key Val _)
      if existing.isSome then
        emitDiagnostic (.msg s!"{name} is already defined")
        return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : MetaM Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def elabRun {α : Type} (coreCtx : CoreContext) (metaCtx : MetaContext) (action : OptionT MetaM α) :
    Task Key Val (Option α × Global × ElabInfo) := do
  let ((optResult, metaSt), info) ← WriterT.run ((StateT.run (action metaCtx) { localEnv := {} }) coreCtx)
  return (optResult, metaSt.localEnv, info)

end Qdt
