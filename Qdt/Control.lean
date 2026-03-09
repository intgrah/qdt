module

public import Mathlib.Control.Monad.Writer

public import Qdt.TermContext
public import Qdt.Incremental.Query
public import Incremental.Basic

@[expose] public section

namespace Qdt

open Lean (Name)
open Incremental
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

structure ElabContext where
  filepath : FilePath
  univParams : List Name
  selfNames : List Name := []
  collectHovers : Bool
  currentDecl : Name
  path : Path := []
deriving Repr, Inhabited

structure ElabState where
  localEnv : Global
  sorryId : Nat
  entryCache : Std.HashMap Name (Option Constant)
deriving Inhabited

abbrev ElabM :=
  Task Monad Key Val
  |> WriterT ElabInfo
  |> StateT ElabState
  |> ReaderT ElabContext

abbrev TermM (n : Nat) := ReaderT (TermContext n) ElabM
abbrev SemM (n c : Nat) := ReaderT (Env n c) ElabM

instance {n} : MonadLiftT (SemM n n) (TermM n) where
  monadLift m n := m n.env

def currentDecl : ElabM Name := do
  return (← read).currentDecl

def currentPath : ElabM Path := do
  return (← read).path

def withChild {α : Type} (i : Nat) : ElabM α → ElabM α :=
  ReaderT.adapt fun ctx => { ctx with path := i :: ctx.path }

def getUnivParams : ElabM (List Name) := do
  return (← readThe ElabContext).univParams

def emitDiagnostic (err : Error) : ElabM Unit := do
  let path ← currentPath
  tell { diagnostics := #[{ path, error := err }], hovers := #[] }

def raiseError {α : Type} (err : Error) : OptionT ElabM α := do
  emitDiagnostic err
  failure

def emitHover (hover : HoverContent) : ElabM Unit := do
  if !(← readThe ElabContext).collectHovers then return
  let path ← currentPath
  tell { diagnostics := #[], hovers := #[{ path, hover }] }

def getLocalEnv : ElabM Global := do
  return (← get).localEnv

def fetchConstant (name : Name) : ElabM (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  let ctx ← readThe ElabContext
  if name ∈ ctx.selfNames then
    return none
  if let some result := st.entryCache[name]? then
    return result
  let (declIndex, _) ← (fetch (Key.declarationIndex ctx.filepath) : Task Monad Key Val _)
  let currentDeclName := (← read).currentDecl
  if let some idx := declIndex[name]? then
    if let some currentIdx := declIndex[currentDeclName]? then
      if idx ≥ currentIdx then
        modify fun st => { st with entryCache := st.entryCache.insert name none }
        return none
  let result : Val (Key.constant ctx.filepath name) ←
    (fetch (Key.constant ctx.filepath name) : Task Monad Key Val _)
  let result : Option Constant := result.map Prod.fst
  modify fun st => { st with entryCache := st.entryCache.insert name result }
  return result

def fetchConstantInfo (name : Name) : ElabM (Option ConstantInfo) := do
  let some e ← fetchConstant name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.toConstantInfo)

def fetchDefinition (name : Name) : ElabM (Option (Tm 0)) := do
  let some (.definition info) ← fetchConstant name | return none
  return some info.tm

def fetchInductive (name : Name) : ElabM (Option InductiveInfo) := do
  let some (.inductive info) ← fetchConstant name | return none
  return some info

def fetchRecursor (name : Name) : ElabM (Option RecursorInfo) := do
  let some (.recursor info) ← fetchConstant name | return none
  return some info

def fetchConstructor (name : Name) : ElabM (Option ConstructorInfo) := do
  let some (.constructor info) ← fetchConstant name | return none
  return some info

def addConstant (name : Name) (constant : Constant) : ElabM Bool := do
  let st ← get
  if name ∈ st.localEnv then
    emitDiagnostic (.alreadyDefined name)
    return false
  let ctx ← readThe ElabContext
  let currentDeclName := (← read).currentDecl
  let (declIndex, _) ← (fetch (Key.declarationIndex ctx.filepath) : Task Monad Key Val _)
  match declIndex[name]? with
  | some nameIdx =>
      match declIndex[currentDeclName]? with
      | some currentIdx =>
          if nameIdx != currentIdx then
            emitDiagnostic (.alreadyDefined name)
            return false
      | none => pure ()
  | none =>
      let existing : Val (Key.constant ctx.filepath name) ←
        (fetch (Key.constant ctx.filepath name) : Task Monad Key Val _)
      if existing.isSome then
        emitDiagnostic (.alreadyDefined name)
        return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : ElabM Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def ElabM.run {α : Type} (ctx : ElabContext) (action : ElabM α) :
    Task Monad Key Val (α × Global × ElabInfo) := do
  let state : ElabState := {
    localEnv := ∅
    sorryId := 0
    entryCache := ∅
  }
  let ((result, st), info) ← WriterT.run (StateT.run (action ctx) state)
  return (result, st.localEnv, info)

end Qdt
