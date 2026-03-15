module

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

structure ElabContext where
  filepath : FilePath
  univParams : List Name
  collectHovers : Bool
  currentDecl : Name
  path : Path := []
deriving Repr, Inhabited

structure ElabState where
  localEnv : Global
  sorryId : Nat
  entryCache : Std.HashMap Name (Option Constant)
  diagnostics : Array Diagnostic := #[]
  hovers : Array HoverInfo := #[]
deriving Inhabited

abbrev ElabM :=
  Task Monad InputKey InputV Key Val
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
  return (← read).univParams

def emitDiagnostic (err : Error) : ElabM Unit := do
  let path ← currentPath
  modify fun st => { st with diagnostics := st.diagnostics.push { path, error := err } }

def raiseError {α : Type} (err : Error) : OptionT ElabM α := do
  emitDiagnostic err
  failure

def emitHover (hover : HoverContent) : ElabM Unit := do
  if !(← readThe ElabContext).collectHovers then return
  let path ← currentPath
  modify fun st => { st with hovers := st.hovers.push { path, hover } }

def getLocalEnv : ElabM Global := do
  return (← get).localEnv

def fetchConstant (name : Name) : ElabM (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  let ctx ← readThe ElabContext
  if let some result := st.entryCache[name]? then
    return result
  let (declIndex, _) ← (fetch (Key.declarationIndex ctx.filepath) : Task Monad InputKey InputV Key Val _)
  let currentDeclName := (← read).currentDecl
  if let some idx := declIndex[name]? then
    if let some currentIdx := declIndex[currentDeclName]? then
      if idx ≥ currentIdx then
        modify fun st => { st with entryCache := st.entryCache.insert name none }
        return none
  let result : Val (Key.constant ctx.filepath name) ←
    (fetch (Key.constant ctx.filepath name) : Task Monad InputKey InputV Key Val _)
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
  let (declIndex, _) ← (fetch (Key.declarationIndex ctx.filepath) : Task Monad InputKey InputV Key Val _)
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
        (fetch (Key.constant ctx.filepath name) : Task Monad InputKey InputV Key Val _)
      if existing.isSome then
        emitDiagnostic (.alreadyDefined name)
        return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : ElabM Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def ElabM.run {α : Type} (ctx : ElabContext) (action : ElabM α) :
    Task Monad InputKey InputV Key Val (α × Global × ElabInfo) := do
  let state : ElabState := {
    localEnv := ∅
    sorryId := 0
    entryCache := ∅
  }
  let (result, st) ← StateT.run (action ctx) state
  return (result, st.localEnv, { diagnostics := st.diagnostics, hovers := st.hovers })

end Qdt
