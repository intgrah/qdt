module

public import Qdt.TermContext
public import Qdt.Incremental.Query

@[expose] public section

namespace Qdt

open Lean (Name)
open Incremental
open Frontend (Path SourceMap)
open System (FilePath)

open Std (HashMap HashSet)

variable (ι₀ : ∀ i, config.V i) (q₀ : config.Q)

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
  betaCount : Nat := 0
  evalCount : Nat := 0
  whnfCount : Nat := 0
deriving Inhabited

abbrev ElabM :=
  Task Monad config ι₀ q₀
  |> StateT ElabState
  |> ReaderT ElabContext

abbrev TermM (n : Nat) := ReaderT (TermContext n) (ElabM ι₀ q₀)
abbrev SemM (n c : Nat) := ReaderT (Env n c) (ElabM ι₀ q₀)

instance {n} : MonadLiftT (SemM ι₀ q₀ n n) (TermM ι₀ q₀ n) where
  monadLift m n := m n.env

@[inline] def currentDecl : ElabM ι₀ q₀ Name := do
  return (← read).currentDecl

@[inline] def currentPath : ElabM ι₀ q₀ Path := do
  return (← read).path

@[inline] def withChild {α : Type} (i : Nat) : ElabM ι₀ q₀ α → ElabM ι₀ q₀ α :=
  ReaderT.adapt fun ctx => { ctx with path := i :: ctx.path }

@[inline] def getUnivParams : ElabM ι₀ q₀ (List Name) := do
  return (← read).univParams

@[inline] def emitDiagnostic (err : Error) : ElabM ι₀ q₀ Unit := do
  let path ← currentPath ι₀ q₀
  modify fun st => { st with diagnostics := st.diagnostics.push { path, error := err } }

def raiseError {α : Type} (err : Error) : OptionT (ElabM ι₀ q₀) α := do
  emitDiagnostic ι₀ q₀ err
  failure

@[inline] def emitHover (hover : HoverContent) : ElabM ι₀ q₀ Unit := do
  if !(← readThe ElabContext).collectHovers then return
  let path ← currentPath ι₀ q₀
  modify fun st => { st with hovers := st.hovers.push { path, hover } }

def getLocalEnv : ElabM ι₀ q₀ Global := do
  return (← get).localEnv

def fetchConstant (name : Name) : ElabM ι₀ q₀ (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  let ctx ← readThe ElabContext
  if let some result := st.entryCache[name]? then
    return result
  let (declIndex, _) ← (Task.fetch (c := Monad) (ℭ := config) (ι₀ := ι₀) (q₀ := q₀) (Key.declarationIndex ctx.filepath) sorry : Task Monad config ι₀ q₀ _)
  let currentDeclName := (← read).currentDecl
  if let some idx := declIndex[name]? then
    if let some currentIdx := declIndex[currentDeclName]? then
      if idx ≥ currentIdx then
        modify fun st => { st with entryCache := st.entryCache.insert name none }
        return none
  let result : Val (Key.constant ctx.filepath name) ←
    (Task.fetch (c := Monad) (ℭ := config) (ι₀ := ι₀) (q₀ := q₀) (Key.constant ctx.filepath name) sorry : Task Monad config ι₀ q₀ _)
  let result : Option Constant := result.map Prod.fst
  modify fun st => { st with entryCache := st.entryCache.insert name result }
  return result

def fetchConstantInfo (name : Name) : ElabM ι₀ q₀ (Option ConstantInfo) := do
  let some e ← fetchConstant ι₀ q₀ name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.toConstantInfo)

def fetchDefinition (name : Name) : ElabM ι₀ q₀ (Option (Tm 0)) := do
  let some (.definition info) ← fetchConstant ι₀ q₀ name | return none
  return some info.tm

def fetchInductive (name : Name) : ElabM ι₀ q₀ (Option InductiveInfo) := do
  let some (.inductive info) ← fetchConstant ι₀ q₀ name | return none
  return some info

def fetchRecursor (name : Name) : ElabM ι₀ q₀ (Option RecursorInfo) := do
  let some (.recursor info) ← fetchConstant ι₀ q₀ name | return none
  return some info

def fetchConstructor (name : Name) : ElabM ι₀ q₀ (Option ConstructorInfo) := do
  let some (.constructor info) ← fetchConstant ι₀ q₀ name | return none
  return some info

def addConstant (name : Name) (constant : Constant) : ElabM ι₀ q₀ Bool := do
  let st ← get
  if name ∈ st.localEnv then
    emitDiagnostic ι₀ q₀ (.alreadyDefined name)
    return false
  let ctx ← readThe ElabContext
  let currentDeclName := (← read).currentDecl
  let (declIndex, _) ← (fetch (q₀ := q₀) (Key.declarationIndex ctx.filepath) sorry : Task Monad config ι₀ q₀ _)
  match declIndex[name]? with
  | some nameIdx =>
      match declIndex[currentDeclName]? with
      | some currentIdx =>
          if nameIdx != currentIdx then
            emitDiagnostic ι₀ q₀ (.alreadyDefined name)
            return false
      | none => pure ()
  | none =>
      let existing : Val (Key.constant ctx.filepath name) ←
        (fetch (q₀ := q₀) (Key.constant ctx.filepath name) sorry : Task Monad config ι₀ q₀ _)
      if existing.isSome then
        emitDiagnostic ι₀ q₀ (.alreadyDefined name)
        return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : ElabM ι₀ q₀ Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def ElabM.run {α : Type} (ctx : ElabContext) (action : ElabM ι₀ q₀ α) :
    Task Monad config ι₀ q₀ (α × Global × ElabInfo) := do
  let state : ElabState := {
    localEnv := ∅
    sorryId := 0
    entryCache := ∅
  }
  let (result, st) ← StateT.run (action ctx) state
  return (result, st.localEnv,
    { diagnostics := st.diagnostics, hovers := st.hovers
    , betaCount := st.betaCount, evalCount := st.evalCount, whnfCount := st.whnfCount })

end Qdt
