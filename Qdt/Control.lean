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

variable (q₀ : config.Q)

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
  MTask config q₀
  |> StateT ElabState
  |> ReaderT ElabContext

abbrev TermM (n : Nat) := ReaderT (TermContext n) (ElabM q₀)
abbrev SemM (n c : Nat) := ReaderT (Env n c) (ElabM q₀)

instance {n} : MonadLiftT (SemM q₀ n n) (TermM q₀ n) where
  monadLift m n := m n.env

@[inline] def currentDecl : ElabM q₀ Name := do
  return (← read).currentDecl

@[inline] def currentPath : ElabM q₀ Path := do
  return (← read).path

@[inline] def withChild {α : Type} (i : Nat) : ElabM q₀ α → ElabM q₀ α :=
  ReaderT.adapt fun ctx => { ctx with path := i :: ctx.path }

@[inline] def getUnivParams : ElabM q₀ (List Name) := do
  return (← read).univParams

@[inline] def emitDiagnostic (err : Error) : ElabM q₀ Unit := do
  let path ← currentPath q₀
  modify fun st => { st with diagnostics := st.diagnostics.push { path, error := err } }

def raiseError {α : Type} (err : Error) : OptionT (ElabM q₀) α := do
  emitDiagnostic q₀ err
  failure

@[inline] def emitHover (hover : HoverContent) : ElabM q₀ Unit := do
  if !(← readThe ElabContext).collectHovers then return
  let path ← currentPath q₀
  modify fun st => { st with hovers := st.hovers.push { path, hover } }

def getLocalEnv : ElabM q₀ Global := do
  return (← get).localEnv

def fetchConstant (name : Name) : ElabM q₀ (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  let ctx ← readThe ElabContext
  if let some result := st.entryCache[name]? then
    return result
  let currentDeclName := (← read).currentDecl
  let inScope ←
    MTask.fetch (ℭ := config) (q₀ := q₀)
      (Key.declScope ctx.filepath name currentDeclName) sorry
  if !inScope then
    modify fun st => { st with entryCache := st.entryCache.insert name none }
    return none
  let result : Val (Key.constant ctx.filepath name) ←
    MTask.fetch (ℭ := config) (q₀ := q₀) (Key.constant ctx.filepath name) sorry
  modify fun st => { st with entryCache := st.entryCache.insert name result }
  return result

def fetchConstantInfo (name : Name) : ElabM q₀ (Option ConstantInfo) := do
  let some e ← fetchConstant q₀ name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.toConstantInfo)

def fetchDefinition (name : Name) : ElabM q₀ (Option (Tm 0)) := do
  let some (.definition info) ← fetchConstant q₀ name | return none
  return some info.tm

def fetchInductive (name : Name) : ElabM q₀ (Option InductiveInfo) := do
  let some (.inductive info) ← fetchConstant q₀ name | return none
  return some info

def fetchRecursor (name : Name) : ElabM q₀ (Option RecursorInfo) := do
  let some (.recursor info) ← fetchConstant q₀ name | return none
  return some info

def fetchConstructor (name : Name) : ElabM q₀ (Option ConstructorInfo) := do
  let some (.constructor info) ← fetchConstant q₀ name | return none
  return some info

def addConstant (name : Name) (constant : Constant) : ElabM q₀ Bool := do
  let st ← get
  if name ∈ st.localEnv then
    emitDiagnostic q₀ (.alreadyDefined name)
    return false
  let ctx ← readThe ElabContext
  let currentDeclName := (← read).currentDecl
  unless name == currentDeclName do
    let (declIndex, _) ← (MTask.fetch (q₀ := q₀) (Key.declarationIndex ctx.filepath) sorry : MTask config q₀ _)
    match declIndex[name]? with
    | some nameIdx =>
        match declIndex[currentDeclName]? with
        | some currentIdx =>
            if nameIdx != currentIdx then
              emitDiagnostic q₀ (.alreadyDefined name)
              return false
        | none => pure ()
    | none =>
        let existing : Val (Key.constant ctx.filepath name) ←
          (MTask.fetch (q₀ := q₀) (Key.constant ctx.filepath name) sorry : MTask config q₀ _)
        if existing.isSome then
          emitDiagnostic q₀ (.alreadyDefined name)
          return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : ElabM q₀ Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def ElabM.run {α : Type} (ctx : ElabContext) (action : ElabM q₀ α) :
    MTask config q₀ (α × Global × ElabInfo) := do
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
