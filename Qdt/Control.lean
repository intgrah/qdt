module

public import Qdt.TermContext
public import Qdt.Theory.Universe.Subst
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

structure MetaInfo where
  arity : Nat
  numScopeArgs : Nat := 0
  ctxNames : List Name
  ty : Ty 0
  solution : Option (Tm 0) := none
  path : Path
  decl : Name
  errored : Bool := false
deriving Inhabited

structure ElabState where
  localEnv : Global
  sorryId : Nat
  entryCache : Std.HashMap Name (Option Constant)
  diagnostics : Array Diagnostic := #[]
  hovers : Array HoverInfo := #[]
  metas : Array MetaInfo := #[]
  usubst : Universe.Subst := .empty
  nextUMVar : UMVarId := 0
  postponedUEqs : Array (Universe × Universe) := #[]
deriving Inhabited

abbrev ElabM :=
  Task config q₀
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
  let ctx ← read
  modify fun st =>
    { st with diagnostics := st.diagnostics.push { path := ctx.path, univParams := ctx.univParams, error := err } }

@[inline] def emitDiagnosticAt (path : Path) (err : Error) : ElabM q₀ Unit := do
  let ctx ← read
  modify fun st =>
    { st with diagnostics := st.diagnostics.push { path, univParams := ctx.univParams, error := err } }

def raiseError {α : Type} (err : Error) : OptionT (ElabM q₀) α := do
  emitDiagnostic q₀ err
  failure

def promoteUniverseMVars (userCount : Nat) (mvarIds : List UMVarId) :
    List Name × (UMVarId → Option Universe) :=
  let dedup := mvarIds.eraseDups
  let names := dedup.zipIdx.map fun (_, i) => (`_uvar).num i
  let table : Std.HashMap UMVarId Universe :=
    dedup.zipIdx.foldl (init := ∅) fun acc (id, i) =>
      acc.insert id (.level (userCount + i))
  (names, fun id => table[id]?)

def checkUnusedUniverseParams (declName : Name) (univParams : List Name)
    (used : List Nat) : OptionT (ElabM q₀) Unit := do
  for (name, i) in univParams.zipIdx do
    if !used.contains i then
      raiseError q₀ (.unusedUniverseParam declName name)

@[inline] def getMetaInfo (id : MVarId) : ElabM q₀ (Option MetaInfo) := do
  return (← get).metas[id]?

@[inline] def metaSolution (id : MVarId) : ElabM q₀ (Option (Tm 0)) := do
  match (← get).metas[id]? with
  | some info => return info.solution
  | none => return none

@[inline] def assignMeta (id : MVarId) (soln : Tm 0) : ElabM q₀ Unit :=
  modify fun st =>
    match st.metas[id]? with
    | some info => { st with metas := st.metas.set! id { info with solution := some soln } }
    | none => st

@[inline] def markMetaErrored (id : MVarId) : ElabM q₀ Unit :=
  modify fun st =>
    match st.metas[id]? with
    | some info => { st with metas := st.metas.set! id { info with errored := true } }
    | none => st

@[inline] def metaIsErrored (id : MVarId) : ElabM q₀ Bool := do
  match (← get).metas[id]? with
  | some info => return info.errored
  | none => return false

@[inline] def freshMetaId (info : MetaInfo) : ElabM q₀ MVarId := do
  let st ← get
  let id := st.metas.size
  set { st with metas := st.metas.push info }
  return id

@[inline] def resetMetas : ElabM q₀ Unit :=
  modify fun st => { st with metas := #[] }

@[inline] def emitHover (hover : HoverContent) : ElabM q₀ Unit := do
  let ctx ← readThe ElabContext
  if !ctx.collectHovers then return
  modify fun st =>
    { st with hovers := st.hovers.push { path := ctx.path, univParams := ctx.univParams, hover } }

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
    Task.fetch (ℭ := config) (q₀ := q₀)
      (Key.declScope ctx.filepath name currentDeclName) sorry
  if !inScope then
    modify fun st => { st with entryCache := st.entryCache.insert name none }
    return none
  let result : Val (Key.constant ctx.filepath name) ←
    Task.fetch (ℭ := config) (q₀ := q₀) (Key.constant ctx.filepath name) sorry
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
    let (declIndex, _) ← Task.fetch (q₀ := q₀) (Key.declarationIndex ctx.filepath) sorry
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
          Task.fetch (q₀ := q₀) (Key.constant ctx.filepath name) sorry
        if existing.isSome then
          emitDiagnostic q₀ (.alreadyDefined name)
          return false
  set { st with localEnv := st.localEnv.insert name constant }
  return true

def replaceEntry (name : Name) (constant : Constant) : ElabM q₀ Unit := do
  let st ← get
  set { st with localEnv := st.localEnv.insert name constant }

def ElabM.run {α : Type} (ctx : ElabContext) (action : ElabM q₀ α) :
    Task config q₀ (α × Global × ElabInfo) := do
  let state : ElabState := {
    localEnv := ∅
    sorryId := 0
    entryCache := ∅
    metas := #[]
  }
  let (result, st) ← StateT.run (action ctx) state
  return (result, st.localEnv,
    { diagnostics := st.diagnostics, hovers := st.hovers })

end Qdt
