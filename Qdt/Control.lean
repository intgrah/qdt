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
  mayPostpone : Bool := true
deriving Repr, Inhabited

structure MetaInfo where
  arity : Nat
  ctx : Ctx 0 arity
  ty : Ty arity
  ctxNames : List Name
  solution : Option (Tm arity) := none
  groundSolution : Bool := false
  tyNorm : Option (Ty arity) := none
  path : Path
  decl : Name
  errored : Bool := false

instance : Inhabited MetaInfo where
  default :=
    { arity := 0, ctx := .nil, ty := .u .zero, ctxNames := [],
      solution := none, path := default, decl := default }

structure PostponeEntry where
  {n : Nat}
  ctx : TermContext n
  expected : VTy n
  ast : Frontend.Ast
  placeholder : Tm n
  path : Path
  univParams : List Name

structure ElabState where
  localEnv : Global
  pending : Global := ∅
  sorryId : Nat
  inaccessibleId : Nat := 0
  entryCache : Std.HashMap Name (Option Constant)
  diagnostics : Array Diagnostic := #[]
  hovers : Array HoverInfo := #[]
  metas : Array MetaInfo := #[]
  deltaCache : Std.HashMap (Name × List Universe) (VTm 0) := ∅
  usubst : Universe.Subst := .empty
  nextUMVar : UMVarId := 0
  postponedUEqs : Array (Universe × Universe) := #[]
  postponeSignal : Bool := false
  postponed : Array PostponeEntry := #[]
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

partial def mintFreshUnivNames (used : Std.HashSet Name) (count : Nat) : List Name :=
  go count 1 used #[]
where
  go (need i : Nat) (used : Std.HashSet Name) (acc : Array Name) : List Name :=
    if need = 0 then acc.toList
    else
      let nm := (`u).appendIndexAfter i
      if used.contains nm then go need (i + 1) used acc
      else go (need - 1) (i + 1) (used.insert nm) (acc.push nm)

def promoteUniverseMVars (userParams : List Name) (mvarIds : List UMVarId) :
    List Name × (UMVarId → Option Universe) :=
  let dedup := mvarIds.eraseDups
  let used : Std.HashSet Name := userParams.foldl (init := ∅) (·.insert ·)
  let names := mintFreshUnivNames used dedup.length
  let table : Std.HashMap UMVarId Universe :=
    (dedup.zip names).foldl (init := ∅) fun acc (id, nm) =>
      acc.insert id (.param nm)
  (names, fun id => table[id]?)

def checkUnusedUniverseParams (declName : Name) (univParams : List Name)
    (used : List Name) : OptionT (ElabM q₀) Unit := do
  for name in univParams do
    if !used.contains name then
      raiseError q₀ (.unusedUniverseParam declName name)

@[inline] def getMetaInfo (id : MVarId) : ElabM q₀ MetaInfo := do
  return (← get).metas[id]!

@[inline] def assignMeta (info : MetaInfo) (id : MVarId) (soln : Tm info.arity) :
    ElabM q₀ Unit :=
  modify fun st => { st with metas := st.metas.set! id { info with solution := some soln } }

@[inline] def compressMetaSolution (info : MetaInfo) (id : MVarId) (soln : Tm info.arity)
    (ground : Bool) : ElabM q₀ Unit :=
  modify fun st =>
    { st with metas := st.metas.set! id { info with solution := some soln, groundSolution := ground } }

@[inline] def setMetaTyNorm (info : MetaInfo) (id : MVarId) (t : Ty info.arity) : ElabM q₀ Unit :=
  modify fun st => { st with metas := st.metas.set! id { info with tyNorm := some t } }

@[inline] def markMetaErrored (id : MVarId) : ElabM q₀ Unit :=
  modify fun st =>
    let info := st.metas[id]!
    { st with metas := st.metas.set! id { info with errored := true } }

@[inline] def metaIsErrored (id : MVarId) : ElabM q₀ Bool := do
  return (← get).metas[id]!.errored

@[inline] def freshMetaId (info : MetaInfo) : ElabM q₀ MVarId := do
  let st ← get
  let id := st.metas.size
  set { st with metas := st.metas.push info }
  return id

@[inline] def resetMetas : ElabM q₀ Unit :=
  modify fun st => { st with metas := #[], postponed := #[], postponeSignal := false }

@[inline] def emitHover (hover : HoverContent) : ElabM q₀ Unit := do
  let ctx ← readThe ElabContext
  if !ctx.collectHovers then return
  modify fun st =>
    { st with hovers := st.hovers.push { path := ctx.path, univParams := ctx.univParams, hover } }

def fetchConstant (name : Name) : ElabM q₀ (Option Constant) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  if let some e := st.pending[name]? then
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

def addPending (name : Name) (constant : Constant) : ElabM q₀ Unit :=
  modify fun st => { st with pending := st.pending.insert name constant }

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
