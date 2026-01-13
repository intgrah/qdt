import Std.Data.HashMap

import Qdt.Frontend.Source
import Qdt.Error
import Qdt.MLTT.Global
import Qdt.TermContext
import Qdt.Incremental
import Qdt.IncrementalElab.Query

namespace Qdt

open Lean (Name)
open Incremental (BaseM Fetch Key Val TaskM)

/-- Topological sort of modules using DFS -/
inductive ModuleStatus : Type
  | importing
  | imported
deriving Repr, Inhabited

structure CoreContext where
  file : System.FilePath
  /-- Names owned by the current top-level decl (for breaking self-cycles while elaborating it). -/
  selfNames : List Name

def CoreContext.empty : CoreContext where
  file := System.FilePath.mk ""
  selfNames := []

structure CoreState where
  modules : Std.HashMap Name ModuleStatus
  /-- Entries produced while elaborating the current top-level decl. -/
  localEnv : Global
  errors : Array Error
deriving Inhabited

-- Unifier stuff would go here
structure MetaContext where
  currentDecl : Name
deriving Repr, Inhabited

def MetaContext.empty : MetaContext where
  currentDecl := .anonymous

structure MetaState where
  sorryId : Nat
deriving Repr, Inhabited

def MetaState.empty : MetaState where
  sorryId := 0
/--
CoreM provides context at the global scope.
It provides the ability to throw exceptions,
make queries, and extend the local environment for the current decl.
-/
abbrev QueryM := TaskM Error Val

abbrev CoreM := ReaderT CoreContext (StateT CoreState QueryM)

/--
MetaM provides context at the definition scope.
There is nothing here yet :)
-/
abbrev MetaM := ReaderT MetaContext (StateT MetaState CoreM)

instance : Monad MetaM :=
  inferInstanceAs (Monad (ReaderT MetaContext (StateT MetaState CoreM)))

instance : MonadStateOf MetaState MetaM :=
  inferInstanceAs (MonadStateOf MetaState (ReaderT MetaContext (StateT MetaState CoreM)))

/--
TermM provides context at the syntactic term scope.
It provides the context.
-/
abbrev TermM (n : Nat) := ReaderT (TermContext n) MetaM

/--
SemM provides context at the semantic term scope.
It provides the environment
-/
abbrev SemM (n c : Nat) := ReaderT (Env n c) MetaM

protected instance {n} : MonadLiftT (SemM n n) (TermM n) where
  monadLift m := fun e => m e.env

def getLocalEnv : CoreM Global := do
  let genv ← get
  return genv.localEnv

/-!
Global lookups.

These are intentionally *fine-grained* (per-name) to make it possible to plug in
incremental memoisation later without treating the whole global environment as an
implicit dependency.
-/

def fetchEntry (name : Name) : CoreM (Option Entry) := do
  if let some e := (← get).localEnv[name]? then
    return some e
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.entry ctx.file name) : QueryM _)

def fetchTy (name : Name) : CoreM (Option (Ty 0)) := do
  if let some ty := (← get).localEnv.findTy name then
    return some ty
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.constTy ctx.file name) : QueryM _)

def fetchDefinition (name : Name) : CoreM (Option (Tm 0)) := do
  if let some info := (← get).localEnv.findDefinition name then
    return some info.tm
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.constDef ctx.file name) : QueryM _)

def fetchInductive (name : Name) : CoreM (Option InductiveInfo) := do
  if let some info := (← get).localEnv.findInductive name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.inductiveInfo ctx.file name) : QueryM _)

def fetchRecursor (name : Name) : CoreM (Option RecursorInfo) := do
  if let some info := (← get).localEnv.findRecursor name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.recursorInfo ctx.file name) : QueryM _)

def fetchConstructor (name : Name) : CoreM (Option ConstructorInfo) := do
  if let some info := (← get).localEnv.findConstructor name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  (TaskM.fetch (Key.constructorInfo ctx.file name) : QueryM _)

def Global.addEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  if st.localEnv.contains name then
    throw (.msg s!"{name} is already defined")
  set { st with localEnv := st.localEnv.insert name entry }

def Global.replaceEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  set { st with localEnv := st.localEnv.insert name entry }

end Qdt
