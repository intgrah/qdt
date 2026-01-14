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

/--
Topological sort of modules using DFS
Temporary-permanent mark algorithm
-/
inductive ModuleStatus : Type
  | importing
  | imported
deriving Repr, Inhabited

structure CoreContext where
  file : Option System.FilePath
  selfNames : List Name

def CoreContext.empty : CoreContext where
  file := none
  selfNames := []

structure CoreState where
  modules : Std.HashMap Name ModuleStatus
  /-- Entries from imported modules. -/
  importedEnv : Global
  /-- Entries produced while elaborating the current top-level declaration -/
  localEnv : Global
  errors : Array Error
deriving Inhabited

structure MetaContext where
  currentDecl : Name
deriving Repr, Inhabited

def MetaContext.empty : MetaContext where
  currentDecl := .anonymous

structure MetaState where
  sorryId : Nat := 0
  univParams : List Name
deriving Repr, Inhabited

/--
CoreM provides context at the global scope.
It provides the ability to throw exceptions,
make queries, and extend the local environment for the current decl.
-/
abbrev QueryM := TaskM Error Val

abbrev CoreM := ReaderT CoreContext (StateT CoreState QueryM)

/--
MetaM provides context at the definition scope.
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
These are intentionally fine-grained to make it possible to
incrementalise without treating the whole global environment as a dependency.
-/

def fetchEntry (name : Name) : CoreM (Option Entry) := do
  let st ← get
  if let some e := st.localEnv[name]? then
    return some e
  if let some e := st.importedEnv[name]? then
    return some e
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.entry file name) : QueryM _)

def fetchTy (name : Name) : CoreM (Option (Ty 0)) := do
  let st ← get
  if let some ty := st.localEnv.findTy name then
    return some ty
  if let some ty := st.importedEnv.findTy name then
    return some ty
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.constTy file name) : QueryM _)

def fetchConstantInfo (name : Name) : CoreM (Option ConstantInfo) := do
  let st ← get
  if let some result := st.localEnv.findConstantInfo name then
    return some result
  if let some result := st.importedEnv.findConstantInfo name then
    return some result
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.constantInfo file name) : QueryM _)

def fetchDefinition (name : Name) : CoreM (Option (Tm 0)) := do
  let st ← get
  if let some info := st.localEnv.findDefinition name then
    return some info.tm
  if let some info := st.importedEnv.findDefinition name then
    return some info.tm
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.constDef file name) : QueryM _)

def fetchInductive (name : Name) : CoreM (Option InductiveInfo) := do
  let st ← get
  if let some info := st.localEnv.findInductive name then
    return some info
  if let some info := st.importedEnv.findInductive name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.inductiveInfo file name) : QueryM _)

def fetchRecursor (name : Name) : CoreM (Option RecursorInfo) := do
  let st ← get
  if let some info := st.localEnv.findRecursor name then
    return some info
  if let some info := st.importedEnv.findRecursor name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.recursorInfo file name) : QueryM _)

def fetchConstructor (name : Name) : CoreM (Option ConstructorInfo) := do
  let st ← get
  if let some info := st.localEnv.findConstructor name then
    return some info
  if let some info := st.importedEnv.findConstructor name then
    return some info
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file => (TaskM.fetch (Key.constructorInfo file name) : QueryM _)

def Global.addEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  if st.localEnv.contains name then
    throw (.msg s!"{name} is already defined")
  set { st with localEnv := st.localEnv.insert name entry }

def Global.replaceEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  set { st with localEnv := st.localEnv.insert name entry }

end Qdt
