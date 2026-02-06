import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Frontend.Source
import Qdt.Error
import Qdt.MLTT.Global
import Qdt.TermContext
import Qdt.Incremental.Basic
import Qdt.Incremental.Query

namespace Qdt

open Lean (Name)
open Incremental (BaseM Key Val TaskM)

open Std (HashMap HashSet)

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
  imports : HashSet System.FilePath

def CoreContext.empty : CoreContext where
  file := none
  selfNames := []
  imports := ∅

structure CoreState where
  modules : HashMap Name ModuleStatus
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

section Monads

-- abbrev BaseM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
--   StateRefT (RunState ε R) (EIO ε)

-- abbrev Task
--     (c : (Type u → Type u) → Type (u + 1))
--     (Q : Type u)
--     (R : Q → Type u)
--     (f : Type u → Type u) [c f] :=
--   ReaderT (∀ q : Q, f (R q)) f

-- abbrev TaskT := Task Monad

-- abbrev TaskM (ε : Type) {Q : Type} (R : Q → Type) [BEq Q] [Hashable Q] : Type → Type :=
--   TaskT Q R (BaseM ε R)

/-- QueryM provides the ability to make queries queries. -/
abbrev QueryM : Type → Type :=
  TaskM Error Val

/-- CoreM provides context at the global scope. -/
abbrev CoreM : Type → Type :=
  ReaderT CoreContext (StateT CoreState QueryM)

/-- MetaM provides context at the definition scope. -/
abbrev MetaM : Type → Type :=
  ReaderT MetaContext (StateT MetaState CoreM)

/-- TermM provides context for type checking. -/
abbrev TermM (n : Nat) : Type → Type :=
  ReaderT (TermContext n) MetaM

/-- SemM provides the environment for NbE. -/
abbrev SemM (n c : Nat) : Type → Type :=
  ReaderT (Env n c) MetaM

protected instance {n} : MonadLiftT (SemM n n) (TermM n) where
  monadLift := (· ·.env)

end Monads

def getLocalEnv : CoreM Global := do
  let genv ← getThe CoreState
  return genv.localEnv

/-!
These are intentionally fine-grained to make it possible to
incrementalise without treating the whole global environment as a dependency.
-/

def fetchEntry (name : Name) : CoreM (Option Entry) := do
  let st ← getThe CoreState
  if let some e := st.localEnv[name]? then
    return some e
  if let some e := st.importedEnv[name]? then
    if let some file := e.file then
      let _ ← fetchQ (.entry ⟨file⟩ name)
    return some e
  let ctx ← read
  if ctx.selfNames.contains name then
    return none
  match ctx.file with
  | none => return none
  | some file =>
      if let some e ← fetchQ (.entry file name) then
        modify fun st => { st with importedEnv := st.importedEnv.insert name e }
        return some e
      for importFile in ctx.imports do
        if let some e ← fetchQ (.entry importFile name) then
          modify fun st => { st with importedEnv := st.importedEnv.insert name e }
          return some e
      return none

def fetchTy (name : Name) : CoreM (Option (Ty 0)) := do
  let some e ← fetchEntry name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.ty)

def fetchConstantInfo (name : Name) : CoreM (Option ConstantInfo) := do
  let some e ← fetchEntry name | return none
  return some (match e with
    | .definition info | .opaque info | .axiom info
    | .recursor info | .constructor info | .inductive info => info.toConstantInfo)

def fetchDefinition (name : Name) : CoreM (Option (Tm 0)) := do
  let some (.definition info) ← fetchEntry name | return none
  return some info.tm

def fetchInductive (name : Name) : CoreM (Option InductiveInfo) := do
  let some (.inductive info) ← fetchEntry name | return none
  return some info

def fetchRecursor (name : Name) : CoreM (Option RecursorInfo) := do
  let some (.recursor info) ← fetchEntry name | return none
  return some info

def fetchConstructor (name : Name) : CoreM (Option ConstructorInfo) := do
  let some (.constructor info) ← fetchEntry name | return none
  return some info

def Global.addEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  if st.localEnv.contains name then
    throw (.msg s!"{name} is already defined")
  let ctx ← read
  let file := ctx.file.map toString
  let entry := entry.setFile file
  set { st with localEnv := st.localEnv.insert name entry }

def Global.replaceEntry (name : Name) (entry : Entry) : CoreM Unit := do
  let st ← getThe CoreState
  let ctx ← read
  let file := ctx.file.map toString
  let entry := entry.setFile file
  set { st with localEnv := st.localEnv.insert name entry }

end Qdt
