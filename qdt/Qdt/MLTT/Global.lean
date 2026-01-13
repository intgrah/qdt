import Std.Data.HashMap

import Qdt.MLTT.Syntax

instance {α n} [Hashable α] : Hashable (Vector α n) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

namespace Qdt

open Lean (Name)

structure DefinitionInfo where
  ty : Ty 0
  tm : Tm 0
deriving Repr, Hashable

structure OpaqueInfo where
  ty : Ty 0
deriving Repr, Hashable

structure AxiomInfo where
  ty : Ty 0
deriving Repr, Hashable

structure ConstructorInfo where
  ty : Ty 0
  indName : Name
deriving Repr, Hashable

structure InductiveInfo where
  ty : Ty 0
  numParams : Nat
  numIndices : Nat
  numMinors : Nat
  ctorNames : Vector Name numMinors
deriving Repr, Hashable

structure RecursorRule (numParamsMotivesMinors : Nat) where
  ctorName : Name
  numFields : Nat
  rhs : Tm (numParamsMotivesMinors + numFields)
deriving Repr, Hashable

structure RecursorInfo where
  ty : Ty 0
  recName : Name
  numParams : Nat
  numMotives : Nat
  numMinors : Nat
  numIndices : Nat
  recRules : Vector (RecursorRule (numParams + numMotives + numMinors)) numMinors
deriving Repr, Hashable

inductive Entry : Type
  | definition (info : DefinitionInfo)
  | opaque (info : OpaqueInfo)
  | axiom (info : AxiomInfo)
  | inductive (info : InductiveInfo)
  | recursor (info : RecursorInfo)
  | constructor (info : ConstructorInfo)
deriving Repr, Hashable

abbrev Global := Std.HashMap Name Entry

namespace Global

def findDefinition (name : Name) (g : Global) : Option DefinitionInfo := do
  let .definition info ← g[name]? | none
  return info

def findRecursor (name : Name) (g : Global) : Option RecursorInfo := do
  let .recursor info ← g[name]? | none
  return info

def findConstructor (name : Name) (g : Global) : Option ConstructorInfo := do
  let .constructor info ← g[name]? | none
  return info

def findInductive (name : Name) (g : Global) : Option InductiveInfo := do
  let .inductive info ← g[name]? | none
  return info

def findTy (name : Name) (g : Global) : Option (Ty 0) := do
  match ← g[name]? with
  | .definition info
  | .opaque info
  | .axiom info
  | .recursor info
  | .constructor info
  | .inductive info =>
      return info.ty

end Global
end Qdt
