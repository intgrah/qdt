import Std.Data.HashMap

import Qdt.MLTT.Syntax

instance {α n} [Hashable α] : Hashable (Vector α n) where
  hash as := as.foldl (fun r a => mixHash r (hash a)) 7

namespace Qdt

open Lean (Name)

structure ConstantInfo where
  file : Option String := none
  univParams : List Name
  ty : Ty 0
deriving Repr, Hashable

structure DefinitionInfo extends ConstantInfo where
  tm : Tm 0
deriving Repr, Hashable

structure OpaqueInfo extends ConstantInfo where
deriving Repr, Hashable

structure AxiomInfo extends ConstantInfo where
deriving Repr, Hashable

structure ConstructorInfo extends ConstantInfo where
  indName : Name
deriving Repr, Hashable

structure InductiveInfo extends ConstantInfo where
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

structure RecursorInfo extends ConstantInfo where
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

def Entry.setFile (file : Option String) : Entry → Entry
  | .definition info => .definition { info with file }
  | .opaque info => .opaque { info with file }
  | .axiom info => .axiom { info with file }
  | .inductive info => .inductive { info with file }
  | .recursor info => .recursor { info with file }
  | .constructor info => .constructor { info with file }

def Entry.file : Entry → Option String
  | .definition info
  | .opaque info
  | .axiom info
  | .inductive info
  | .recursor info
  | .constructor info => info.file

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

def findConstantInfo (name : Name) (g : Global) : Option ConstantInfo := do
  match ← g[name]? with
  | .definition info
  | .opaque info
  | .axiom info
  | .recursor info
  | .constructor info
  | .inductive info =>
      return info.toConstantInfo

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
