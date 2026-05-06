module

public import Qdt.Semantics
public import Std.Data.HashMap.Basic

@[expose] public section

instance {α n} [Hashable α] : Hashable (Vector α n) where
  hash as := hash as.toList

namespace Qdt

open Lean (Name)

structure ConstantInfo where
  univParams : List Name
  ty : Ty 0
deriving Repr, Hashable

structure DefinitionInfo extends ConstantInfo where
  tm : Tm 0
  vtm : VTm 0
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

inductive Constant : Type
  | definition (info : DefinitionInfo)
  | opaque (info : OpaqueInfo)
  | axiom (info : AxiomInfo)
  | inductive (info : InductiveInfo)
  | recursor (info : RecursorInfo)
  | constructor (info : ConstructorInfo)
deriving Repr, Hashable

def Constant.ty : Constant → Ty 0
  | .definition info
  | .opaque info
  | .axiom info
  | .recursor info
  | .constructor info
  | .inductive info =>
      info.ty

def Constant.toConstantInfo : Constant → ConstantInfo
  | .definition info
  | .opaque info
  | .axiom info
  | .recursor info
  | .constructor info
  | .inductive info =>
      info.toConstantInfo

abbrev Global := Std.HashMap Name Constant

namespace Global

def findDefinition (name : Name) (g : Global) : Option DefinitionInfo := do
  let .definition info ← g[name]? | none
  return info

def findTy (name : Name) (g : Global) : Option (Ty 0) :=
  Constant.ty <$> g[name]?

end Global
end Qdt
