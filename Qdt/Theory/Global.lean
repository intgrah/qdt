module

public import Qdt.Theory.Syntax
public import Std.Data.HashMap.Basic

@[expose] public section

instance {α n} [Hashable α] : Hashable (Vector α n) where
  hash as := hash as.toList

namespace Qdt

open Lean (Name)

structure ConstantInfo where
  numUnivParams : Nat
  ty : Ty 0
deriving Repr, Hashable

structure DefinitionInfo extends ConstantInfo where
  tm : Tm 0
deriving Repr, Hashable

structure OpaqueInfo extends ConstantInfo where
deriving Repr, Hashable

structure AxiomInfo extends ConstantInfo where
  synthetic : Bool := false
deriving Repr, Hashable

structure ConstructorInfo extends ConstantInfo where
  indName : Name
deriving Repr, Hashable

structure InductiveInfo extends ConstantInfo where
  numParams : Nat
  numIndices : Nat
  numCtors : Nat
  ctorNames : Vector Name numCtors
  pathCtorNames : Array Name := #[]
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
  numPointCtors : Nat
  recRules :
    Vector (RecursorRule (numParams + numMotives + numMinors)) numPointCtors
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

def Constant.freeUMVars : Constant → List UMVarId
  | .definition info => info.ty.freeUMVars ++ info.tm.freeUMVars
  | .opaque info | .axiom info | .constructor info | .inductive info =>
      info.ty.freeUMVars
  | .recursor info =>
      info.ty.freeUMVars ++
      info.recRules.toList.flatMap (fun r => r.rhs.freeUMVars)

def Constant.substUMVars (f : UMVarId → Option Universe) : Constant → Constant
  | .definition info =>
      .definition { info with ty := info.ty.substUMVars f, tm := info.tm.substUMVars f }
  | .opaque info => .opaque { info with ty := info.ty.substUMVars f }
  | .axiom info => .axiom { info with ty := info.ty.substUMVars f }
  | .constructor info => .constructor { info with ty := info.ty.substUMVars f }
  | .inductive info => .inductive { info with ty := info.ty.substUMVars f }
  | .recursor info =>
      .recursor { info with
        ty := info.ty.substUMVars f
        recRules := info.recRules.map (fun r => { r with rhs := r.rhs.substUMVars f }) }

def Constant.setNumUnivParams (n : Nat) : Constant → Constant
  | .definition info => .definition { info with numUnivParams := n }
  | .opaque info => .opaque { info with numUnivParams := n }
  | .axiom info => .axiom { info with numUnivParams := n }
  | .constructor info => .constructor { info with numUnivParams := n }
  | .inductive info => .inductive { info with numUnivParams := n }
  | .recursor info => .recursor { info with numUnivParams := n }

def Constant.extendConstUnivs (extras : List Universe) (name : Name) :
    Constant → Constant
  | .definition info =>
      .definition { info with
        ty := info.ty.extendConstUnivs extras name
        tm := info.tm.extendConstUnivs extras name }
  | .opaque info => .opaque { info with ty := info.ty.extendConstUnivs extras name }
  | .axiom info => .axiom { info with ty := info.ty.extendConstUnivs extras name }
  | .constructor info => .constructor { info with ty := info.ty.extendConstUnivs extras name }
  | .inductive info => .inductive { info with ty := info.ty.extendConstUnivs extras name }
  | .recursor info =>
      .recursor { info with
        ty := info.ty.extendConstUnivs extras name
        recRules := info.recRules.map (fun r =>
          { r with rhs := r.rhs.extendConstUnivs extras name }) }

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

def findConstantInfo (name : Name) (g : Global) : Option ConstantInfo :=
  Constant.toConstantInfo <$> g[name]?

theorem findTy_eq_findConstantInfo {name : Name} {g : Global} :
    g.findTy name = (g.findConstantInfo name).map ConstantInfo.ty := by
  unfold findTy findConstantInfo
  cases g[name]? with
  | none => rfl
  | some c => simp [Constant.ty, Constant.toConstantInfo]; cases c <;> rfl

def findInductive (name : Name) (g : Global) : Option InductiveInfo := do
  let .inductive info ← g[name]? | none
  return info

def findConstructor (name : Name) (g : Global) : Option ConstructorInfo := do
  let .constructor info ← g[name]? | none
  return info

def findRecursor (name : Name) (g : Global) : Option RecursorInfo := do
  let .recursor info ← g[name]? | none
  return info

def AxiomFree (Δ : Global) : Prop :=
  ∀ (name : Name) (entry : Constant), Δ[name]? = some entry →
    match entry with | .axiom _ => False | _ => True

theorem AxiomFree.findTy_safe {Δ : Global} (hAx : Global.AxiomFree Δ)
    {name : Name} {ty : Ty 0} (hLook : Δ.findTy name = some ty) :
    ∃ entry : Constant,
      Δ[name]? = some entry ∧ entry.ty = ty ∧
        match entry with | .axiom _ => False | _ => True := by
  -- `findTy` is `Constant.ty <$> g[name]?`; unfolding the functor
  -- application exposes the underlying entry via
  -- `Option.map_eq_some_iff`.
  unfold findTy at hLook
  rw [show ((Constant.ty <$> Δ[name]?) = Option.map Constant.ty Δ[name]?)
        from rfl] at hLook
  rw [Option.map_eq_some_iff] at hLook
  obtain ⟨entry, hGet, hEq⟩ := hLook
  exact ⟨entry, hGet, hEq, hAx name entry hGet⟩

end Global
end Qdt
