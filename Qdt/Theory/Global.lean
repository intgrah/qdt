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

/-- Look up a constant's `ConstantInfo` (universe parameters + type).
Used by `Tm.HasType.const` to enforce that the universe-instantiation
list provided in the term has the right arity.  Without this, the
`.const` rule allowed `(.const name us)` with arbitrary `|us|`,
making `Universe.subst` non-associative on `info.ty` and breaking
universe-substLevels-preservation of typing. -/
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

/-! ## Axiom-freeness

An `AxiomFree` global context is one whose entries are all
definitions, opaques, inductives, recursors, or constructors — no
`Constant.axiom`s.  This is a consistency-grade hypothesis: in the
presence of arbitrary axioms, the fundamental lemma cannot hold (an
axiom of type `Empty` would directly inhabit the empty type).

The fundamental lemma (`Tm.HasType.fundamental`) takes `AxiomFree`
as a hypothesis so that the `Tm.HasType.const` case can rule out the
axiom alternative when destructing the looked-up `Constant`.
-/

/-- A `Global` is *axiom-free* iff none of its entries is a
`Constant.axiom`.  The fundamental lemma is gated on this
hypothesis. -/
def AxiomFree (Δ : Global) : Prop :=
  ∀ (name : Name) (entry : Constant), Δ[name]? = some entry →
    match entry with | .axiom _ => False | _ => True

/-- From `AxiomFree Δ` and a successful `findTy`, recover the
underlying entry along with a proof that it is **not** an axiom.
This is the bridge used by the fundamental lemma's `const` case to
discharge the otherwise-unprovable axiom alternative. -/
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
