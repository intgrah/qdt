module

public import Mathlib.Algebra.Group.Defs
public import Qdt.Frontend.Parser.Core
public import Qdt.Pretty
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Qdt

open Lean (Name)
open Frontend (Path)

inductive Error
  | msg (msg : String)
  | notImplemented (msg : String)
  | importCycle (modules : List Name)
  | expectedType {c} (names : List Name) (got : Ty c)
  | syntaxError (err : Frontend.Parser.ParseError)
  | duplicateUniverseParam (name : Name)
  | inferUnannotatedLambda
  | inferSorry
  | expectedFunctionType {c} (names : List Name) (got : Ty c)
  | typeMismatch {c} (names : List Name) (expected : Ty c) (got : Ty c)
  | unboundVariable (name : Name)
  | unboundUniverseVariable (name : Name)
  | alreadyDefined (name : Name)
  | duplicateImport (name : Name)
  | unresolvedImport (name : Name)
  | typeFamilyCtorReturnTypeRequired (ctorName : Name)
  | inductiveReturnTypeMustBeTypeUniverse (indName : Name)
  | structureResultTypeMustBeTypeUniverse (structName : Name)
  | universeArgCountMismatch (name : Name) (expected : Nat) (got : Nat)
  | nonPositiveOccurrence (indName : Name)
  | ctorMustReturnInductive (ctorName : Name) (indName : Name)
  | ctorParamMismatch (ctorName : Name)
  | fieldUniverseTooLarge (ctorName : Name) (fieldName : Name) (fieldUniv : Universe) (indUniv : Universe)
  | ctorNameNotAtomic (ctorName : Name)
  | fieldNameNotAtomic (structName : Name)
  | unsolvedMetavariable (decl : Name) (id : Nat) (ty : Ty 0)
  | inferHole
  | unusedUniverseParam (declName : Name) (paramName : Name)
  | unsolvedUniverseMetavariable (declName : Name)
  | stuckUniverseConstraint (lhs : Universe) (rhs : Universe)
deriving Inhabited, Hashable

def Error.format (e : Error) : String :=
  match e with
  | .msg s =>
    s
  | .notImplemented s =>
    s!"Not implemented: {s}"
  | .importCycle modules =>
    s!"Import cycle: {modules}"
  | .expectedType names got =>
    s!"Expected type, got {got.fmt names Prec.min}"
  | .syntaxError err =>
    s!"Syntax error: {err.msg}"
  | .duplicateUniverseParam name =>
    s!"Duplicate universe parameter {name}"
  | .inferUnannotatedLambda =>
    "Cannot infer type of unannotated lambda"
  | .inferSorry =>
    "Cannot infer type of sorry"
  | .expectedFunctionType names got =>
    s!"Expected function type, got {got.fmt names Prec.min}"
  | .typeMismatch names expected got =>
    s!"Type mismatch: expected\n{expected.fmt names Prec.min},\ngot\n{got.fmt names Prec.min}"
  | .unboundVariable name =>
    s!"Unbound variable {name}"
  | .unboundUniverseVariable name =>
    s!"Unbound universe variable {name}"
  | .alreadyDefined name =>
    s!"{name} is already defined"
  | .duplicateImport name =>
    s!"ambiguous declaration '{name}': defined in multiple imported modules"
  | .unresolvedImport name =>
    s!"unknown module prefix '{name}'"
  | .typeFamilyCtorReturnTypeRequired ctorName =>
    s!"{ctorName}: constructor must specify return type for inductive type family"
  | .inductiveReturnTypeMustBeTypeUniverse indName =>
    s!"{indName}: inductive return type must be a Type universe"
  | .structureResultTypeMustBeTypeUniverse structName =>
    s!"{structName}: structure result type must be a Type universe"
  | .universeArgCountMismatch name expected got =>
    s!"{name}: expected {expected} universe arguments, got {got}"
  | .nonPositiveOccurrence indName =>
    s!"{indName} has a non-positive occurrence"
  | .ctorMustReturnInductive ctorName indName =>
    s!"{ctorName} must return {indName}"
  | .ctorParamMismatch ctorName =>
    s!"{ctorName}: inductive type parameters must be constant throughout the definition"
  | .fieldUniverseTooLarge ctorName fieldName fieldUniv indUniv =>
    s!"{ctorName}: field '{fieldName}' has type in universe {(Universe.fmt fieldUniv 0).pretty}, but inductive lives in {(Universe.fmt indUniv 0).pretty}"
  | .ctorNameNotAtomic ctorName =>
    s!"{ctorName}: constructor name must be atomic"
  | .fieldNameNotAtomic structName =>
    s!"{structName}: field name must be atomic"
  | .unsolvedMetavariable decl id ty =>
    s!"unsolved metavariable ?m{id} : {ty.fmt [] Prec.min} in {decl}"
  | .inferHole =>
    "cannot infer the value of a hole here; provide a type annotation"
  | .unusedUniverseParam declName paramName =>
    s!"{declName}: unused universe parameter '{paramName}'"
  | .unsolvedUniverseMetavariable declName =>
    s!"{declName}: unsolved universe metavariable"
  | .stuckUniverseConstraint lhs rhs =>
    s!"stuck at solving universe constraint\n  {lhs.fmt Prec.min} =?= {rhs.fmt Prec.min}"

instance : ToString Error where toString := Error.format

@[pp_using_anonymous_constructor]
structure Diagnostic where
  path : Path
  error : Error
  univParams : List Name := []
deriving Inhabited, Hashable

inductive HoverContent
  | signature (name : Name) {n : Nat} (params : Ctx 0 n) (retTy : Ty n)
  | localVar (name : Name) (ctxNames : List Name) {n : Nat} (ty : Ty n)
  | typeOnly (ctxNames : List Name) {n : Nat} (ty : Ty n)
  | hole (metaId : MVarId) (ctxNames : List Name) {n : Nat} (ty : Ty n)
deriving Hashable

structure HoverInfo where
  path : Path
  hover : HoverContent
  univParams : List Name := []
deriving Hashable

def HoverContent.format (univs : List Name) : HoverContent → String
  | .signature name params retTy =>
      let binderDelims : BinderInfo → String × String
        | .explicit => ("(", ")")
        | .implicit => ("{", "}")
      let rec collectParams {a b : Nat} (names : List Name) : Ctx a b → List String × List Name
        | .nil => ([], names)
        | .snoc bs ⟨pname, bi, pty⟩ =>
            let (prev, prevNames) := collectParams names bs
            let x := freshName prevNames pname
            let (l, r) := binderDelims bi
            (prev ++ [s!"{l}{x} : {pty.fmt prevNames Prec.min}{r}"], x :: prevNames)
      let rec peelPis {m : Nat} (names : List Name) : Ty m → List String × String
        | .pi pname bi dom cod =>
            if pname.isAnonymous ∧ bi matches .explicit then
              ([], toString ((Ty.pi pname bi dom cod).fmt names Prec.min))
            else
              let x := freshName names pname
              let (rest, retStr) := peelPis (x :: names) cod
              let (l, r) := binderDelims bi
              (s!"{l}{x} : {dom.fmt names Prec.min}{r}" :: rest, retStr)
        | ty => ([], toString (ty.fmt names Prec.min))
      let (ctxParts, ctxNames) := collectParams [] params
      let (piParts, retStr) := peelPis ctxNames retTy
      let allParts := ctxParts ++ piParts
      let paramsStr := " ".intercalate allParts
      let baseName := if name.isAnonymous then "_" else toString name
      let univSuffix :=
        if univs.isEmpty then ""
        else ".{" ++ ", ".intercalate (univs.map toString) ++ "}"
      let nameStr := baseName ++ univSuffix
      if paramsStr.isEmpty then s!"{nameStr} : {retStr}"
      else s!"{nameStr} {paramsStr} : {retStr}"
  | .localVar name ctxNames ty =>
      let nameStr :=
        if name.isAnonymous then "_"
        else if isInaccessible name then toString (displayName ctxNames name)
        else toString name
      s!"{nameStr} : {ty.fmt ctxNames Prec.min}"
  | .typeOnly ctxNames ty =>
      s!"{ty.fmt ctxNames Prec.min}"
  | .hole _ ctxNames ty =>
      s!"{ty.fmt ctxNames Prec.min}"

instance {α} : Monoid (Array α) where
  one := #[]
  mul := Array.append
  one_mul _ := Array.empty_append
  mul_one _ := Array.append_empty
  mul_assoc _ _ _ := Array.append_assoc

structure ElabInfo where
  diagnostics : Array Diagnostic
  hovers : Array HoverInfo
deriving Hashable, Inhabited

instance : Monoid ElabInfo where
  one := ⟨#[], #[]⟩
  mul | ⟨d₁, h₁⟩, ⟨d₂, h₂⟩ => ⟨d₁ ++ d₂, h₁ ++ h₂⟩
  one_mul := by simp [HMul.hMul]
  mul_one := by simp [HMul.hMul]
  mul_assoc := by intros; simp [HMul.hMul, Array.append_assoc]

end Qdt
