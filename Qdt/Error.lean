module

public import Mathlib.Algebra.Group.Defs
public import Qdt.Frontend.Ast
public import Qdt.Pretty

@[expose] public section

namespace Qdt

open Lean (Name)
open Frontend (Path)

inductive Error
  | msg (msg : String)
  | notImplemented (msg : String)
  | importCycle (modules : List Name)
  | expectedType {c} (names : List Name) (got : Ty c)
  | syntaxError
  | duplicateUniverseParam (name : Name)
  | inferUnannotatedLambda
  | inferSorry
  | expectedFunctionType {c} (names : List Name) (got : Ty c)
  | typeMismatch {c} (names : List Name) (expected : Ty c) (got : Ty c)
  | unboundVariable (name : Name)
  | unboundUniverseVariable (name : Name)
  | alreadyDefined (name : Name)
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
deriving Inhabited, Hashable

instance : ToString Error where toString
  | .msg msg =>
    msg
  | .notImplemented msg =>
    s!"Not implemented: {msg}"
  | .importCycle modules =>
    s!"Import cycle: {modules}"
  | .expectedType names got =>
    s!"Expected type, got {got.fmt names Prec.min}"
  | .syntaxError =>
    "Syntax error"
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
    s!"{ctorName}: field '{fieldName}' has type in universe {fieldUniv}, but inductive lives in {indUniv}"
  | .ctorNameNotAtomic ctorName =>
    s!"{ctorName}: constructor name must be atomic"
  | .fieldNameNotAtomic structName =>
    s!"{structName}: field name must be atomic"

@[pp_using_anonymous_constructor]
structure Diagnostic where
  path : Path
  error : Error
deriving Inhabited, Hashable

inductive HoverContent where
  | signature (name : Name) {n : Nat} (params : Ctx 0 n) (retTy : Ty n)
  | localVar (name : Name) (ctxNames : List Name) {n : Nat} (ty : Ty n)
  | typeOnly (ctxNames : List Name) {n : Nat} (ty : Ty n)
deriving Hashable

structure HoverInfo where
  path : Path
  hover : HoverContent
deriving Hashable

def HoverContent.format : HoverContent → String
  | .signature name params retTy =>
      let rec collectParams : {a b : Nat} → List Name → Ctx a b → List String × List Name
        | _, _, names, .nil => ([], names)
        | _, _, names, .snoc bs ⟨pname, pty⟩ =>
            let (prev, prevNames) := collectParams names bs
            let x := freshName prevNames pname
            let tyStr := toString (pty.fmt prevNames Prec.min)
            (prev ++ [s!"({x} : {tyStr})"], x :: prevNames)
      let rec peelPis : {m : Nat} → List Name → Ty m → List String × String
        | _, names, .pi ⟨pname, dom⟩ cod =>
            if pname.isAnonymous then
              ([], toString ((Ty.pi ⟨pname, dom⟩ cod).fmt names Prec.min))
            else
              let x := freshName names pname
              let domStr := toString (dom.fmt names Prec.min)
              let (rest, retStr) := peelPis (x :: names) cod
              (s!"({x} : {domStr})" :: rest, retStr)
        | _, names, ty => ([], toString (ty.fmt names Prec.min))
      let (ctxParts, ctxNames) := collectParams [] params
      let (piParts, retStr) := peelPis ctxNames retTy
      let allParts := ctxParts ++ piParts
      let paramsStr := " ".intercalate allParts
      if paramsStr.isEmpty then s!"{name} : {retStr}"
      else s!"{name} {paramsStr} : {retStr}"
  | .localVar name ctxNames ty =>
      s!"{name} : {toString (ty.fmt ctxNames Prec.min)}"
  | .typeOnly ctxNames ty =>
      toString (ty.fmt ctxNames Prec.min)

instance {α} : Monoid (Array α) where
  one := #[]
  mul := Array.append
  one_mul _ := Array.empty_append
  mul_one _ := Array.append_empty
  mul_assoc _ _ _ := Array.append_assoc

@[pp_using_anonymous_constructor]
structure ElabInfo where
  diagnostics : Array Diagnostic
  hovers : Array HoverInfo

instance : Hashable ElabInfo where
  hash info := mixHash (hash info.diagnostics.size) (hash info.hovers.size)

instance : Monoid ElabInfo where
  one := ⟨#[], #[]⟩
  mul | ⟨d₁, h₁⟩, ⟨d₂, h₂⟩ => ⟨d₁ ++ d₂, h₁ ++ h₂⟩
  one_mul := by simp [HMul.hMul]
  mul_one := by simp [HMul.hMul]
  mul_assoc := by simp [HMul.hMul]

end Qdt
