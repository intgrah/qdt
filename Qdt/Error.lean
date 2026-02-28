import Mathlib.Algebra.Group.Defs
import Qdt.Frontend.Ast
import Qdt.Pretty

namespace Qdt

open Lean (Name)
open Frontend (Path)

inductive Error
  | msg (msg : String)
  | ioError (error : IO.Error)
  | notImplemented (msg : String)
  | expectedType {c} (names : List Name) (got : Ty c)
  | syntaxError
  | duplicateUniverseParam (name : Name)
  | higherUniverse
  | inferUnannotatedLambda
  | inferSorry
  | expectedFunctionType {c} (names : List Name) (got : Ty c)
  | typeMismatch {c} (names : List Name) (expected : Ty c) (got : Ty c)
  | unboundVariable (name : Name)
  | unboundUniverseVariable (name : Name)
  | typeFamilyCtorReturnTypeRequired (ctorName : Name)
  | structureResultTypeMustBeTypeUniverse (structName : Name)
  | universeArgCountMismatch (name : Name) (expected : Nat) (got : Nat)
  | nonPositiveOccurrence (indName : Name)
  | ctorMustReturnInductive (ctorName : Name) (indName : Name)
  | ctorParamMismatch (ctorName : Name)
deriving Inhabited

instance : ToString Error where toString
  | .msg msg => msg
  | .ioError error => s!"IO error: {error}"
  | .notImplemented msg => s!"Not implemented: {msg}"
  | .expectedType names got => s!"Expected type, got {got.fmt names Prec.min}"
  | .syntaxError => "Syntax error"
  | .duplicateUniverseParam name => s!"Duplicate universe parameter {name}"
  | .higherUniverse => "No higher universes than Type"
  | .inferUnannotatedLambda => "Cannot infer type of unannotated lambda"
  | .inferSorry => "Cannot infer type of sorry"
  | .expectedFunctionType names got => s!"Expected function type, got {got.fmt names Prec.min}"
  | .typeMismatch names expected got => s!"Type mismatch: expected\n{expected.fmt names Prec.min},\ngot\n{got.fmt names Prec.min}"
  | .unboundVariable name => s!"Unbound variable {name}"
  | .unboundUniverseVariable name => s!"Unbound universe variable {name}"
  | .typeFamilyCtorReturnTypeRequired ctorName => s!"{ctorName}: constructor must specify return type for inductive type family"
  | .structureResultTypeMustBeTypeUniverse structName => s!"{structName}: structure result type must be of the form Type u"
  | .universeArgCountMismatch name expected got => s!"{name}: expected {expected} universe arguments, got {got}"
  | .nonPositiveOccurrence indName => s!"{indName} has a non-positive occurrence"
  | .ctorMustReturnInductive ctorName indName => s!"{ctorName} must return {indName}"
  | .ctorParamMismatch ctorName => s!"{ctorName}: inductive type parameters must be constant throughout the definition"

structure Diagnostic where
  path : Path
  error : Error
deriving Inhabited

structure TypeInfo where
  path : Path
  ty : String

instance : Inhabited TypeInfo := ⟨{ path := [], ty := "" }⟩

instance {α} : Monoid (Array α) where
  one := #[]
  mul := Array.append
  one_mul _ := Array.empty_append
  mul_one a := Array.append_empty
  mul_assoc a b c := Array.append_assoc

structure ElabInfo where
  diagnostics : Array Diagnostic
  types : Array TypeInfo
deriving Inhabited

instance : Hashable ElabInfo where
  hash info := mixHash (hash info.diagnostics.size) (hash info.types.size)

instance : One ElabInfo where
  one := { diagnostics := #[], types := #[] }

@[simp] theorem ElabInfo.one_diagnostics : (1 : ElabInfo).diagnostics = #[] := rfl
@[simp] theorem ElabInfo.one_types : (1 : ElabInfo).types = #[] := rfl

instance : Mul ElabInfo where
  mul a b := { diagnostics := a.diagnostics ++ b.diagnostics, types := a.types ++ b.types }

instance : Monoid ElabInfo where
  one_mul x := by cases x; simp [HMul.hMul, Mul.mul]
  mul_one x := by cases x; simp [HMul.hMul, Mul.mul]
  mul_assoc _ _ _ := by simp only [HMul.hMul, Mul.mul]; congr 1 <;> exact Array.append_assoc ..

end Qdt
