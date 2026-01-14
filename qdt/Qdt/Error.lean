import Qdt.Frontend.Source
import Qdt.Pretty

namespace Qdt

open Lean (Name)
open Frontend (Src)

inductive Error
  | msg (msg : String)
  | ioError (error : IO.Error)
  | notImplemented (msg : String := "")
  | expectedType (src : Src) {c} (names : List Name) (got : Ty c)
  | typecheckMissing (src : Src)
  | duplicateUniverseParam (src : Src) (name : Name)
  | higherUniverse (src : Src)
  | inferUnannotatedLambda (src : Src)
  | inferSorry (src : Src)
  | expectedFunctionType (src : Src) {c} (names : List Name) (got : Ty c)
  | typeMismatch (src : Src) {c} (names : List Name) (expected : Ty c) (got : Ty c)
  | unboundVariable (src : Src) (name : Name)
  | unboundUniverseVariable (src : Src) (name : Name)
  | typeFamilyCtorReturnTypeRequired (src : Src) (ctorName : Name)
  | structureResultTypeMustBeTypeUniverse (src : Src) (structName : Name)
  | universeArgCountMismatch (src : Src) (name : Name) (expected : Nat) (got : Nat)
  | nonPositiveOccurrence (indName : Name)
  | ctorMustReturnInductive (ctorName : Name) (indName : Name)
  | ctorParamMismatch (ctorName : Name)
deriving Inhabited

instance : ToString Error where toString
  | .msg msg => msg
  | .ioError error => s!"IO error: {error}"
  | .notImplemented msg => s!"Not implemented: {msg}"
  | .expectedType src names got => s!"{repr src}: Expected type, got {got.fmt names Prec.min}"
  | .typecheckMissing src => s!"{repr src}: Syntax error"
  | .duplicateUniverseParam src name => s!"{repr src}: Duplicate universe parameter {name}"
  | .higherUniverse src => s!"{repr src}: No higher universes than Type"
  | .inferUnannotatedLambda src => s!"{repr src}: Cannot infer type of unannotated lambda"
  | .inferSorry src => s!"{repr src}: Cannot infer type of sorry"
  | .expectedFunctionType src names got => s!"{repr src}: Expected function type, got {got.fmt names Prec.min}"
  | .typeMismatch src names expected got => s!"{repr src}: Type mismatch: expected\n{expected.fmt names Prec.min},\ngot\n{got.fmt names Prec.min}"
  | .unboundVariable src name => s!"{repr src}: Unbound variable {name}"
  | .unboundUniverseVariable src name => s!"{repr src}: Unbound universe variable {name}"
  | .typeFamilyCtorReturnTypeRequired src ctorName => s!"{repr src}: {ctorName}: constructor must specify return type for inductive type family"
  | .structureResultTypeMustBeTypeUniverse src structName => s!"{repr src}: {structName}: structure result type must be of the form Type u"
  | .universeArgCountMismatch src name expected got => s!"{repr src}: {name}: expected {expected} universe arguments, got {got}"
  | .nonPositiveOccurrence indName => s!"{indName} has a non-positive occurrence"
  | .ctorMustReturnInductive ctorName indName => s!"{ctorName} must return {indName}"
  | .ctorParamMismatch ctorName => s!"{ctorName}: inductive type parameters must be constant throughout the definition"

end Qdt
