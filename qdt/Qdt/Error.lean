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
  | higherUniverse (src : Src)
  | inferUnannotatedLambda (src : Src)
  | inferSorry (src : Src)
  | expectedFunctionType (src : Src) {c} (names : List Name) (got : Ty c)
  | typeMismatch (src : Src) {c} (names : List Name) (expected : Ty c) (got : Ty c)
  | unboundVariable (src : Src) (name : Name)
  | indexedTypeCtorReturnTypeRequired (src : Src) (ctorName : Name)
  | structureResultTypeMustBeType (src : Src) (structName : Name)
deriving Inhabited

instance : ToString Error where toString
  | .msg msg => msg
  | .ioError error => s!"IO error: {error}"
  | .notImplemented msg => s!"Not implemented: {msg}"
  | .expectedType _src names got => s!"Expected type, got {got.pp .min names}"
  | .typecheckMissing _src => s!"Syntax error"
  | .higherUniverse _src => s!"No higher universes than Type"
  | .inferUnannotatedLambda _src => s!"Cannot infer type of unannotated lambda"
  | .inferSorry _src => s!"Cannot infer type of sorry"
  | .expectedFunctionType _src names got => s!"Expected function type, got {got.pp .min names}"
  | .typeMismatch src names expected got => s!"{repr src}: Type mismatch: expected\n{expected.pp .min names},\ngot\n{got.pp .min names}"
  | .unboundVariable _src name => s!"Unbound variable {name}"
  | .indexedTypeCtorReturnTypeRequired _src ctorName => s!"{ctorName}: constructor must specify return type for indexed type"
  | .structureResultTypeMustBeType _src structName => s!"{structName}: structure result type must be Type"

end Qdt
