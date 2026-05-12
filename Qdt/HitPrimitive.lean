module

public import Qdt.Theory.Global

namespace Qdt

open Lean (Name)

/--
```
  Γ,
  n : trunc_index,
  A : Type u,
  P : trunc n A → Type v,
  Pt : (aa : trunc n A) → is_trunc n (P aa),
  H : (a : A) → P (trunc.tr n A a),
  a : A
  ⊢
  H a : P (trunc.tr n A a)
```
-/
def truncRecRule : RecursorRule 5 where
  ctorName := `trunc.tr
  numFields := 1
  rhs := Tm.app (Tm.var ⟨1, by omega⟩) (Tm.var ⟨0, by omega⟩)

/--
```
  Γ,
  A : Type u,
  R : A → A → Type v,
  P : quotient A R → Type w,
  Pc : (a : A) → P (quotient.class_of A R a),
  Pp : (a₁ a₂ : A) → (H : R a₁ a₂) → Pc a₁ =[eq_of_rel R H] Pc a₂,
  a : A
  ⊢
  Pc a : P (quotient.class_of A R a)
```
-/
def quotientRecRule : RecursorRule 5 where
  ctorName := `quotient.class_of
  numFields := 1
  rhs := Tm.app (Tm.var 2) (Tm.var 0)

public def Hit.recogniseAxiom
    (name : Name) (numUnivParams : Nat) (ty : Ty 0) : Option Constant :=
  match name with
  | `trunc => some <| .inductive {
      numUnivParams,
      ty
      numParams := 2
      numIndices := 0
      numCtors := 1
      ctorNames := #v[`trunc.tr]
    }
  | `trunc.tr => some <| .constructor {
      numUnivParams,
      ty,
      indName := `trunc
    }
  | `trunc.rec => some <| .recursor {
      numUnivParams,
      ty
      recName := `trunc.rec
      numParams := 2
      numMotives := 1
      numMinors := 2
      numIndices := 0
      numPointCtors := 1
      recRules := #v[truncRecRule]
    }
  | `quotient => some <| .inductive {
      numUnivParams,
      ty
      numParams := 2
      numIndices := 0
      numCtors := 1
      ctorNames := #v[`quotient.class_of]
      pathCtorNames := #[`quotient.eq_of_rel]
    }
  | `quotient.class_of => some <| .constructor { numUnivParams, ty, indName := `quotient }
  | `quotient.rec => some <| .recursor {
      numUnivParams,
      ty
      recName := `quotient.rec
      numParams := 2
      numMotives := 1
      numMinors := 2
      numIndices := 0
      numPointCtors := 1
      recRules := #v[quotientRecRule]
    }
  | _ => none

end Qdt
