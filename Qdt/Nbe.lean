import Lean.Data.Name

import Qdt.Control
import Qdt.MLTT.Global
import Qdt.Semantics
import Qdt.MLTT.Syntax

namespace Qdt

open Lean (Name)

mutual

partial def Ty.eval {n c} : Ty c → SemM n c (VTy n)
  | .u _ i => return .u i.normalise
  | .pi _ ⟨_, x, a⟩ b => return .pi ⟨x, ← a.eval⟩ ⟨← read, b⟩
  | .el _ t => do doEl (← t.eval)

partial def doEl {n} : VTm n → MetaM (VTy n)
  | .u' i => return .u i.normalise
  | .pi' x a ⟨env, b⟩ => return .pi ⟨x, ← doEl a⟩ ⟨env, .el none b⟩
  | .neutral ne => return .el ne
  | .lam .. => throw (.msg "doEl: expected type code or neutral")

partial def Tm.eval {n c} : Tm c → SemM n c (VTm n)
  | .u' _ i => return .u' i.normalise
  | .var _ i => return (← read).get i
  | .const _ name us => deltaReduction name (us.map Universe.normalise)
  | .lam _ ⟨_, x, a⟩ body => return .lam ⟨x, ← a.eval⟩ ⟨← read, body⟩
  | .app _ f a => do (← f.eval).app (← a.eval)
  | .pi' _ ⟨_, x, a⟩ b => return .pi' x (← a.eval) ⟨← read, b⟩
  | .proj _ i t => do (← t.eval).proj i
  | .letE _ _x _a t body => do body.eval (.cons (← t.eval) (← read))

partial def VTm.app {n} (f a : VTm n) : MetaM (VTm n) :=
  match f with
  | .u' .. => throw (.msg "VTm.app: expected lambda or neutral")
  | .lam _param clos => betaReduction clos a
  | .neutral ne => do
    match ← iotaReduction ne a with
    | some result => return result
    | none => return .neutral (ne.app a)
  | .pi' .. => throw (.msg "VTm.app: expected lambda or neutral")

partial def VTm.proj {n} (i : Nat) : VTm n → MetaM (VTm n)
  | .u' .. => throw (.msg "VTm.proj: expected neutral")
  | .lam .. => throw (.msg "VTm.proj: expected neutral")
  | .neutral ne => do
    match ← projReduction ne i with
    | some result => return result
    | none => return .neutral (ne.proj i)
  | .pi' .. => throw (.msg s!"VTm.proj: expected neutral")

/-- δ-reduction definition unfolding -/
@[inline]
partial def deltaReduction {n} (name : Name) (us : List Universe) : MetaM (VTm n) := do
  match ← fetchDefinition name, ← fetchConstantInfo name with
  | some tm, some info =>
    let subst := info.univParams.zip us
    tm.substLevels subst |>.eval .nil
  | _, _ => return .neutral ⟨.const name us, .nil⟩

/-- β-reduction taken with a pinch of salt. Substitution is delayed because we have closures. -/
@[inline]
partial def betaReduction {n} (f : ClosTm n) (a : VTm n) : MetaM (VTm n) :=
  let ⟨env, body⟩ := f
  body.eval (.cons a env)

/--
ι-reduction is the computation rule for inductive type recursors.
```
This example shows one stage in the computation of 1 + 1

                              rec      motive        zero     succ                major    field
---------------------------------------------------------------------------------------------------
                              Nat.rec (fun _ => Nat) Nat.one (fun _ => Nat.succ) (Nat.succ Nat.zero) ⤳
(fun _ => Nat.succ) Nat.zero (Nat.rec (fun _ => Nat) Nat.one (fun _ => Nat.succ) Nat.zero)
------------------------------------------------------------------------------------------
 succ               field    (rec      motive        zero     succ               field   )
```
-/
@[inline]
partial def iotaReduction {n}
    (ne : Neutral n)
    (a : VTm n) : -- possible major premise
    MetaM (Option (VTm n)) := do
  let ⟨.const recName recUs, sp⟩ := ne
    | return none
  let some info ← fetchRecursor recName
    | return none
  let some spList := sp.toAppList
    | return none
  let numParamsMotivesMinors := info.numParams + info.numMotives + info.numMinors
  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + info.numIndices
  if spList.length < numParamsMotivesMinorsIndices then
    return none
  let .neutral ⟨.const ctorName _ctorUs, ctorSp⟩ := a
    | return none
  let some rule := info.recRules.find? (fun r => r.ctorName == ctorName)
    | return none
  let paramsMotivesMethods :=
    spList.take numParamsMotivesMinors
  let some ctorArgs := ctorSp.toAppList
    | return none
  let fields := ctorArgs.drop info.numParams
  let args := paramsMotivesMethods ++ fields
  let envList := args.reverse
  let env := Env.ofList envList
  let numFields := rule.numFields
  let univSubst := info.univParams.zip recUs
  let rhs := rule.rhs.substLevels univSubst
  if h : envList.length = numParamsMotivesMinors + numFields then
    let env' : Env n (numParamsMotivesMinors + numFields) := h ▸ env
    rhs.eval env'
  else
    return none

/--
Prod-reduction is the computation rule for projections.

(Prod.mk Nat Nat 2 3).0 ⤳ 2
-/
@[inline]
partial def projReduction {n}
    (ne : Neutral n)
    (i : Nat) :
    MetaM (Option (VTm n)) := do
  let ⟨.const ctor _us, sp⟩ := ne
    | return none
  let some ctorInfo ← fetchConstructor ctor
    | return none
  let some indInfo ← fetchInductive ctorInfo.indName
    | return none
  let some spList := sp.toAppList
    | return none
  return spList[indInfo.numParams + i]?

end

def VTm.apps {n} : VTm n → List (VTm n) → MetaM (VTm n) :=
  List.foldlM VTm.app

end Qdt
