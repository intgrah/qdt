import Lean.Data.Name

import Qdt.Control
import Qdt.MLTT.Global
import Qdt.Semantics
import Qdt.MLTT.Syntax

namespace Qdt

open Lean (Name)

mutual

partial def Ty.eval {n c} : Ty c → SemM n c (VTy n)
  | .u => return .u
  | .pi ⟨x, a⟩ b => return .pi ⟨x, ← a.eval⟩ ⟨← read, b⟩
  | .el t => do doEl (← t.eval)

partial def doEl {n} : VTm n → MetaM (VTy n)
  | .piHat x a ⟨env, b⟩ => return .pi ⟨x, ← doEl a⟩ ⟨env, .el b⟩
  | .neutral ne => return .el ne
  | .lam .. => throw (.msg "doEl: expected type code or neutral")

partial def Tm.eval {n c} : Tm c → SemM n c (VTm n)
  | .var i => return (← read).get i
  | .const name => deltaReduction name
  | .lam ⟨x, a⟩ body => return .lam ⟨x, ← a.eval⟩ ⟨← read, body⟩
  | .app f a => do (← f.eval).app (← a.eval)
  | .piHat x a b => return .piHat x (← a.eval) ⟨← read, b⟩
  | .proj i t => do (← t.eval).proj i
  | .letE _x _a t body => do body.eval (.cons (← t.eval) (← read))

partial def VTm.app {n} (f a : VTm n) : MetaM (VTm n) :=
  match f with
  | .lam _param clos => betaReduction clos a
  | .neutral ne => do
    match ← iotaReduction ne a with
    | some result => return result
    | none => return .neutral (ne.app a)
  | .piHat .. => throw (.msg "doApp: expected lambda or neutral")

partial def VTm.proj {n} (i : Nat) : VTm n → MetaM (VTm n)
  | .lam .. => throw (.msg "VTm.proj: expected neutral")
  | .neutral ne => do
    match ← projReduction ne i with
    | some result => return result
    | none => return .neutral (ne.proj i)
  | .piHat .. => throw (.msg s!"VTm.proj: expected neutral, got piHat")

/-- δ-reduction definition unfolding -/
@[inline]
partial def deltaReduction {n} (name : Name) : MetaM (VTm n) := do
  match ← fetchDefinition name with
  | some tm => tm.eval .nil
  | none => return .neutral ⟨.const name, .nil⟩

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
  let ⟨.const recName, sp⟩ := ne
    | return none
  let some info ← fetchRecursor recName
    | return none
  let some spList := sp.toAppList
    | return none
  let numParamsMotivesMinorsIndices :=
    info.numParams + info.numMotives + info.numMinors + info.numIndices
  if spList.length < numParamsMotivesMinorsIndices then
    return none
  let .neutral ⟨.const ctorName, ctorSp⟩ := a
    | return none
  let some rule := info.recRules.find? (fun r => r.ctorName == ctorName)
    | return none
  let paramsMotivesMethods :=
    spList.take (info.numParams + info.numMotives + info.numMinors)
  let some ctorArgs := ctorSp.toAppList
    | return none
  let fields := ctorArgs.drop info.numParams
  let args := paramsMotivesMethods ++ fields
  let envList := args.reverse
  let env := Env.ofList envList
  let nf := rule.numFields
  let rhs := rule.rhs
  if h : envList.length = info.numParams + info.numMotives + info.numMinors + nf then
    let env' : Env n (info.numParams + info.numMotives + info.numMinors + nf) := h ▸ env
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
  let ⟨.const ctor, sp⟩ := ne
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
