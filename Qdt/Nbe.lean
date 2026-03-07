module

public import Lean.Data.Name

public import Qdt.Control
public import Qdt.Theory.Global
public import Qdt.Semantics
public import Qdt.Theory.Syntax

@[expose] public section

namespace Qdt

open Lean (Name)

mutual

partial def Ty.eval {n c} : Ty c → SemM n c (VTy n)
  | .u i => return .u i.normalise
  | .pi ⟨x, a⟩ b => return .pi ⟨x, ← a.eval⟩ ⟨← read, b⟩
  | .el t => do doEl (← t.eval)

partial def doEl {n} : VTm n → ElabM (VTy n)
  | .u' i => return .u i.normalise
  | .pi' x a ⟨env, b⟩ => return .pi ⟨x, ← doEl a⟩ ⟨env, .el b⟩
  | .neutral ne => return .el ne
  | .lam .. => panic! "doEl: expected type code or neutral"

partial def Tm.eval {n c} : Tm c → SemM n c (VTm n)
  | .u' i => return .u' i.normalise
  | .var i => return (← read).get i
  | .const name us => deltaReduction name (us.map Universe.normalise)
  | .lam ⟨x, a⟩ body => return .lam ⟨x, ← a.eval⟩ ⟨← read, body⟩
  | .app fn arg => do (← fn.eval).app (← arg.eval)
  | .pi' ⟨x, a⟩ b => return .pi' x (← a.eval) ⟨← read, b⟩
  | .proj i t => do (← t.eval).proj i
  | .letE _x _a t body => do body.eval (.cons (← t.eval) (← read))

partial def VTm.app {n} (fn arg : VTm n) : ElabM (VTm n) :=
  match fn with
  | .u' .. => panic! "VTm.app: expected lambda or neutral"
  | .lam _param clos => betaReduction clos arg
  | .neutral ne => do
    match ← iotaReduction ne arg with
    | some result => return result
    | none => return .neutral (ne.app arg)
  | .pi' .. => panic! "VTm.app: expected lambda or neutral"

partial def VTm.proj {n} (i : Nat) : VTm n → ElabM (VTm n)
  | .u' .. => panic! "VTm.proj: expected neutral"
  | .lam .. => panic! "VTm.proj: expected neutral"
  | .neutral ne => do
    match ← projReduction ne i with
    | some result => return result
    | none => return .neutral (ne.proj i)
  | .pi' .. => panic! "VTm.proj: expected neutral"

@[inline]
partial def deltaReduction {n} (name : Name) (us : List Universe) : ElabM (VTm n) := do
  match ← fetchDefinition name, ← fetchConstantInfo name with
  | some tm, some info =>
    let subst := info.univParams.zip us
    tm.substLevels subst |>.eval .nil
  | _, _ => return .neutral ⟨.const name us, .nil⟩

@[inline]
partial def betaReduction {n} (clos : ClosTm n) (arg : VTm n) : ElabM (VTm n) :=
  let ⟨env, body⟩ := clos
  body.eval (.cons arg env)

@[inline]
partial def iotaReduction {n}
    (ne : Neutral n)
    (arg : VTm n) :
    ElabM (Option (VTm n)) := do
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
  let .neutral ⟨.const ctorName _ctorUs, ctorSp⟩ := arg
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

@[inline]
partial def projReduction {n}
    (ne : Neutral n)
    (i : Nat) :
    ElabM (Option (VTm n)) := do
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

def VTm.apps {n} : VTm n → List (VTm n) → ElabM (VTm n) :=
  List.foldlM VTm.app

end Qdt
