module

public import Qdt.Control

public section

namespace Qdt

open Lean (Name)

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

mutual

partial def Ty.eval {n c} : Ty c → SemM ι₀ q₀ n c (VTy n)
  | .u i => return .u i
  | .pi x a b => return .pi x (← a.eval) ⟨← read, b⟩
  | .el t => do doEl (← t.eval)

partial def doEl {n} : VTm n → ElabM ι₀ q₀ (VTy n)
  | .u' i => return .u i
  | .pi' x a ⟨env, b⟩ => return .pi x (← doEl a) ⟨env, .el b⟩
  | .neutral ne => do
    match ← (VTm.neutral ne).whnf with
    | .neutral ne' => return .el ne'
    | v => doEl v
  | .lam .. => panic! "doEl: expected type code or neutral"

partial def Tm.eval {n c} : Tm c → SemM ι₀ q₀ n c (VTm n)
  | .u' i => return .u' i
  | .var i => return (← read).get i
  | .const name us => return .neutral ⟨.const name us, .nil⟩
  | .lam x a body => return .lam x (← a.eval) ⟨← read, body⟩
  | .app fn arg => do (← fn.eval).app (← arg.eval)
  | .pi' x a b => return .pi' x (← a.eval) ⟨← read, b⟩
  | .proj i t => do (← t.eval).proj i
  | .letE _x _a t body => do body.eval (.cons (← t.eval) (← read))

partial def VTm.app {n} (fn arg : VTm n) : ElabM ι₀ q₀ (VTm n) :=
  match fn with
  | .u' .. => panic! "VTm.app: expected lambda or neutral"
  | .lam _ _ clos => betaReduction clos arg
  | .neutral ne => do
    match ← (VTm.neutral ne).whnf with
    | .lam _ _ clos => betaReduction clos arg
    | .neutral ne' =>
      match ← iotaReduction ne' arg with
      | some result => return result
      | none => return .neutral (ne'.app arg)
    | _ => panic! "VTm.app: unexpected whnf result"
  | .pi' .. => panic! "VTm.app: expected lambda or neutral"

partial def VTm.proj {n} (i : Nat) : VTm n → ElabM ι₀ q₀ (VTm n)
  | .u' .. => panic! "VTm.proj: expected neutral"
  | .lam .. => panic! "VTm.proj: expected neutral"
  | .neutral ne => do
    match ← (VTm.neutral ne).whnf with
    | .neutral ne' =>
      match ← projReduction ne' i with
      | some result => return result
      | none => return .neutral (ne'.proj i)
    | v => v.proj i
  | .pi' .. => panic! "VTm.proj: expected neutral"

partial def deltaReduction {n} (name : Name) (us : List Universe) : ElabM ι₀ q₀ (Option (VTm n)) := do
  let some tm ← fetchDefinition ι₀ q₀ name | return none
  let some info ← fetchConstantInfo ι₀ q₀ name | return none
  let subst := info.univParams.zip us
  return some (← (tm.substLevels subst).eval .nil)

partial def applySpine {n} : Spine n → VTm n → ElabM ι₀ q₀ (VTm n)
  | .nil, v => return v
  | .app sp arg, v => do (← applySpine sp v).app arg
  | .proj sp i, v => do (← applySpine sp v).proj i

partial def VTm.whnf {n} : VTm n → ElabM ι₀ q₀ (VTm n)
  | .neutral ⟨.const name us, sp⟩ => do
    match ← deltaReduction name us with
    | some v => (← applySpine sp v).whnf
    | none => return .neutral ⟨.const name us, sp⟩
  | v => return v

partial def betaReduction {n} (clos : ClosTm n) (arg : VTm n) : ElabM ι₀ q₀ (VTm n) :=
  let ⟨env, body⟩ := clos
  body.eval (.cons arg env)

partial def iotaReduction {n}
    (ne : Neutral n)
    (arg : VTm n) :
    ElabM ι₀ q₀ (Option (VTm n)) := do
  let ⟨.const recName recUs, sp⟩ := ne
    | return none
  let some info ← fetchRecursor ι₀ q₀ recName
    | return none
  let some spList := sp.toAppList
    | return none
  let numParamsMotivesMinors := info.numParams + info.numMotives + info.numMinors
  let numParamsMotivesMinorsIndices := numParamsMotivesMinors + info.numIndices
  if spList.length < numParamsMotivesMinorsIndices then
    return none
  let .neutral ⟨.const ctorName _ctorUs, ctorSp⟩ ← arg.whnf
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

partial def projReduction {n}
    (ne : Neutral n)
    (i : Nat) :
    ElabM ι₀ q₀ (Option (VTm n)) := do
  let ⟨.const ctor _us, sp⟩ := ne
    | return none
  let some ctorInfo ← fetchConstructor ι₀ q₀ ctor
    | return none
  let some indInfo ← fetchInductive ι₀ q₀ ctorInfo.indName
    | return none
  let some spList := sp.toAppList
    | return none
  return spList[indInfo.numParams + i]?

end

def VTm.apps {n} : VTm n → List (VTm n) → ElabM ι₀ q₀ (VTm n) :=
  List.foldlM (VTm.app ι₀ q₀)

end Qdt
