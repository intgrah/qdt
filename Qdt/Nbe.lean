module

public import Qdt.Control

public section

namespace Qdt

open Lean (Name)

variable (q₀ : Key)

mutual

partial def Ty.eval {n c} : Ty c → SemM q₀ n c (VTy n)
  | .u i => return .u i
  | .pi x bi a b => return .pi x bi (← a.eval) ⟨← read, b⟩
  | .el t => do doEl (← t.eval)

partial def doEl {n} : VTm n → ElabM q₀ (VTy n)
  | .u' i => return .u i
  | .pi' x bi a ⟨env, b⟩ => return .pi x bi (← doEl a) ⟨env, .el b⟩
  | .neutral ne => do
    match ← (VTm.neutral ne).whnf with
    | .neutral ne' => return .el ne'
    | v => doEl v
  | .glued ne key => do doEl (← (VTm.glued ne key).whnf)
  | .lam .. => panic! "doEl: expected type code or neutral"

partial def Tm.eval {n c} : Tm c → SemM q₀ n c (VTm n)
  | .u' i => return .u' i
  | .var i => return (← read).get i
  | .const name us => do
    match ← fetchConstant q₀ name with
    | some (.definition _) => return .glued ⟨.const name us, .nil⟩ (.const name us)
    | some _ => return .neutral ⟨.const name us, .nil⟩
    | none => return .neutral ⟨.const name us, .nil⟩
  | .lam x bi a body => return .lam x bi (← a.eval) ⟨← read, body⟩
  | .app fn arg => do (← fn.eval).app (← arg.eval)
  | .pi' x bi a b => return .pi' x bi (← a.eval) ⟨← read, b⟩
  | .proj i t => do (← t.eval).proj i
  | .letE _x _a t body => do body.eval (.cons (← t.eval) (← read))
  | .mvar id => return .glued ⟨.mvar id, .nil⟩ (.mvar id)

partial def VTm.app {n} (fn arg : VTm n) : ElabM q₀ (VTm n) :=
  match fn with
  | .u' .. => panic! "VTm.app: expected lambda or neutral"
  | .lam _ _ _ clos => betaReduction clos arg
  | .neutral ne => return .neutral (ne.app arg)
  | .glued ne key => return .glued (ne.app arg) key
  | .pi' .. => panic! "VTm.app: expected lambda or neutral"

partial def VTm.proj {n} (i : Nat) : VTm n → ElabM q₀ (VTm n)
  | .u' .. => panic! "VTm.proj: expected neutral"
  | .lam .. => panic! "VTm.proj: expected neutral"
  | .neutral ne => do
    match ← (VTm.neutral ne).whnf with
    | .neutral ne' =>
      match ← projReduction (ne'.proj i) with
      | some result => return result
      | none => return .neutral (ne'.proj i)
    | v => v.proj i
  | .glued ne key => do (← (VTm.glued ne key).whnf).proj i
  | .pi' .. => panic! "VTm.proj: expected neutral"

partial def deltaReduction {n} (name : Name) (us : List Universe) : ElabM q₀ (Option (VTm n)) := do
  if let some v := (← get).deltaCache[(name, us)]? then
    return some (VTm.weaken (Nat.zero_le n) v)
  let some (.definition info) ← fetchConstant q₀ name | return none
  let v ← (info.tm.instantiateParams info.univParams us).eval Env.nil
  modify fun st => { st with deltaCache := st.deltaCache.insert (name, us) v }
  return some (VTm.weaken (Nat.zero_le n) v)


partial def metaReduction {n} (id : MVarId) (sp : Spine n) :
    ElabM q₀ (Option (VTm n)) := do
  let info ← getMetaInfo q₀ id
  let some body := info.solution | return none
  let some args := sp.toAppList | return none
  if hGe : info.arity ≤ args.length then
    let envList := (args.take info.arity).reverse
    have hLen : envList.length = info.arity := by
      simp [envList, List.length_reverse, List.length_take]; omega
    let env : Env n info.arity := hLen ▸ Env.ofList envList
    some <$> (args.drop info.arity).foldlM (·.app ·) (← body.eval env)
  else
    let lam : VTm n ← (Tm.lams info.ctx body).eval Env.nil
    some <$> args.foldlM (·.app ·) lam

partial def applySpine {n} : Spine n → VTm n → ElabM q₀ (VTm n)
  | .nil, v => return v
  | .app sp arg, v => do (← applySpine sp v).app arg
  | .proj sp i, v => do (← applySpine sp v).proj i

partial def VTm.whnf {n} : VTm n → ElabM q₀ (VTm n)
  | .neutral ⟨.const name us, sp⟩ => do
    match ← deltaReduction name us with
    | some v => (← applySpine sp v).whnf
    | none =>
      match ← iotaReduction ⟨.const name us, sp⟩ with
      | some v => v.whnf
      | none => return .neutral ⟨.const name us, sp⟩
  | .neutral ⟨.mvar id, sp⟩ => do
    match ← metaReduction id sp with
    | some v => v.whnf
    | none => return .neutral ⟨.mvar id, sp⟩
  | .glued ⟨_, sp⟩ (.const name us) => do
    match ← deltaReduction name us with
    | some v => (← applySpine sp v).whnf
    | none =>
      match ← iotaReduction ⟨.const name us, sp⟩ with
      | some v => v.whnf
      | none => return .neutral ⟨.const name us, sp⟩
  | .glued ⟨_, sp⟩ (.mvar id) => do
    match ← metaReduction id sp with
    | some v => v.whnf
    | none => return .neutral ⟨.mvar id, sp⟩

  | v => return v

partial def betaReduction {n} (clos : ClosTm n) (arg : VTm n) : ElabM q₀ (VTm n) := do
  let ⟨env, body⟩ := clos
  body.eval (.cons arg env)

partial def iotaReduction {n}
    (ne : Neutral n) :
    ElabM q₀ (Option (VTm n)) := do
  let ⟨.const recName recUs, sp⟩ := ne
    | return none
  let some info ← fetchRecursor q₀ recName
    | return none
  let some spList := sp.toAppList
    | return none
  let numParamsMotivesMinors := info.numParams + info.numMotives + info.numMinors
  let numTotal := numParamsMotivesMinors + info.numIndices + 1
  if spList.length < numTotal then
    return none
  if spList.length < numTotal then
    return none
  let major := spList[numTotal - 1]!
  let .neutral ⟨.const ctorName _ctorUs, ctorSp⟩ ← major.whnf
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
  let rhs := rule.rhs.instantiateParams info.univParams recUs
  if h : envList.length = numParamsMotivesMinors + numFields then
    let env' : Env n (numParamsMotivesMinors + numFields) := h ▸ env
    let result ← rhs.eval env'
    let remaining := spList.drop numTotal
    some <$> remaining.foldlM (fun acc v => acc.app v) result
  else
    return none

partial def projReduction {n}
    (ne : Neutral n) :
    ElabM q₀ (Option (VTm n)) := do
  let ⟨.const ctor _us, sp⟩ := ne
    | return none
  let some ctorInfo ← fetchConstructor q₀ ctor
    | return none
  let some indInfo ← fetchInductive q₀ ctorInfo.indName
    | return none
  match sp with
  | .proj sp' i =>
    let some spList := sp'.toAppList
      | return none
    let some val := spList[indInfo.numParams + i]?
      | return none
    return some val
  | _ => return none

end

def VTm.apps {n} : VTm n → List (VTm n) → ElabM q₀ (VTm n) :=
  List.foldlM (VTm.app q₀)

end Qdt
