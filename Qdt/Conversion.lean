module

public import Qdt.Nbe
public import Qdt.Unify
public import Qdt.Theory.Universe.Solve
public import Qdt.Theory.Substitution.Basic

public section

namespace Qdt

variable (q₀ : Key)

inductive ConvState
  | rigid
  | flex
  | full

def Ctx.lookupTy : {n : Nat} → Idx n → Ctx 0 n → Ty n
  | _ + 1, ⟨0, _⟩, .snoc _ ⟨_, ty⟩ => ty.shiftAfter 0 1
  | _ + 1, ⟨i + 1, h⟩, .snoc rest _ =>
      (Ctx.lookupTy ⟨i, by omega⟩ rest).shiftAfter 0 1

partial def Tm.inferTy {a : Nat} (q₀ : Key) (paramCtx : Ctx 0 a) : Tm a →
    ElabM q₀ (Option (Ty a))
  | .var i => return some (paramCtx.lookupTy i)
  | .u' u => return some (.u u.mkSucc)
  | .const c us => do
      let some info ← fetchConstantInfo q₀ c | return none
      if info.numUnivParams != us.length then return none
      return some (info.ty.substLevels us).wkClosed
  | .app f arg => do
      let some fTy ← Tm.inferTy q₀ paramCtx f | return none
      let .pi _ _ body := fTy | return none
      return some (body.subst (Subst.beta arg))
  | .lam name ty body => do
      let some bodyTy ← Tm.inferTy q₀ (paramCtx.snoc (name, ty)) body | return none
      return some (.pi name ty bodyTy)
  | .pi' name dom cod => do
      let some domTy ← Tm.inferTy q₀ paramCtx dom | return none
      let .u uA := domTy | return none
      let some codTy ← Tm.inferTy q₀ (paramCtx.snoc (name, .el dom)) cod | return none
      let .u uB := codTy | return none
      return some (.u (uA.mkMax uB))
  | .letE name ty rhs body => do
      let some bodyTy ← Tm.inferTy q₀ (paramCtx.snoc (name, ty)) body | return none
      return some (bodyTy.subst (Subst.beta rhs))
  | .proj i t => do
      let some tTy ← Tm.inferTy q₀ paramCtx t | return none
      let .el body := tTy | return none
      let (head, structArgs) := Tm.splitApps body
      let .const structName us := head | return none
      let some indInfo ← fetchInductive q₀ structName | return none
      if indInfo.numCtors ≠ 1 then return none
      let some ctorName := indInfo.ctorNames.toList.head? | return none
      let some ctorInfo ← fetchConstructor q₀ ctorName | return none
      let ctorTy : Ty a := (ctorInfo.ty.substLevels us).wkClosed
      let applied := List.range i |>.foldl (fun ty j => ty.bind (·.applyArg (.proj j t)))
                       (structArgs.foldl (fun ty arg => ty.bind (·.applyArg arg)) (some ctorTy))
      return applied.bind fun
        | .pi _ fieldTy _ => some fieldTy
        | _ => none
  | .mvar id => do
      let info ← getMetaInfo q₀ id
      return some (Ty.pis info.ctx info.ty).wkClosed

mutual

public partial def VTm.conv {n} (cctx : VCtx n) (a b : VTm n) (cs : ConvState := .rigid) :
    ElabM q₀ Bool :=
  match a, b with
  | .u' i₁, .u' i₂ => Universe.solveUEq q₀ i₁ i₂
  | .glued ne₁ _, .glued ne₂ _ => do
      match cs with
      | .flex => ne₁.conv cctx ne₂ cs
      | .rigid =>
        if ← ne₁.conv cctx ne₂ .flex then return true
        (← a.whnf q₀).conv cctx (← b.whnf q₀) .full
      | .full => (← a.whnf q₀).conv cctx (← b.whnf q₀) cs
  | .glued _ _, other => do (← a.whnf q₀).conv cctx other cs
  | other, .glued _ _ => do other.conv cctx (← b.whnf q₀) cs
  | .neutral n₁, .neutral n₂ => do
      match cs with
      | .flex => n₁.conv cctx n₂ cs
      | _ =>
        let a' ← (VTm.neutral n₁).whnf q₀
        let b' ← (VTm.neutral n₂).whnf q₀
        match a', b' with
        | .neutral n₁', .neutral n₂' => n₁'.conv cctx n₂' cs
        | _, _ => a'.conv cctx b' cs
  | .lam name aTy ⟨env₁, body₁⟩, .lam _ _ ⟨env₂, body₂⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← body₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← body₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv (cctx.snoc (.bound name aTy)) b₂Val cs
  | .lam name aTy ⟨env, body⟩, other => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          bVal.conv (cctx.snoc (.bound name aTy)) oVal cs
      | _ => return false
  | other, .lam name aTy ⟨env, body⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          oVal.conv (cctx.snoc (.bound name aTy)) bVal cs
      | _ => return false
  | .pi' name a₁ ⟨env₁, b₁⟩, .pi' _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.conv cctx a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← b₂.eval q₀ (env₂.weaken.cons var)
      let aTy ← doEl q₀ a₁
      b₁Val.conv (cctx.snoc (.bound name aTy)) b₂Val cs
  | .neutral ne, other => do
      match ← (VTm.neutral ne).whnf q₀ with
      | .neutral ⟨.mvar id, sp⟩ =>
          match cs with
          | .flex => return false
          | _ =>
            if ← solveMVarChecked id cctx sp other then return true
            solveMVarFOApprox id cctx sp other cs
      | .neutral _ => return false
      | v => v.conv cctx other cs
  | other, .neutral ne => do
      match ← (VTm.neutral ne).whnf q₀ with
      | .neutral ⟨.mvar id, sp⟩ =>
          match cs with
          | .flex => return false
          | _ =>
            if ← solveMVarChecked id cctx sp other then return true
            solveMVarFOApprox id cctx sp other cs
      | .neutral _ => return false
      | v => other.conv cctx v cs
  | _, _ => return false

partial def solveMVarFOApprox {n} (id : MVarId) (cctx : VCtx n) (sp : Spine n) (rhs : VTm n)
    (cs : ConvState) : ElabM q₀ Bool := do
  let rhs ← rhs.whnf q₀
  match rhs with
  | .neutral ⟨rhsHead, .app sp' lastArg⟩ =>
      match sp with
      | .app spRest spLast =>
          if !(← spLast.conv cctx lastArg cs) then return false
          VTm.conv cctx (.neutral ⟨.mvar id, spRest⟩) (.neutral ⟨rhsHead, sp'⟩) cs
      | _ => return false
  | .glued ⟨rhsHead, .app sp' lastArg⟩ _ =>
      match sp with
      | .app spRest spLast =>
          if !(← spLast.conv cctx lastArg cs) then return false
          VTm.conv cctx (.neutral ⟨.mvar id, spRest⟩) (.neutral ⟨rhsHead, sp'⟩) cs
      | _ => return false
  | _ => return false

partial def etaConv {n} (cctx : VCtx n) (ne : Neutral n) (other : VTm n) (cs : ConvState) :
    ElabM q₀ Bool := do
  let ⟨.const ctorName _us, sp⟩ := ne
    | return false
  let some ctorInfo ← fetchConstructor q₀ ctorName
    | return false
  let some indInfo ← fetchInductive q₀ ctorInfo.indName
    | return false
  if indInfo.numIndices ≠ 0 ∨ indInfo.numCtors ≠ 1 then
    return false
  let some args := sp.toAppList
    | return false
  if args.length < indInfo.numParams then
    return false
  let fields := args.drop indInfo.numParams
  List.finRange fields.length |>.allM (fun (i : Fin fields.length) => do
    let proj ← other.proj q₀ i.val
    proj.conv cctx fields[i] cs
  )

partial def Neutral.conv {n} (cctx : VCtx n) :
    Neutral n → Neutral n → ConvState → ElabM q₀ Bool
  | ne₁@⟨h₁, sp₁⟩, ne₂@⟨h₂, sp₂⟩, cs => do
      match h₁, h₂ with
      | .var v₁, .var v₂ =>
          if v₁ == v₂ then sp₁.conv cctx sp₂ cs else return false
      | .const n₁ us₁, .const n₂ us₂ =>
          if n₁ == n₂ && (← Universe.solveUEqList q₀ us₁ us₂) then
            match cs with
            | .rigid =>
                if ← sp₁.conv cctx sp₂ .flex then return true
                match ← deltaReduction q₀ n₁ us₁ with
                | some v₁ =>
                    (← applySpine q₀ sp₁ v₁).conv cctx (← applySpine q₀ sp₂ v₁) .full
                | none => sp₁.conv cctx sp₂ .full
            | _ => sp₁.conv cctx sp₂ cs
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← deltaReduction q₀ n₁ us₁, ← deltaReduction q₀ n₂ us₂ with
              | some v₁, some v₂ =>
                  (← applySpine q₀ sp₁ v₁).conv cctx (← applySpine q₀ sp₂ v₂) .full
              | some v₁, none =>
                  (← applySpine q₀ sp₁ v₁).conv cctx (.neutral ne₂) .full
              | none, some v₂ =>
                  (VTm.neutral ne₁).conv cctx (← applySpine q₀ sp₂ v₂) .full
              | none, none =>
                  return (← etaConv cctx ne₁ (.neutral ne₂) cs)
                    || (← etaConv cctx ne₂ (.neutral ne₁) cs)
      | .const n₁ us₁, .var _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₁ us₁ with
            | some v₁ => (← applySpine q₀ sp₁ v₁).conv cctx (.neutral ne₂) .full
            | none => etaConv cctx ne₁ (.neutral ne₂) cs
      | .var _, .const n₂ us₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₂ us₂ with
            | some v₂ => (VTm.neutral ne₁).conv cctx (← applySpine q₀ sp₂ v₂) .full
            | none => etaConv cctx ne₂ (.neutral ne₁) cs
      | .mvar i₁, .mvar i₂ =>
          if i₁ == i₂ then
            match cs with
            | .flex => sp₁.conv cctx sp₂ cs
            | _ =>
              if ← sp₁.conv cctx sp₂ .flex then return true
              match ← metaReduction q₀ i₁ sp₁, ← metaReduction q₀ i₁ sp₂ with
              | some v₁, some v₂ => v₁.conv cctx v₂ .full
              | _, _ => sp₁.conv cctx sp₂ .full
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← metaReduction q₀ i₁ sp₁, ← metaReduction q₀ i₂ sp₂ with
              | some v₁, some v₂ => v₁.conv cctx v₂ .full
              | some v₁, none => v₁.conv cctx (.neutral ne₂) .full
              | none, some v₂ => (VTm.neutral ne₁).conv cctx v₂ .full
              | none, none =>
                  if ← solveMVarChecked i₁ cctx sp₁ (.neutral ne₂) then return true
                  if ← solveMVarChecked i₂ cctx sp₂ (.neutral ne₁) then return true
                  if ← solveMVarFOApprox i₁ cctx sp₁ (.neutral ne₂) cs then return true
                  solveMVarFOApprox i₂ cctx sp₂ (.neutral ne₁) cs
      | .mvar i₁, _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← metaReduction q₀ i₁ sp₁ with
            | some v₁ => v₁.conv cctx (.neutral ne₂) .full
            | none =>
              if ← solveMVarChecked i₁ cctx sp₁ (.neutral ne₂) then return true
              solveMVarFOApprox i₁ cctx sp₁ (.neutral ne₂) cs
      | _, .mvar i₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← metaReduction q₀ i₂ sp₂ with
            | some v₂ => (VTm.neutral ne₁).conv cctx v₂ .full
            | none =>
              if ← solveMVarChecked i₂ cctx sp₂ (.neutral ne₁) then return true
              solveMVarFOApprox i₂ cctx sp₂ (.neutral ne₁) cs

partial def Spine.conv {n} (cctx : VCtx n) :
    Spine n → Spine n → ConvState → ElabM q₀ Bool
  | .nil, .nil, _ => return true
  | .app sp₁ t₁, .app sp₂ t₂, cs =>
      return (← sp₁.conv cctx sp₂ cs) && (← t₁.conv cctx t₂ cs)
  | .proj sp₁ i₁, .proj sp₂ i₂, cs =>
      return i₁ == i₂ && (← sp₁.conv cctx sp₂ cs)
  | _, _, _ => return false

public partial def VTy.conv {n} (cctx : VCtx n) (a b : VTy n) (cs : ConvState := .rigid) :
    ElabM q₀ Bool :=
  match a, b with
  | .u i₁, .u i₂ => Universe.solveUEq q₀ i₁ i₂
  | .pi name a₁ ⟨env₁, b₁⟩, .pi _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.conv cctx a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← b₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv (cctx.snoc (.bound name a₁)) b₂Val cs
  | .el n₁, .el n₂ => n₁.conv cctx n₂ cs
  | a, .el ⟨.mvar id, sp⟩ => do
      let aVTm ← (← a.reify q₀).eval q₀ (Env.identity n)
      aVTm.conv cctx (.neutral ⟨.mvar id, sp⟩) cs
  | .el ⟨.mvar id, sp⟩, b => do
      let bVTm ← (← b.reify q₀).eval q₀ (Env.identity n)
      (VTm.neutral ⟨.mvar id, sp⟩).conv cctx bVTm cs
  | _, _ => return false

partial def solveMVarChecked {n} (id : MVarId) (cctx : VCtx n) (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ Bool := do
  let info ← getMetaInfo q₀ id
  let normalizedTy ← (← info.ty.eval q₀ (Env.identity info.arity)).quote q₀
  let infoNorm : MetaInfo := { info with ty := normalizedTy }
  let some soln ← infoNorm.solve q₀ id cctx sp rhs | return false
  assignMeta q₀ infoNorm id soln
  if let some codU := normalizedTy.getResultUniverse? then
    if let some (.u bodyU) ← Tm.inferTy q₀ info.ctx soln then
      let _ ← Universe.solveUEq q₀ codU bodyU
  return true

end

end Qdt
