module

public import Qdt.Nbe
public import Qdt.Unify
public import Qdt.Theory.Universe.Solve
public import Qdt.Theory.Substitution.Basic

public section

namespace Qdt

variable (q₀ : Key)

inductive ConvState where
  | rigid
  | flex
  | full

def Ctx.lookupTy : {n : Nat} → Idx n → Ctx 0 n → Ty n
  | _ + 1, ⟨0, _⟩, .snoc _ ⟨_, ty⟩ => ty.shiftAfter 0 1
  | _ + 1, ⟨i + 1, h⟩, .snoc rest _ =>
      (Ctx.lookupTy ⟨i, by omega⟩ rest).shiftAfter 0 1

def Ty.collectTele {a : Nat} : Ty a → Σ b, Ctx a b × Ty b :=
  go Tele.nil
where
  go {a b : Nat} (acc : Ctx a b) : Ty b → Σ nb : Nat, Ctx a nb × Ty nb
    | .pi name ty body => go (acc.snoc (name, ty)) body
    | t => ⟨b, acc, t⟩

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
      match fTy with
      | .pi _ _ body => return some (body.subst (Subst.beta arg))
      | _ => return none
  | .mvar id => do
      let some info ← getMetaInfo q₀ id | return none
      return some info.ty.wkClosed
  | _ => return none

mutual

public partial def VTm.conv {n} (a b : VTm n) (cs : ConvState := .rigid) : ElabM q₀ Bool :=
  match a, b with
  | .u' i₁, .u' i₂ => Universe.solveUEq q₀ i₁ i₂
  | .glued ne₁ _, .glued ne₂ _ => do
      match cs with
      | .flex => ne₁.conv ne₂ cs
      | .rigid =>
        if ← ne₁.conv ne₂ .flex then return true
        (← a.whnf q₀).conv (← b.whnf q₀) .full
      | .full => (← a.whnf q₀).conv (← b.whnf q₀) cs
  | .glued _ _, other => do (← a.whnf q₀).conv other cs
  | other, .glued _ _ => do other.conv (← b.whnf q₀) cs
  | .neutral n₁, .neutral n₂ => do
      match cs with
      | .flex => n₁.conv n₂ cs
      | _ =>
        let a' ← (VTm.neutral n₁).whnf q₀
        let b' ← (VTm.neutral n₂).whnf q₀
        match a', b' with
        | .neutral n₁', .neutral n₂' => n₁'.conv n₂' cs
        | _, _ => a'.conv b' cs
  | .lam _ _ ⟨env₁, body₁⟩, .lam _ _ ⟨env₂, body₂⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← body₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← body₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv b₂Val cs
  | .lam _ _ ⟨env, body⟩, other => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          bVal.conv oVal cs
      | _ => return false
  | other, .lam _ _ ⟨env, body⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          oVal.conv bVal cs
      | _ => return false
  | .pi' _ a₁ ⟨env₁, b₁⟩, .pi' _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.conv a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← b₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv b₂Val cs
  | .neutral ne, other => do
      match ← (VTm.neutral ne).whnf q₀ with
      | .neutral ⟨.mvar id, sp⟩ =>
          match cs with
          | .flex => return false
          | _ =>
            if ← solveMVarChecked id sp other then return true
            solveMVarFOApprox id sp other cs
      | .neutral _ => return false
      | v => v.conv other cs
  | other, .neutral ne => do
      match ← (VTm.neutral ne).whnf q₀ with
      | .neutral ⟨.mvar id, sp⟩ =>
          match cs with
          | .flex => return false
          | _ =>
            if ← solveMVarChecked id sp other then return true
            solveMVarFOApprox id sp other cs
      | .neutral _ => return false
      | v => other.conv v cs
  | _, _ => return false

partial def solveMVarFOApprox {n} (id : MVarId) (sp : Spine n) (rhs : VTm n)
    (cs : ConvState) : ElabM q₀ Bool := do
  let rhs ← rhs.whnf q₀
  match rhs with
  | .neutral ⟨rhsHead, .app sp' lastArg⟩ =>
      match sp with
      | .app spRest spLast =>
          if !(← spLast.conv lastArg cs) then return false
          VTm.conv (.neutral ⟨.mvar id, spRest⟩) (.neutral ⟨rhsHead, sp'⟩) cs
      | _ => return false
  | .glued ⟨rhsHead, .app sp' lastArg⟩ _ =>
      match sp with
      | .app spRest spLast =>
          if !(← spLast.conv lastArg cs) then return false
          VTm.conv (.neutral ⟨.mvar id, spRest⟩) (.neutral ⟨rhsHead, sp'⟩) cs
      | _ => return false
  | _ => return false

partial def etaConv {n} (ne : Neutral n) (other : VTm n) (cs : ConvState) : ElabM q₀ Bool := do
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
    proj.conv fields[i] cs
  )

partial def Neutral.conv {n} : Neutral n → Neutral n → ConvState → ElabM q₀ Bool
  | ne₁@⟨h₁, sp₁⟩, ne₂@⟨h₂, sp₂⟩, cs => do
      match h₁, h₂ with
      | .var v₁, .var v₂ =>
          if v₁ == v₂ then sp₁.conv sp₂ cs else return false
      | .const n₁ us₁, .const n₂ us₂ =>
          if n₁ == n₂ && (← Universe.solveUEqList q₀ us₁ us₂) then
            match cs with
            | .rigid =>
                if ← sp₁.conv sp₂ .flex then return true
                match ← deltaReduction q₀ n₁ us₁ with
                | some v₁ => (← applySpine q₀ sp₁ v₁).conv (← applySpine q₀ sp₂ v₁) .full
                | none => sp₁.conv sp₂ .full
            | _ => sp₁.conv sp₂ cs
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← deltaReduction q₀ n₁ us₁, ← deltaReduction q₀ n₂ us₂ with
              | some v₁, some v₂ =>
                  (← applySpine q₀ sp₁ v₁).conv (← applySpine q₀ sp₂ v₂) .full
              | some v₁, none =>
                  (← applySpine q₀ sp₁ v₁).conv (.neutral ne₂) .full
              | none, some v₂ =>
                  (VTm.neutral ne₁).conv (← applySpine q₀ sp₂ v₂) .full
              | none, none =>
                  return (← etaConv ne₁ (.neutral ne₂) cs) || (← etaConv ne₂ (.neutral ne₁) cs)
      | .const n₁ us₁, .var _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₁ us₁ with
            | some v₁ => (← applySpine q₀ sp₁ v₁).conv (.neutral ne₂) .full
            | none => etaConv ne₁ (.neutral ne₂) cs
      | .var _, .const n₂ us₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₂ us₂ with
            | some v₂ => (VTm.neutral ne₁).conv (← applySpine q₀ sp₂ v₂) .full
            | none => etaConv ne₂ (.neutral ne₁) cs
      | .mvar i₁, .mvar i₂ =>
          if i₁ == i₂ then
            match cs with
            | .flex => sp₁.conv sp₂ cs
            | _ =>
              if ← sp₁.conv sp₂ .flex then return true
              match ← metaReduction q₀ i₁ with
              | some v => (← applySpine q₀ sp₁ v).conv (← applySpine q₀ sp₂ v) .full
              | none => sp₁.conv sp₂ .full
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← metaReduction q₀ i₁, ← metaReduction q₀ i₂ with
              | some v₁, some v₂ =>
                  (← applySpine q₀ sp₁ v₁).conv (← applySpine q₀ sp₂ v₂) .full
              | some v₁, none =>
                  (← applySpine q₀ sp₁ v₁).conv (.neutral ne₂) .full
              | none, some v₂ =>
                  (VTm.neutral ne₁).conv (← applySpine q₀ sp₂ v₂) .full
              | none, none =>
                  if ← solveMVarChecked i₁ sp₁ (.neutral ne₂) then return true
                  if ← solveMVarChecked i₂ sp₂ (.neutral ne₁) then return true
                  if ← solveMVarFOApprox i₁ sp₁ (.neutral ne₂) cs then return true
                  solveMVarFOApprox i₂ sp₂ (.neutral ne₁) cs
      | .mvar i₁, _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← metaReduction q₀ i₁ with
            | some v₁ => (← applySpine q₀ sp₁ v₁).conv (.neutral ne₂) .full
            | none =>
              if ← solveMVarChecked i₁ sp₁ (.neutral ne₂) then return true
              solveMVarFOApprox i₁ sp₁ (.neutral ne₂) cs
      | _, .mvar i₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← metaReduction q₀ i₂ with
            | some v₂ => (VTm.neutral ne₁).conv (← applySpine q₀ sp₂ v₂) .full
            | none =>
              if ← solveMVarChecked i₂ sp₂ (.neutral ne₁) then return true
              solveMVarFOApprox i₂ sp₂ (.neutral ne₁) cs

partial def Spine.conv {n} : Spine n → Spine n → ConvState → ElabM q₀ Bool
  | .nil, .nil, _ => return true
  | .app sp₁ t₁, .app sp₂ t₂, cs => return (← t₁.conv t₂ cs) && (← sp₁.conv sp₂ cs)
  | .proj sp₁ i₁, .proj sp₂ i₂, cs => return i₁ == i₂ && (← sp₁.conv sp₂ cs)
  | _, _, _ => return false

public partial def VTy.conv {n} (a b : VTy n) (cs : ConvState := .rigid) : ElabM q₀ Bool :=
  match a, b with
  | .u i₁, .u i₂ => Universe.solveUEq q₀ i₁ i₂
  | .pi _ a₁ ⟨env₁, b₁⟩, .pi _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.conv a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← b₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv b₂Val cs
  | .el n₁, .el n₂ => n₁.conv n₂ cs
  | a, .el ⟨.mvar id, sp⟩ => do
      let aVTm ← (← a.reify q₀).eval q₀ (Env.identity n)
      aVTm.conv (.neutral ⟨.mvar id, sp⟩) cs
  | .el ⟨.mvar id, sp⟩, b => do
      let bVTm ← (← b.reify q₀).eval q₀ (Env.identity n)
      (VTm.neutral ⟨.mvar id, sp⟩).conv bVTm cs
  | _, _ => return false

partial def solveMVarChecked {n} (id : MVarId) (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ Bool := do
  let some ⟨a, body⟩ ← Unify.solveMVar q₀ id sp rhs | return false
  assignMeta q₀ id (Unify.wrapLams a body)
  if let some info ← getMetaInfo q₀ id then
    let ⟨b, paramCtx, codomain⟩ := info.ty.collectTele
    if h : b = a then
      let paramCtx : Ctx 0 a := h ▸ paramCtx
      let codomain : Ty a := h ▸ codomain
      if let some bodyTy ← Tm.inferTy q₀ paramCtx body then
        let codomainV ← codomain.eval q₀ (Env.identity a)
        let bodyTyV ← bodyTy.eval q₀ (Env.identity a)
        match codomainV, bodyTyV with
        | .u _, .u _ => let _ ← codomainV.conv bodyTyV
        | _, _ => pure ()
  return true

end

end Qdt
