import Qdt.Nbe

namespace Qdt

mutual

partial def VTm.defEq {n} : VTm n → VTm n → MetaM Bool
  | .neutral n₁, .neutral n₂ => n₁.defEq n₂
  | .lam _ ⟨env₁, body₁⟩, .lam _ ⟨env₂, body₂⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← body₁.eval (env₁.weaken.cons var)
      let b₂Val ← body₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val
  | .lam _ ⟨env, body⟩, other => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app var
          bVal.defEq oVal
      | _ => return false
  | other, .lam _ ⟨env, body⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app var
          oVal.defEq bVal
      | _ => return false
  | .piHat _ a₁ ⟨env₁, b₁⟩, .piHat _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val
  | _, _ => return false

private partial def etaDefEq {n} (ne : Neutral n) (other : VTm n) : MetaM Bool := do
  let ⟨.const ctorName, sp⟩ := ne
    | return false
  let some ctorInfo ← fetchConstructor ctorName
    | return false
  let some indInfo ← fetchInductive ctorInfo.indName
    | return false
  if indInfo.numIndices ≠ 0 ∨ indInfo.numMinors ≠ 1 then
    return false
  let some args := sp.toAppList
    | return false
  if args.length < indInfo.numParams then
    return false
  let fields := args.drop indInfo.numParams
  List.finRange fields.length |>.allM (fun i => do
    let proj ← other.proj i.val
    proj.defEq fields[i]
  )

partial def Neutral.defEq {n} : Neutral n → Neutral n → MetaM Bool
  | ne₁@⟨h₁, sp₁⟩, ne₂@⟨h₂, sp₂⟩ => do
      match h₁, h₂ with
      | .var v₁, .var v₂ =>
          if v₁ == v₂ then sp₁.defEq sp₂ else return false
      | .const n₁, .const n₂ =>
          if n₁ == n₂ then
            sp₁.defEq sp₂
          else
            let eta1 ← etaDefEq ⟨.const n₁, sp₁⟩ (.neutral ne₂)
            let eta2 ← etaDefEq ⟨.const n₂, sp₂⟩ (.neutral ne₁)
            return eta1 || eta2
      | .const _, .var _ => etaDefEq ne₁ (.neutral ne₂)
      | .var _, .const _ => etaDefEq ne₂ (.neutral ne₁)

partial def Spine.defEq {n} : Spine n → Spine n → MetaM Bool
  | .nil, .nil => return true
  | .app sp₁ t₁, .app sp₂ t₂ => return (← t₁.defEq t₂) && (← sp₁.defEq sp₂)
  | .proj sp₁ i₁, .proj sp₂ i₂ => return i₁ == i₂ && (← sp₁.defEq sp₂)
  | _, _ => return false

end

partial def VTy.defEq {n} : VTy n → VTy n → MetaM Bool
  | .u, .u => return true
  | .pi ⟨_, a₁⟩ ⟨env₁, b₁⟩, .pi ⟨_, a₂⟩ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val
  | .el n₁, .el n₂ => n₁.defEq n₂
  | _, _ => return false

end Qdt
