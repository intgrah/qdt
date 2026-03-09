module

public import Qdt.Nbe

@[expose] public section

namespace Qdt

mutual

partial def VTm.defEq {n} : VTm n → VTm n → ElabM Bool
  | .u' i₁, .u' i₂ => return i₁ == i₂
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
  | .pi' _ a₁ ⟨env₁, b₁⟩, .pi' _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val
  | .neutral ne, other => do
      match ← (VTm.neutral ne).whnf with
      | .neutral _ => return false
      | v => v.defEq other
  | other, .neutral ne => do
      match ← (VTm.neutral ne).whnf with
      | .neutral _ => return false
      | v => other.defEq v
  | _, _ => return false

partial def etaDefEq {n} (ne : Neutral n) (other : VTm n) : ElabM Bool := do
  let ⟨.const ctorName _us, sp⟩ := ne
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

partial def Neutral.defEq {n} : Neutral n → Neutral n → ElabM Bool
  | ne₁@⟨h₁, sp₁⟩, ne₂@⟨h₂, sp₂⟩ => do
      match h₁, h₂ with
      | .var v₁, .var v₂ =>
          if v₁ == v₂ then sp₁.defEq sp₂ else return false
      | .const n₁ us₁, .const n₂ us₂ =>
          if n₁ == n₂ && us₁ == us₂ then
            sp₁.defEq sp₂
          else
            match ← deltaReduction n₁ us₁, ← deltaReduction n₂ us₂ with
            | some v₁, some v₂ =>
                (← applySpine sp₁ v₁).defEq (← applySpine sp₂ v₂)
            | some v₁, none =>
                (← applySpine sp₁ v₁).defEq (.neutral ne₂)
            | none, some v₂ =>
                (VTm.neutral ne₁).defEq (← applySpine sp₂ v₂)
            | none, none =>
                return (← etaDefEq ne₁ (.neutral ne₂)) || (← etaDefEq ne₂ (.neutral ne₁))
      | .const n₁ us₁, .var _ =>
          match ← deltaReduction n₁ us₁ with
          | some v₁ => (← applySpine sp₁ v₁).defEq (.neutral ne₂)
          | none => etaDefEq ne₁ (.neutral ne₂)
      | .var _, .const n₂ us₂ =>
          match ← deltaReduction n₂ us₂ with
          | some v₂ => (VTm.neutral ne₁).defEq (← applySpine sp₂ v₂)
          | none => etaDefEq ne₂ (.neutral ne₁)

partial def Spine.defEq {n} : Spine n → Spine n → ElabM Bool
  | .nil, .nil => return true
  | .app sp₁ t₁, .app sp₂ t₂ => return (← t₁.defEq t₂) && (← sp₁.defEq sp₂)
  | .proj sp₁ i₁, .proj sp₂ i₂ => return i₁ == i₂ && (← sp₁.defEq sp₂)
  | _, _ => return false

end

partial def VTy.defEq {n} : VTy n → VTy n → ElabM Bool
  | .u i₁, .u i₂ => return i₁ == i₂
  | .pi ⟨_, a₁⟩ ⟨env₁, b₁⟩, .pi ⟨_, a₂⟩ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val
  | .el n₁, .el n₂ => n₁.defEq n₂
  | _, _ => return false

end Qdt
