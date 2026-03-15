module

public import Qdt.Nbe

public section

namespace Qdt

inductive ConvState where
  | rigid
  | flex
  | full

mutual

public partial def VTm.defEq {n} (a b : VTm n) (cs : ConvState := .rigid) : ElabM Bool :=
  match a, b with
  | .u' i₁, .u' i₂ => return i₁ == i₂
  | .neutral n₁, .neutral n₂ => n₁.defEq n₂ cs
  | .lam _ _ ⟨env₁, body₁⟩, .lam _ _ ⟨env₂, body₂⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← body₁.eval (env₁.weaken.cons var)
      let b₂Val ← body₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val cs
  | .lam _ _ ⟨env, body⟩, other => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app var
          bVal.defEq oVal cs
      | _ => return false
  | other, .lam _ _ ⟨env, body⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app var
          oVal.defEq bVal cs
      | _ => return false
  | .pi' _ a₁ ⟨env₁, b₁⟩, .pi' _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val cs
  | .neutral ne, other => do
      match ← (VTm.neutral ne).whnf with
      | .neutral _ => return false
      | v => v.defEq other cs
  | other, .neutral ne => do
      match ← (VTm.neutral ne).whnf with
      | .neutral _ => return false
      | v => other.defEq v cs
  | _, _ => return false

partial def etaDefEq {n} (ne : Neutral n) (other : VTm n) (cs : ConvState) : ElabM Bool := do
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
  List.finRange fields.length |>.allM (fun (i : Fin fields.length) => do
    let proj ← other.proj i.val
    proj.defEq fields[i] cs
  )

partial def Neutral.defEq {n} : Neutral n → Neutral n → ConvState → ElabM Bool
  | ne₁@⟨h₁, sp₁⟩, ne₂@⟨h₂, sp₂⟩, cs => do
      match h₁, h₂ with
      | .var v₁, .var v₂ =>
          if v₁ == v₂ then sp₁.defEq sp₂ cs else return false
      | .const n₁ us₁, .const n₂ us₂ =>
          if n₁ == n₂ && us₁ == us₂ then
            match cs with
            | .rigid =>
                if ← sp₁.defEq sp₂ .flex then return true
                match ← deltaReduction n₁ us₁ with
                | some v₁ => (← applySpine sp₁ v₁).defEq (← applySpine sp₂ v₁) .full
                | none => sp₁.defEq sp₂ .full
            | _ => sp₁.defEq sp₂ cs
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← deltaReduction n₁ us₁, ← deltaReduction n₂ us₂ with
              | some v₁, some v₂ =>
                  (← applySpine sp₁ v₁).defEq (← applySpine sp₂ v₂) .full
              | some v₁, none =>
                  (← applySpine sp₁ v₁).defEq (.neutral ne₂) .full
              | none, some v₂ =>
                  (VTm.neutral ne₁).defEq (← applySpine sp₂ v₂) .full
              | none, none =>
                  return (← etaDefEq ne₁ (.neutral ne₂) cs) || (← etaDefEq ne₂ (.neutral ne₁) cs)
      | .const n₁ us₁, .var _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction n₁ us₁ with
            | some v₁ => (← applySpine sp₁ v₁).defEq (.neutral ne₂) .full
            | none => etaDefEq ne₁ (.neutral ne₂) cs
      | .var _, .const n₂ us₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction n₂ us₂ with
            | some v₂ => (VTm.neutral ne₁).defEq (← applySpine sp₂ v₂) .full
            | none => etaDefEq ne₂ (.neutral ne₁) cs

partial def Spine.defEq {n} : Spine n → Spine n → ConvState → ElabM Bool
  | .nil, .nil, _ => return true
  | .app sp₁ t₁, .app sp₂ t₂, cs => return (← t₁.defEq t₂ cs) && (← sp₁.defEq sp₂ cs)
  | .proj sp₁ i₁, .proj sp₂ i₂, cs => return i₁ == i₂ && (← sp₁.defEq sp₂ cs)
  | _, _, _ => return false

end

public partial def VTy.defEq {n} (a b : VTy n) (cs : ConvState := .rigid) : ElabM Bool :=
  match a, b with
  | .u i₁, .u i₂ => return i₁ == i₂
  | .pi _ a₁ ⟨env₁, b₁⟩, .pi _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.defEq a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval (env₁.weaken.cons var)
      let b₂Val ← b₂.eval (env₂.weaken.cons var)
      b₁Val.defEq b₂Val cs
  | .el n₁, .el n₂ => n₁.defEq n₂ cs
  | _, _ => return false

end Qdt
