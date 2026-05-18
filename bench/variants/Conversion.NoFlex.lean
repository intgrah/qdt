module

public import Qdt.Nbe

public section

namespace Qdt

variable (q₀ : Key)

inductive ConvState where
  | rigid
  | flex
  | full

mutual

public partial def VTm.conv {n} (a b : VTm n) (cs : ConvState := .rigid) : ElabM q₀ Bool :=
  match a, b with
  | .u' i₁, .u' i₂ => return i₁ == i₂
  | .glued ne₁ _ _, .glued ne₂ _ _ => do
      match cs with
      | .flex => ne₁.conv ne₂ cs
      | .rigid => (← a.whnf q₀).conv (← b.whnf q₀) .full
      | .full => (← a.whnf q₀).conv (← b.whnf q₀) cs


  | .glued _ _ _, other => do (← a.whnf q₀).conv other cs
  | other, .glued _ _ _ => do other.conv (← b.whnf q₀) cs
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
      | .neutral _ => return false
      | v => v.conv other cs
  | other, .neutral ne => do
      match ← (VTm.neutral ne).whnf q₀ with
      | .neutral _ => return false
      | v => other.conv v cs
  | _, _ => return false

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
          if n₁ == n₂ && us₁ == us₂ then
            match cs with
            | .rigid =>
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

partial def Spine.conv {n} : Spine n → Spine n → ConvState → ElabM q₀ Bool
  | .nil, .nil, _ => return true
  | .app sp₁ t₁, .app sp₂ t₂, cs => return (← t₁.conv t₂ cs) && (← sp₁.conv sp₂ cs)
  | .proj sp₁ i₁, .proj sp₂ i₂, cs => return i₁ == i₂ && (← sp₁.conv sp₂ cs)
  | _, _, _ => return false

end

public partial def VTy.conv {n} (a b : VTy n) (cs : ConvState := .rigid) : ElabM q₀ Bool :=
  match a, b with
  | .u i₁, .u i₂ => return i₁ == i₂
  | .pi _ a₁ ⟨env₁, b₁⟩, .pi _ a₂ ⟨env₂, b₂⟩ => do
      if !(← a₁.conv a₂ cs) then return false
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← b₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← b₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv b₂Val cs
  | .el n₁, .el n₂ => n₁.conv q₀ n₂ cs
  | _, _ => return false

end Qdt
