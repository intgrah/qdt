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

def Ctx.lookupTy : {n : Nat} → Idx n → Ctx 0 n → Ty n
  | _ + 1, ⟨0, _⟩, .snoc _ ⟨_, _, ty⟩ => ty.shiftAfter 0 1
  | _ + 1, ⟨i + 1, h⟩, .snoc rest _ =>
      (Ctx.lookupTy ⟨i, by omega⟩ rest).shiftAfter 0 1

partial def Tm.inferTy {a : Nat} (q₀ : Key) (paramCtx : Ctx 0 a) : Tm a →
    ElabM q₀ (Option (Ty a))
  | .var i => return some (paramCtx.lookupTy i)
  | .u' u => return some (.u u.mkSucc)
  | .const c us => do
      let some info ← fetchConstantInfo q₀ c | return none
      if info.numUnivParams != us.length then return none
      return some (info.ty.instantiateParams info.univParams us).wkClosed
  | .app f arg => do
      let some fTy ← Tm.inferTy q₀ paramCtx f | return none
      let .pi _ _ _ body := fTy | return none
      return some (body.subst (Subst.beta arg))
  | .lam name bi ty body => do
      let some bodyTy ← Tm.inferTy q₀ (paramCtx.snoc (name, bi, ty)) body | return none
      return some (.pi name bi ty bodyTy)
  | .pi' name bi dom cod => do
      let some domTy ← Tm.inferTy q₀ paramCtx dom | return none
      let .u uA := domTy | return none
      let some codTy ← Tm.inferTy q₀ (paramCtx.snoc (name, bi, .el dom)) cod | return none
      let .u uB := codTy | return none
      return some (.u (uA.mkMax uB))
  | .letE name ty rhs body => do
      let some bodyTy ← Tm.inferTy q₀ (paramCtx.snoc (name, .explicit, ty)) body | return none
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
      let ctorTy : Ty a := (ctorInfo.ty.instantiateParams ctorInfo.univParams us).wkClosed
      let applied := List.range i |>.foldl (fun ty j => ty.bind (·.applyArg (.proj j t)))
                       (structArgs.foldl (fun ty arg => ty.bind (·.applyArg arg)) (some ctorTy))
      return applied.bind fun
        | .pi _ _ fieldTy _ => some fieldTy
        | _ => none
  | .mvar id => do
      let info ← getMetaInfo q₀ id
      return some (Ty.pis info.ctx info.ty).wkClosed

def Ty.resultUniverseAfter {a : Nat} (n : Nat) (ty : Ty a) : Option Universe :=
  match n, ty with
  | 0, .u lvl => some lvl
  | n + 1, .pi _ _ _ cod => Ty.resultUniverseAfter n cod
  | _, _ => none

partial def Tm.typeUniverse? {a : Nat} (q₀ : Key) (paramCtx : Ctx 0 a) (t : Tm a) :
    ElabM q₀ (Option Universe) := do
  let (head, args) := t.splitApps
  let n := args.length
  match head with
  | .u' u => if n == 0 then return some u.mkSucc else return none
  | .pi' name bi dom cod =>
      if n != 0 then return none
      let some uA ← Tm.typeUniverse? q₀ paramCtx dom | return none
      let some uB ← Tm.typeUniverse? q₀ (paramCtx.snoc (name, bi, .el dom)) cod | return none
      return some (uA.mkMax uB)
  | .var i => return Ty.resultUniverseAfter n (paramCtx.lookupTy i)
  | .const c us =>
      let some info ← fetchConstantInfo q₀ c | return none
      if info.numUnivParams != us.length then return none
      let ty : Ty a := (info.ty.instantiateParams info.univParams us).wkClosed
      return Ty.resultUniverseAfter n ty
  | .mvar id =>
      let info ← getMetaInfo q₀ id
      let ty : Ty a := (Ty.pis info.ctx info.ty).wkClosed
      return Ty.resultUniverseAfter n ty
  | _ =>
      match ← Tm.inferTy q₀ paramCtx t with
      | some (.u u) => return some u
      | _ => return none

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
        (← a.whnf q₀).conv cctx (← b.whnf q₀) .rigid
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
  | .lam name _ aTy ⟨env₁, body₁⟩, .lam _ _ _ ⟨env₂, body₂⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let b₁Val ← body₁.eval q₀ (env₁.weaken.cons var)
      let b₂Val ← body₂.eval q₀ (env₂.weaken.cons var)
      b₁Val.conv (cctx.snoc (.bound name aTy)) b₂Val cs
  | .lam name _ aTy ⟨env, body⟩, other => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          bVal.conv (cctx.snoc (.bound name aTy)) oVal cs
      | _ => return false
  | other, .lam name _ aTy ⟨env, body⟩ => do
      let var : VTm (n + 1) := VTm.varAt n
      let bVal ← body.eval q₀ (env.weaken.cons var)
      match other.weaken (m := n + 1) with
      | .neutral ne =>
          let oVal ← (VTm.neutral ne).app q₀ var
          oVal.conv (cctx.snoc (.bound name aTy)) bVal cs
      | _ => return false
  | .pi' name _ a₁ ⟨env₁, b₁⟩, .pi' _ _ a₂ ⟨env₂, b₂⟩ => do
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
          if !(← spLast.conv cctx lastArg .flex) then return false
          VTm.conv cctx (.neutral ⟨.mvar id, spRest⟩) (.neutral ⟨rhsHead, sp'⟩) cs
      | _ => return false
  | .glued ⟨rhsHead, .app sp' lastArg⟩ _ =>
      match sp with
      | .app spRest spLast =>
          if !(← spLast.conv cctx lastArg .flex) then return false
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
                    (← applySpine q₀ sp₁ v₁).conv cctx (← applySpine q₀ sp₂ v₁) .rigid
                | none => sp₁.conv cctx sp₂ .rigid
            | _ => sp₁.conv cctx sp₂ cs
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← deltaReduction q₀ n₁ us₁, ← deltaReduction q₀ n₂ us₂ with
              | some v₁, some v₂ =>
                  (← applySpine q₀ sp₁ v₁).conv cctx (← applySpine q₀ sp₂ v₂) .rigid
              | some v₁, none =>
                  (← applySpine q₀ sp₁ v₁).conv cctx (.neutral ne₂) .rigid
              | none, some v₂ =>
                  (VTm.neutral ne₁).conv cctx (← applySpine q₀ sp₂ v₂) .rigid
              | none, none =>
                  return (← etaConv cctx ne₁ (.neutral ne₂) cs)
                    || (← etaConv cctx ne₂ (.neutral ne₁) cs)
      | .const n₁ us₁, .var _ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₁ us₁ with
            | some v₁ => (← applySpine q₀ sp₁ v₁).conv cctx (.neutral ne₂) .rigid
            | none => etaConv cctx ne₁ (.neutral ne₂) cs
      | .var _, .const n₂ us₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← deltaReduction q₀ n₂ us₂ with
            | some v₂ => (VTm.neutral ne₁).conv cctx (← applySpine q₀ sp₂ v₂) .rigid
            | none => etaConv cctx ne₂ (.neutral ne₁) cs
      | .mvar i₁, .mvar i₂ =>
          if i₁ == i₂ then
            match cs with
            | .flex => sp₁.conv cctx sp₂ cs
            | _ =>
              if ← sp₁.conv cctx sp₂ .flex then return true
              match ← metaReduction q₀ i₁ sp₁, ← metaReduction q₀ i₁ sp₂ with
              | some v₁, some v₂ => v₁.conv cctx v₂ .rigid
              | _, _ => sp₁.conv cctx sp₂ .rigid
          else
            match cs with
            | .flex => return false
            | _ =>
              match ← metaReduction q₀ i₁ sp₁, ← metaReduction q₀ i₂ sp₂ with
              | some v₁, some v₂ => v₁.conv cctx v₂ .rigid
              | some v₁, none => v₁.conv cctx (.neutral ne₂) .rigid
              | none, some v₂ => (VTm.neutral ne₁).conv cctx v₂ .rigid
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
            | some v₁ => v₁.conv cctx (.neutral ne₂) .rigid
            | none =>
              if ← solveMVarChecked i₁ cctx sp₁ (.neutral ne₂) then return true
              solveMVarFOApprox i₁ cctx sp₁ (.neutral ne₂) cs
      | _, .mvar i₂ =>
          match cs with
          | .flex => return false
          | _ =>
            match ← metaReduction q₀ i₂ sp₂ with
            | some v₂ => (VTm.neutral ne₁).conv cctx v₂ .rigid
            | none =>
              if ← solveMVarChecked i₂ cctx sp₂ (.neutral ne₁) then return true
              solveMVarFOApprox i₂ cctx sp₂ (.neutral ne₁) cs

partial def Spine.conv {n} (cctx : VCtx n) :
    Spine n → Spine n → ConvState → ElabM q₀ Bool
  | .nil, .nil, _ => return true
  | .app sp₁ t₁, .app sp₂ t₂, cs => do
      if ← sp₁.conv cctx sp₂ cs then t₁.conv cctx t₂ cs else return false
  | .proj sp₁ i₁, .proj sp₂ i₂, cs =>
      if i₁ == i₂ then sp₁.conv cctx sp₂ cs else return false
  | _, _, _ => return false

public partial def VTy.conv {n} (cctx : VCtx n) (a b : VTy n) (cs : ConvState := .rigid) :
    ElabM q₀ Bool :=
  match a, b with
  | .u i₁, .u i₂ => Universe.solveUEq q₀ i₁ i₂
  | .pi name _ a₁ ⟨env₁, b₁⟩, .pi _ _ a₂ ⟨env₂, b₂⟩ => do
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

partial def stripTrailingMatch {n} (cctx : VCtx n) :
    Nat → Spine n → VTm n → ElabM q₀ (Option (Spine n × VTm n))
  | 0, sp, rhs => return some (sp, rhs)
  | k + 1, .app spRest spLast, .neutral ⟨h, .app rhsRest rhsLast⟩ => do
      if ← spLast.conv cctx rhsLast then
        stripTrailingMatch cctx k spRest (.neutral ⟨h, rhsRest⟩)
      else return none
  | _, _, _ => return none

partial def solveMVarChecked {n} (id : MVarId) (cctx : VCtx n) (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ Bool := do
  let info ← getMetaInfo q₀ id
  let normalizedTy ←
    match info.tyNorm with
    | some t => pure t
    | none => do
        let t ← (← info.ty.eval q₀ (Env.identity info.arity)).quote q₀
        unless info.ty.hasMeta do setMetaTyNorm q₀ info id t
        pure t
  let infoNorm : MetaInfo := { info with ty := normalizedTy }
  let (sp, rhs) ←
    match sp.toAppList with
    | some args =>
        let nNonpat := args.length - (Spine.patternPrefix args).length
        if nNonpat == 0 then pure (sp, rhs)
        else
          let saved ← get
          match ← stripTrailingMatch cctx nNonpat sp rhs with
          | some res => pure res
          | none => do set saved; pure (sp, rhs)
    | none => pure (sp, rhs)
  let some soln ← infoNorm.solve q₀ id cctx sp rhs | return false
  if let some codU := normalizedTy.getResultUniverse? then
    if let some bodyU ← Tm.typeUniverse? q₀ info.ctx soln then
      unless ← Universe.solveUEq q₀ codU bodyU do return false
  assignMeta q₀ infoNorm id soln
  return true

end

def VTm.convSpec {n} (cctx : VCtx n) (a b : VTm n) : ElabM q₀ Bool := do
  let s ← get
  let r ← VTm.conv q₀ cctx a b
  set s
  return r

def Ty.toTm {n} : Ty n → Tm n
  | .u lv => .u' lv
  | .pi nm bi dom cod => .pi' nm bi dom.toTm cod.toTm
  | .el t => t

mutual

partial def Ty.replaceConv {m} (tctx : TermContext m) (target rep : Tm m) : Ty m → ElabM q₀ (Ty m)
  | .u lv => return .u lv
  | .pi nm bi dom cod => do
      let dom' ← Ty.replaceConv tctx target rep dom
      let tctx' ← tctx.bindV q₀ nm (← dom.eval q₀ tctx.env)
      let cod' ← Ty.replaceConv tctx' target.weaken rep.weaken cod
      return .pi nm bi dom' cod'
  | .el t => return .el (← Tm.replaceConv tctx target rep t)

partial def Tm.replaceConv {m} (tctx : TermContext m) (target rep : Tm m) (t : Tm m) :
    ElabM q₀ (Tm m) := do
  if (← VTm.convSpec q₀ tctx.ctx (← t.eval q₀ tctx.env) (← target.eval q₀ tctx.env)) then
    return rep
  match t with
  | .u' lv => return .u' lv
  | .var i => return .var i
  | .const nm us => return .const nm us
  | .mvar id => return .mvar id
  | .app f a => return .app (← Tm.replaceConv tctx target rep f) (← Tm.replaceConv tctx target rep a)
  | .proj k s => return .proj k (← Tm.replaceConv tctx target rep s)
  | .lam nm bi ty body => do
      let ty' ← Ty.replaceConv tctx target rep ty
      let tctx' ← tctx.bindV q₀ nm (← ty.eval q₀ tctx.env)
      let body' ← Tm.replaceConv tctx' target.weaken rep.weaken body
      return .lam nm bi ty' body'
  | .pi' nm bi a b => do
      let a' ← Tm.replaceConv tctx target rep a
      let tctx' ← tctx.bindV q₀ nm (← (Ty.el a).eval q₀ tctx.env)
      let b' ← Tm.replaceConv tctx' target.weaken rep.weaken b
      return .pi' nm bi a' b'
  | .letE nm ty rhs body => do
      let ty' ← Ty.replaceConv tctx target rep ty
      let rhs' ← Tm.replaceConv tctx target rep rhs
      let tctx' ← tctx.defineV q₀ nm (← ty.eval q₀ tctx.env) (← rhs.eval q₀ tctx.env)
      let body' ← Tm.replaceConv tctx' target.weaken rep.weaken body
      return .letE nm ty' rhs' body'

end

def Ty.kabstract {n} (tctx : TermContext n) (name : Lean.Name) (discrTy : VTy n) (discr : Tm n)
    (T : Ty n) : ElabM q₀ (Ty (n + 1)) := do
  let tctx' ← tctx.bindV q₀ name discrTy
  Ty.replaceConv q₀ tctx' discr.weaken (.var ⟨0, by omega⟩) T.weaken

def Tm.kabstract {n} (tctx : TermContext n) (name : Lean.Name) (discrTy : VTy n) (discr : Tm n)
    (t : Tm n) : ElabM q₀ (Tm (n + 1)) := do
  let tctx' ← tctx.bindV q₀ name discrTy
  Tm.replaceConv q₀ tctx' discr.weaken (.var ⟨0, by omega⟩) t.weaken

end Qdt
