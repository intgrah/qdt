module

public import Qdt.Quote
public import Qdt.Theory.Substitution.Basic

public section

namespace Qdt

open Lean (Name)

variable (q₀ : Key)

private def liftRen {n m : Nat} (r : Idx n → Option (Idx m)) :
    Idx (n + 1) → Option (Idx (m + 1))
  | ⟨0, _⟩ => some 0
  | ⟨k + 1, _⟩ => return (← r ⟨k, by omega⟩).succ

mutual
def Ty.rename {n m : Nat} (r : Idx n → Option (Idx m)) : Ty n → Option (Ty m)
  | .u u => return .u u
  | .pi x bi dom cod => return .pi x bi (← dom.rename r) (← cod.rename (liftRen r))
  | .el t => return .el (← t.rename r)

def Tm.rename {n m : Nat} (r : Idx n → Option (Idx m)) : Tm n → Option (Tm m)
  | .u' u => return .u' u
  | .var i => return .var (← r i)
  | .const c us => return .const c us
  | .lam x bi ty body => return .lam x bi (← ty.rename r) (← body.rename (liftRen r))
  | .app f a => return .app (← f.rename r) (← a.rename r)
  | .pi' x bi a b => return .pi' x bi (← a.rename r) (← b.rename (liftRen r))
  | .proj i t => return .proj i (← t.rename r)
  | .letE x ty rhs body =>
      return .letE x (← ty.rename r) (← rhs.rename r) (← body.rename (liftRen r))
  | .mvar id => return .mvar id
end

mutual
def Ty.containsMeta {n} (id : MVarId) : Ty n → Bool
  | .u _ => false
  | .pi _ _ a b => a.containsMeta id || b.containsMeta id
  | .el t => t.containsMeta id

def Tm.containsMeta {n} (id : MVarId) : Tm n → Bool
  | .u' _ | .var _ | .const _ _ => false
  | .lam _ _ ty body => ty.containsMeta id || body.containsMeta id
  | .app f a => f.containsMeta id || a.containsMeta id
  | .pi' _ _ a b => a.containsMeta id || b.containsMeta id
  | .proj _ t => t.containsMeta id
  | .letE _ ty rhs body =>
      ty.containsMeta id || rhs.containsMeta id || body.containsMeta id
  | .mvar id' => id == id'
end

mutual
def Ty.hasMeta {n} : Ty n → Bool
  | .u _ => false
  | .pi _ _ a b => a.hasMeta || b.hasMeta
  | .el t => t.hasMeta

def Tm.hasMeta {n} : Tm n → Bool
  | .u' _ | .var _ | .const _ _ => false
  | .lam _ _ ty body => ty.hasMeta || body.hasMeta
  | .app f a => f.hasMeta || a.hasMeta
  | .pi' _ _ a b => a.hasMeta || b.hasMeta
  | .proj _ t => t.hasMeta
  | .letE _ ty rhs body => ty.hasMeta || rhs.hasMeta || body.hasMeta
  | .mvar _ => true
end

def Spine.patternPrefix {n} : List (VTm n) → List (Lvl n)
  | [] => []
  | .neutral ⟨.var lvl, .nil⟩ :: rest =>
      let inner := Spine.patternPrefix rest
      if lvl ∈ inner then [] else lvl :: inner
  | _ => []

def Ty.takePis {a : Nat} : (extra : Nat) → Ty a → Option (Ctx a (a + extra))
  | 0, _ => some .nil
  | k + 1, .pi name bi dom body => do
      let inner ← body.takePis k
      have : a + 1 + k = a + (k + 1) := by omega
      return this ▸ ((Tele.nil.snoc (name, bi, dom) : Ctx a (a + 1)).append inner)
  | _ + 1, _ => none

def MetaInfo.wrap (info : MetaInfo) {numArgs : Nat} (body : Tm numArgs)
    (hintTele : Option (Ctx info.arity numArgs) := none) :
    Option (Tm info.arity) := do
  if let some tele := hintTele then
    return Tm.lams tele body
  if h : info.arity ≤ numArgs then
    have : info.arity + (numArgs - info.arity) = numArgs := by omega
    return Tm.lams (this ▸ (← info.ty.takePis (numArgs - info.arity))) body
  none

def computeHintTele {n} (info : MetaInfo) (cctx : VCtx n) (args : List (VTm n))
    (patPrefix : List (Lvl n)) :
    ElabM q₀ (Option (Ctx info.arity args.length)) := do
  if hLe : info.arity ≤ args.length then
    let entries : List (Nat × Nat) :=
      patPrefix.zipIdx.map fun (lvl, pos) => (lvl.rev.val, pos)
    let rec go (i : Nat) (hLe' : info.arity + i ≤ args.length)
        (acc : Ctx info.arity (info.arity + i)) :
        ElabM q₀ (Option (Ctx info.arity args.length)) := do
      if hStop : info.arity + i = args.length then
        return some (hStop ▸ acc)
      else
        have hIdx : info.arity + i < args.length := by omega
        let .neutral ⟨.var lvl, .nil⟩ := args[info.arity + i] | return none
        let (name, vty) := cctx.lookupByLevel lvl
        let tyQ ← vty.quote q₀
        let some ty := tyQ.rename fun idx => do
            let pos ← entries.lookup idx.val
            if h : pos < info.arity + i then some (Fin.rev ⟨pos, h⟩) else none
          | return none
        go (i + 1) (by omega) (acc.snoc (name, .explicit, ty))
    termination_by args.length - (info.arity + i)
    go 0 hLe Tele.nil
  else
    return none

def pruneCtx (dropDB : Nat → Bool) :
    {b : Nat} → (depth : Nat) → Ctx 0 b →
    Σ k, Ctx 0 k × (Idx b → Option (Idx k))
  | 0, _, .nil => ⟨0, .nil, fun i => absurd i.isLt (Nat.not_lt_zero _)⟩
  | b + 1, depth, .snoc ts (name, bi, ty) =>
      let ⟨k, ctx', renTs⟩ := pruneCtx dropDB (depth + 1) ts
      match (if dropDB depth then none else ty.rename renTs) with
      | none =>
          ⟨k, ctx', fun i =>
            if h : 0 < i.val then renTs ⟨i.val - 1, by omega⟩ else none⟩
      | some ty' =>
          ⟨k + 1, ctx'.snoc (name, bi, ty'), fun i =>
            if h : 0 < i.val then (renTs ⟨i.val - 1, by omega⟩).map (·.succ)
            else some ⟨0, Nat.zero_lt_succ _⟩⟩

def prunePositions (mid : MVarId) (dropDB : Nat → Bool) : ElabM q₀ Bool := do
  let info ← getMetaInfo q₀ mid
  if info.solution.isSome then return false
  let ⟨newArity, ctx', ren⟩ := pruneCtx dropDB 0 info.ctx
  if newArity == info.arity then return false
  let some tyKept := info.ty.rename ren | return false
  let newInfo : MetaInfo :=
    { info with arity := newArity, ctx := ctx', ty := tyKept, solution := none, tyNorm := none }
  let newId ← freshMetaId q₀ newInfo
  let keptPairs : List (Nat × Tm info.arity) :=
    (List.finRange info.arity).filterMap fun d =>
      (ren d).map (fun newIdx => (newIdx.val, Tm.var d))
  let keptArgs : List (Tm info.arity) := (keptPairs.mergeSort (·.1 ≥ ·.1)).map (·.2)
  let body : Tm info.arity := Tm.apps (.mvar newId) keptArgs
  assignMeta q₀ info mid body
  return true

def Tm.isPatternVar {n} : Tm n → Bool
  | .var _ => true
  | _ => false

partial def Tm.headBeta {n} : Tm n → Tm n
  | .app f a =>
      let f := f.headBeta
      match f with
      | .lam _ _ _ body => (body.subst (Subst.beta a)).headBeta
      | f => .app f a
  | t => t

mutual
partial def Ty.instMetas {n} (t : Ty n) : ElabM q₀ (Ty n) := do
  match t with
  | .u u => return .u u
  | .pi x bi dom cod => return .pi x bi (← dom.instMetas) (← cod.instMetas)
  | .el t => return .el (← t.instMetas)

partial def Tm.instMetas {n} (t : Tm n) : ElabM q₀ (Tm n) := do
  match t with
  | .u' u => return .u' u
  | .var i => return .var i
  | .const c us => return .const c us
  | .lam x bi ty body => return .lam x bi (← ty.instMetas) (← body.instMetas)
  | .pi' x bi a b => return .pi' x bi (← a.instMetas) (← b.instMetas)
  | .proj i s => return .proj i (← s.instMetas)
  | .letE x ty rhs body => return .letE x (← ty.instMetas) (← rhs.instMetas) (← body.instMetas)
  | .mvar id => instMVarApp id []
  | t@(.app _ _) =>
      let (head, args) := t.splitApps
      let args ← args.mapM (·.instMetas)
      match head with
      | .mvar id => instMVarApp id args
      | other => return Tm.apps other args

partial def instMVarApp {n} (id : MVarId) (args : List (Tm n)) : ElabM q₀ (Tm n) := do
  let info ← getMetaInfo q₀ id
  let some body := info.solution | return Tm.apps (.mvar id) args
  let firstA := args.take info.arity
  if h : firstA.length = info.arity then
    let body ←
      if info.groundSolution then pure body
      else do
        let b ← Tm.instMetas body
        compressMetaSolution q₀ info id b (!b.hasMeta)
        pure b
    return (Tm.apps (body.subst (Subst.fromArgs firstA h)) (args.drop info.arity)).headBeta
  else
    return Tm.apps (.mvar id) args
end

def liftKeep (keep : Nat → Bool) : Nat → Bool
  | 0 => true
  | i + 1 => keep i

mutual
partial def tryPruneTy {n} (keep : Nat → Bool) (ty : Ty n) : ElabM q₀ Bool := do
  match ty with
  | .u _ => return false
  | .pi _ _ dom cod => do return (← tryPruneTy keep dom) || (← tryPruneTy (liftKeep keep) cod)
  | .el t => tryPrune keep t

partial def tryPrune {n} (keep : Nat → Bool) (t : Tm n) : ElabM q₀ Bool := do
  match t with
  | .u' _ | .var _ | .const _ _ => return false
  | .lam _ _ ty body => do
      return (← tryPruneTy keep ty) || (← tryPrune (liftKeep keep) body)
  | .pi' _ _ a b => do
      return (← tryPrune keep a) || (← tryPrune (liftKeep keep) b)
  | .proj _ s => tryPrune keep s
  | .letE _ ty rhs body => do
      return (← tryPruneTy keep ty) || (← tryPrune keep rhs)
        || (← tryPrune (liftKeep keep) body)
  | .mvar _ => tryPruneApp keep t
  | .app _ _ => tryPruneApp keep t

partial def tryPruneApp {n} (keep : Nat → Bool) (t : Tm n) : ElabM q₀ Bool := do
  let (head, tArgs) := t.splitApps
  let recurse : ElabM q₀ Bool :=
    tArgs.foldlM (fun acc a => do return acc || (← tryPrune keep a)) false
  match head with
  | .mvar mid =>
      let mi ← getMetaInfo q₀ mid
      if mi.solution.isNone ∧ tArgs.all Tm.isPatternVar ∧ tArgs.length == mi.arity then
        let dropIdxs : List Nat := (tArgs.zipIdx.filterMap fun (a, j) =>
          match a with
          | .var i => if keep i.val then none else some (mi.arity - 1 - j)
          | _ => none)
        if dropIdxs.isEmpty then recurse
        else prunePositions q₀ mid (fun d => dropIdxs.contains d)
      else recurse
  | _ => recurse
end

partial def MetaInfo.solve {n} (info : MetaInfo) (id : MVarId) (cctx : VCtx n)
    (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ (Option (Tm info.arity)) := do
  let some args := sp.toAppList | return none
  let rhsQ ← Tm.instMetas q₀ (← rhs.quote q₀)
  let patPrefix := Spine.patternPrefix args
  let entries : List (Nat × Idx args.length) :=
    patPrefix.zip (List.finRange args.length) |>.map fun (lvl, i) => (lvl.rev, i.rev)
  let keep : Nat → Bool := fun idxVal => (entries.lookup idxVal).isSome
  let rhsQ ←
    if (rhsQ.rename (entries.lookup ·.val)).isSome then pure rhsQ
    else
      let pruned ← tryPrune q₀ keep rhsQ
      if pruned then Tm.instMetas q₀ rhsQ else pure rhsQ
  let some body := rhsQ.rename (entries.lookup ·.val) |>.filter (!·.containsMeta id)
    | return none
  let hintTele ← computeHintTele q₀ info cctx args patPrefix
  let result := info.wrap body hintTele
  return result

end Qdt
