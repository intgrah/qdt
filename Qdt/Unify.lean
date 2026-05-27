module

public import Qdt.Quote

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
  | .pi x dom cod => return .pi x (← dom.rename r) (← cod.rename (liftRen r))
  | .el t => return .el (← t.rename r)

def Tm.rename {n m : Nat} (r : Idx n → Option (Idx m)) : Tm n → Option (Tm m)
  | .u' u => return .u' u
  | .var i => return .var (← r i)
  | .const c us => return .const c us
  | .lam x ty body => return .lam x (← ty.rename r) (← body.rename (liftRen r))
  | .app f a => return .app (← f.rename r) (← a.rename r)
  | .pi' x a b => return .pi' x (← a.rename r) (← b.rename (liftRen r))
  | .proj i t => return .proj i (← t.rename r)
  | .letE x ty rhs body =>
      return .letE x (← ty.rename r) (← rhs.rename r) (← body.rename (liftRen r))
  | .mvar id => return .mvar id
end

mutual
def Ty.containsMeta {n} (id : MVarId) : Ty n → Bool
  | .u _ => false
  | .pi _ a b => a.containsMeta id || b.containsMeta id
  | .el t => t.containsMeta id

def Tm.containsMeta {n} (id : MVarId) : Tm n → Bool
  | .u' _ | .var _ | .const _ _ => false
  | .lam _ ty body => ty.containsMeta id || body.containsMeta id
  | .app f a => f.containsMeta id || a.containsMeta id
  | .pi' _ a b => a.containsMeta id || b.containsMeta id
  | .proj _ t => t.containsMeta id
  | .letE _ ty rhs body =>
      ty.containsMeta id || rhs.containsMeta id || body.containsMeta id
  | .mvar id' => id == id'
end

def Spine.patternPrefix {n} : List (VTm n) → List (Lvl n)
  | [] => []
  | .neutral ⟨.var lvl, .nil⟩ :: rest =>
      let inner := Spine.patternPrefix rest
      if lvl ∈ inner then [] else lvl :: inner
  | _ => []

def Ty.takePis {a : Nat} : (extra : Nat) → Ty a → Option (Ctx a (a + extra))
  | 0, _ => some .nil
  | k + 1, .pi name dom body => do
      let inner ← body.takePis k
      have : a + 1 + k = a + (k + 1) := by omega
      return this ▸ ((Tele.nil.snoc (name, dom) : Ctx a (a + 1)).append inner)
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
        go (i + 1) (by omega) (acc.snoc (name, ty))
    termination_by args.length - (info.arity + i)
    go 0 hLe Tele.nil
  else
    return none

partial def MetaInfo.solve {n} (info : MetaInfo) (id : MVarId) (cctx : VCtx n)
    (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ (Option (Tm info.arity)) := do
  let some args := sp.toAppList | return none
  let rhs ← rhs.quote q₀
  let patPrefix := Spine.patternPrefix args
  let entries : List (Nat × Idx args.length) :=
    patPrefix.zip (List.finRange args.length) |>.map fun (lvl, i) => (lvl.rev, i.rev)
  let some body := rhs.rename (entries.lookup ·.val) |>.filter (!·.containsMeta id)
    | return none
  let hintTele ← computeHintTele q₀ info cctx args patPrefix
  return info.wrap body hintTele

end Qdt
