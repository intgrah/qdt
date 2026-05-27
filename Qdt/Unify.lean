module

public import Qdt.Quote
public import Qdt.Theory.Universe.Solve

public section

namespace Qdt

open Lean (Name)

variable (q₀ : Key)

private def liftRen {n m : Nat} (r : Idx n → Option (Idx m)) :
    Idx (n + 1) → Option (Idx (m + 1))
  | ⟨0, _⟩ => some 0
  | ⟨k + 1, _⟩ => return (← r ⟨k, by omega⟩).succ

mutual
partial def Ty.rename {n m : Nat} (r : Idx n → Option (Idx m)) : Ty n → Option (Ty m)
  | .u u => return .u u
  | .pi x dom cod => return .pi x (← dom.rename r) (← cod.rename (liftRen r))
  | .el t => return .el (← t.rename r)

partial def Tm.rename {n m : Nat} (r : Idx n → Option (Idx m)) : Tm n → Option (Tm m)
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
partial def Ty.containsMeta {n} (id : MVarId) : Ty n → Bool
  | .u _ => false
  | .pi _ a b => a.containsMeta id || b.containsMeta id
  | .el t => t.containsMeta id

partial def Tm.containsMeta {n} (id : MVarId) : Tm n → Bool
  | .u' _ | .var _ | .const _ _ => false
  | .lam _ ty body => ty.containsMeta id || body.containsMeta id
  | .app f a => f.containsMeta id || a.containsMeta id
  | .pi' _ a b => a.containsMeta id || b.containsMeta id
  | .proj _ t => t.containsMeta id
  | .letE _ ty rhs body =>
      ty.containsMeta id || rhs.containsMeta id || body.containsMeta id
  | .mvar id' => id == id'
end

def MetaInfo.freshType {a : Nat} (ctxNames : List Name) (ctx : Ctx 0 a) :
    ElabM q₀ (Ty a) := do
  let univ ← Universe.freshUMVar q₀
  let id ← freshMetaId q₀ {
    arity := a
    ctx
    ty := .u (.mvar univ),
    ctxNames
    path := (← read).path, decl := (← read).currentDecl,
  }
  return .el (Tm.apps (.mvar id) ((List.finRange a).map (Tm.var ·.rev)))

mutual

def Ty.takePisOrFresh {a : Nat} (ctxNames : List Name) (ctx : Ctx 0 a) :
    (extra : Nat) → Ty a → ElabM q₀ (Ctx a (a + extra))
  | 0, _ => return .nil
  | k + 1, .pi name dom body => do
      let inner ← body.takePisOrFresh (name :: ctxNames) (ctx.snoc (name, dom)) k
      have : a + 1 + k = a + (k + 1) := by omega
      return this ▸ ((Tele.nil.snoc (name, dom) : Ctx a (a + 1)).append inner)
  | k + 1, _ => allFresh ctxNames ctx (k + 1)

def allFresh {a : Nat} (ctxNames : List Name) (ctx : Ctx 0 a) :
    (extra : Nat) → ElabM q₀ (Ctx a (a + extra))
  | 0 => return .nil
  | k + 1 => do
      let dom ← MetaInfo.freshType q₀ ctxNames ctx
      let inner ← allFresh (.anonymous :: ctxNames) (ctx.snoc (.anonymous, dom)) k
      have : a + 1 + k = a + (k + 1) := by omega
      return this ▸ ((Tele.nil.snoc (.anonymous, dom) : Ctx a (a + 1)).append inner)

end

def MetaInfo.wrap (info : MetaInfo) {numArgs : Nat} (body : Tm numArgs) :
    ElabM q₀ (Tm info.arity) := do
  if h : info.arity ≤ numArgs then
    have : info.arity + (numArgs - info.arity) = numArgs := by omega
    return Tm.lams (this ▸ (← info.ty.takePisOrFresh q₀ info.ctxNames info.ctx (numArgs - info.arity))) body
  else
    panic! "MetaInfo.wrap: numArgs ({numArgs}) < arity ({info.arity})"

partial def Spine.patternPrefix {n} : List (VTm n) → List (Lvl n)
  | [] => []
  | .neutral ⟨.var lvl, .nil⟩ :: rest =>
      let inner := Spine.patternPrefix rest
      if lvl ∈ inner then [] else lvl :: inner
  | _ => []

partial def MetaInfo.solve {n} (info : MetaInfo) (id : MVarId) (sp : Spine n) (rhs : VTm n) :
    ElabM q₀ (Option (Tm info.arity)) := do
  let some args := sp.toAppList | return none
  let rhs ← rhs.quote q₀
  let entries : List (Nat × Idx args.length) :=
    Spine.patternPrefix args |>.zip (List.finRange args.length) |>.map fun (lvl, i) =>
      (lvl.rev, i.rev)
  let rename (r : Idx n → Option (Idx args.length)) : Option (Tm args.length) :=
    rhs.rename r |>.filter (!·.containsMeta id)
  let body := rename (entries.lookup ·.val) <|> rename (fun _ => none)
  body.mapM (info.wrap q₀)

end Qdt
