module

public import Qdt.Nbe

namespace Qdt

variable (q₀ : Key)

mutual

public partial def VTy.quote {n} : VTy n → ElabM q₀ (Ty n)
  | .u i => return .u i
  | .pi x bi a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi x bi a b
  | .el n => return .el (← n.quote)

public partial def VTm.quote {n} : VTm n → ElabM q₀ (Tm n)
  | .u' i => return .u' i
  | .neutral n => n.quote
  | .lam x bi a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .lam x bi a b
  | .pi' x bi a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi' x bi a b
  | .glued ne _ => ne.quote

partial def Head.quote {n} : Head n → ElabM q₀ (Tm n)
  | .var i => return .var i.rev
  | .const name us => return .const name us
  | .mvar id => return .mvar id

partial def Neutral.quote {n} (ne : Neutral n) : ElabM q₀ (Tm n) := do
  let ⟨h, sp⟩ := ne
  let rec go : Spine n → ElabM q₀ (Tm n)
    | .nil => h.quote
    | .app sp t => return .app (← go sp) (← t.quote)
    | .proj sp i => return .proj i (← go sp)
  go sp

public partial def VTy.reify {n} : VTy n → ElabM q₀ (Tm n)
  | .u i => return .u' i
  | .pi x bi a ⟨env, b⟩ => do
      let a ← a.reify
      let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.reify
      return .pi' x bi a b
  | .el n => n.quote

public partial def VTy.inferLevel {n} (ctx : VCtx n) : VTy n → ElabM q₀ Universe
  | .u i => return i.mkSucc
  | .pi _x _ a ⟨env, b⟩ => do
      let aLevel ← a.inferLevel ctx
      let bVal : VTy (n + 1) ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
      let bLevel ← bVal.inferLevel (ctx.snoc (.bound .anonymous a))
      return aLevel.mkMax bLevel
  | .el ⟨.const name us, _sp⟩ => do
      let some info ← fetchConstantInfo q₀ name
        | panic! s!"inferLevel: unknown constant {name}"
      let ty := info.ty.instantiateParams info.univParams us
      let some u := ty.getResultUniverse?
        | panic! s!"inferLevel: could not determine universe for {name}"
      return u
  | .el ⟨.var lvl, _sp⟩ => do
      let .u u := ctx.lookup lvl.rev
        | panic! "inferLevel: could not determine universe"
      return u
  | .el ⟨.mvar _id, _sp⟩ => do
      panic! "inferLevel: encountered unsolved metavariable in type"

end

public def TermContext.bindV {n} (tctx : TermContext n) (name : Lean.Name) (ty : VTy n) :
    ElabM q₀ (TermContext (n + 1)) := do
  let tyInner : Ty tctx.view.arity := (← ty.quote q₀).subst tctx.view.subst
  return tctx.bind name ty tyInner

public def TermContext.defineV {n} (tctx : TermContext n) (name : Lean.Name) (ty : VTy n) (value : VTm n) :
    ElabM q₀ (TermContext (n + 1)) := do
  let valueInner : Tm tctx.view.arity := (← value.quote q₀).subst tctx.view.subst
  return tctx.define name ty value valueInner

end Qdt
