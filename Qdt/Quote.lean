module

public import Qdt.Nbe

@[expose] public section

namespace Qdt

mutual

partial def VTy.quote {n} : VTy n → ElabM (Ty n)
  | .u i => return .u i
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi ⟨x, a⟩ b
  | .el n => return .el (← n.quote)

partial def VTm.quote {n} : VTm n → ElabM (Tm n)
  | .u' i => return .u' i
  | .neutral n => n.quote
  | .lam ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .lam ⟨x, a⟩ b
  | .pi' x a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi' ⟨x, a⟩ b

partial def Head.quote {n} : Head n → ElabM (Tm n)
  | .var i => return .var i.rev
  | .const name us => return .const name us

partial def Neutral.quote {n} (ne : Neutral n) : ElabM (Tm n) := do
  let ⟨h, sp⟩ := ne
  let rec go : Spine n → ElabM (Tm n)
    | .nil => h.quote
    | .app sp t => return .app (← go sp) (← t.quote)
    | .proj sp i => return .proj i (← go sp)
  go sp

partial def VTy.reify {n} : VTy n → ElabM (Tm n)
  | .u i => return .u' i
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.reify
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.reify
      return .pi' ⟨x, a⟩ b
  | .el n => n.quote

partial def VTy.inferLevel {n} (ctx : VCtx n) : VTy n → ElabM Universe
  | .u i => return i.succ
  | .pi ⟨_x, a⟩ ⟨env, b⟩ => do
      let aLevel ← a.inferLevel ctx
      let bVal : VTy (n + 1) ← b.eval (env.weaken.cons (VTm.varAt n))
      let bLevel ← bVal.inferLevel (ctx.snoc ⟨.anonymous, a⟩)
      return Universe.max aLevel bLevel |>.normalise
  | .el ⟨.const name us, _sp⟩ => do
      let some info ← fetchConstantInfo name
        | panic! s!"inferLevel: unknown constant {name}"
      let ty := info.ty.substLevels (info.univParams.zip us)
      let some u := ty.getResultUniverse?
        | panic! s!"inferLevel: could not determine universe for {name}"
      return u.normalise
  | .el ⟨.var lvl, _sp⟩ => do
      let .u u := ctx.lookup lvl.rev
        | panic! "inferLevel: could not determine universe"
      return u.normalise

end

end Qdt
