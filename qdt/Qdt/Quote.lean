import Qdt.Control
import Qdt.MLTT.Syntax
import Qdt.Nbe

namespace Qdt

mutual

partial def VTy.quote {n} : VTy n → MetaM (Ty n)
  | .u i => return .u i
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi ⟨x, a⟩ b
  | .el n => return .el (← n.quote)

partial def VTm.quote {n} : VTm n → MetaM (Tm n)
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
      return .pi' x a b

partial def Head.quote {n} : Head n → MetaM (Tm n)
  | .var i => return .var i.rev
  | .const name us => return .const name us

partial def Neutral.quote {n} (ne : Neutral n) : MetaM (Tm n) := do
  let ⟨h, sp⟩ := ne
  let rec go : Spine n → MetaM (Tm n)
    | .nil => h.quote
    | .app sp t => return (← go sp).app (← t.quote)
    | .proj sp i => return (← go sp).proj i
  go sp

partial def VTy.reify {n} : VTy n → MetaM (Tm n)
  | .u i => return .u' i
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.reify
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.reify
      return .pi' x a b
  | .el n => n.quote

partial def VTy.inferLevel {n} (ctx : Tele VParam 0 n) : VTy n → MetaM Universe
  | .u i => return i.succ
  | .pi ⟨_x, a⟩ ⟨env, b⟩ => do
      let aLevel ← a.inferLevel ctx
      let bVal : VTy (n + 1) ← b.eval (env.weaken.cons (VTm.varAt n))
      let bLevel ← bVal.inferLevel (ctx.snoc ⟨.anonymous, a⟩)
      return .max aLevel bLevel
  | .el ⟨.const name us, _sp⟩ => do
      let some info ← fetchConstantInfo name
        | throw (.msg s!"inferLevel: unknown constant {name}")
      let ty := info.ty.substLevels (info.univParams.zip us)
      let some u := ty.getResultUniverse?
        | throw (.msg s!"inferLevel: could not determine universe for {name}")
      return u
  | .el ⟨.var lvl, _sp⟩ => do
      let .u u := ctx.lookup lvl.rev
        | throw (.msg s!"inferLevel: variable is not a universe")
      return u

end

end Qdt
