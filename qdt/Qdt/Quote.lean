import Qdt.Control
import Qdt.MLTT.Syntax
import Qdt.Nbe

namespace Qdt

mutual

partial def VTy.quote {n} : VTy n → MetaM (Ty n)
  | .u => return .u
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi ⟨x, a⟩ b
  | .el n => return .el (← n.quote)

partial def VTm.quote {n} : VTm n → MetaM (Tm n)
  | .neutral n => n.quote
  | .lam ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .lam ⟨x, a⟩ b
  | .piHat x a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .piHat x a b

partial def Head.quote {n} : Head n → MetaM (Tm n)
  | .var i => return .var i.rev
  | .const name => return .const name

partial def Neutral.quote {n} (ne : Neutral n) : MetaM (Tm n) := do
  let ⟨h, sp⟩ := ne
  let rec go : Spine n → MetaM (Tm n)
    | .nil => h.quote
    | .app sp t => return (← go sp).app (← t.quote)
    | .proj sp i => return (← go sp).proj i
  go sp

partial def VTy.reify {n} : VTy n → MetaM (Tm n)
  | .u => throw (.msg "Cannot reify Type as a term")
  | .pi ⟨x, a⟩ ⟨env, b⟩ => do
      let a ← a.reify
      let b ← b.eval (env.weaken.cons (VTm.varAt n))
      let b ← b.reify
      return .piHat x a b
  | .el n => n.quote

end

end Qdt
