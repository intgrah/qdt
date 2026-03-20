module

public import Qdt.Nbe

namespace Qdt

variable (ι₀ : ∀ i, InputV i) (q₀ : Key)

mutual

public partial def VTy.quote {n} : VTy n → ElabM ι₀ q₀ (Ty n)
  | .u i => return .u i
  | .pi x a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval ι₀ q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi x a b
  | .el n => return .el (← n.quote)

public partial def VTm.quote {n} : VTm n → ElabM ι₀ q₀ (Tm n)
  | .u' i => return .u' i
  | .neutral n => n.quote
  | .lam x a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval ι₀ q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .lam x a b
  | .pi' x a ⟨env, b⟩ => do
      let a ← a.quote
      let b ← b.eval ι₀ q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.quote
      return .pi' x a b
  | .glued ne _ => ne.quote

partial def Head.quote {n} : Head n → ElabM ι₀ q₀ (Tm n)
  | .var i => return .var i.rev
  | .const name us => return .const name us

partial def Neutral.quote {n} (ne : Neutral n) : ElabM ι₀ q₀ (Tm n) := do
  let ⟨h, sp⟩ := ne
  let rec go : Spine n → ElabM ι₀ q₀ (Tm n)
    | .nil => h.quote
    | .app sp t => return .app (← go sp) (← t.quote)
    | .proj sp i => return .proj i (← go sp)
  go sp

public partial def VTy.reify {n} : VTy n → ElabM ι₀ q₀ (Tm n)
  | .u i => return .u' i
  | .pi x a ⟨env, b⟩ => do
      let a ← a.reify
      let b ← b.eval ι₀ q₀ (env.weaken.cons (VTm.varAt n))
      let b ← b.reify
      return .pi' x a b
  | .el n => n.quote

public partial def VTy.inferLevel {n} (ctx : VCtx n) : VTy n → ElabM ι₀ q₀ Universe
  | .u i => return i.mkSucc
  | .pi _x a ⟨env, b⟩ => do
      let aLevel ← a.inferLevel ctx
      let bVal : VTy (n + 1) ← b.eval ι₀ q₀ (env.weaken.cons (VTm.varAt n))
      let bLevel ← bVal.inferLevel (ctx.snoc ⟨.anonymous, a⟩)
      return aLevel.mkMax bLevel
  | .el ⟨.const name us, _sp⟩ => do
      let some info ← fetchConstantInfo ι₀ q₀ name
        | panic! s!"inferLevel: unknown constant {name}"
      let ty := info.ty.substLevels (info.univParams.zip us)
      let some u := ty.getResultUniverse?
        | panic! s!"inferLevel: could not determine universe for {name}"
      return u
  | .el ⟨.var lvl, _sp⟩ => do
      let .u u := ctx.lookup lvl.rev
        | panic! "inferLevel: could not determine universe"
      return u

end

end Qdt
