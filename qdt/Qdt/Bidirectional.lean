import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.DefinitionalEquality
import Qdt.Quote

namespace Qdt

open Lean (Name)

private def inferIdent {n} (src : Frontend.Src) (name : Name) : TermM n (Tm n × VTy n) := do
  let ctx ← read
  if let some (i, ty) := ctx.findName? name then
    return (.var i, ty)
  else if let some ty := (← fetchTy name) then
    return (.const name, ← ty.eval .nil)
  else throw (.unboundVariable src name)

mutual

private partial def processLetRhs {n}
    (name : Name)
    (tyOpt : Option Frontend.Ast.Term)
    (rhs : Frontend.Ast.Term) :
    TermM n (Tm n × Ty n × VTm n × TermContext (n + 1)) := do
  let (rhs, rhsTyVal, rhsTySyn) ←
    match tyOpt with
    | some ty =>
        let ty ← checkTy ty
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        pure (← checkTm tyVal rhs, tyVal, ty)
    | none =>
        let (rhsTm, rhsTy) ← inferTm rhs
        pure (rhsTm, rhsTy, ← rhsTy.quote)
  let ctx ← read
  let rhsVal ← rhs.eval ctx.env
  let ctx' := ctx.define name rhsTyVal rhsVal
  return (rhs, rhsTySyn, rhsVal, ctx')

private partial def inferAnn {n} (e ann : Frontend.Ast.Term) : TermM n (Tm n × VTy n) := do
  let ann ← checkTy ann
  let ctx ← read
  let annVal ← ann.eval ctx.env
  return (← checkTm annVal e, annVal)

private partial def checkEq {n} (a b : Frontend.Ast.Term) : TermM n (Tm n) := do
  let (aTm, ty) ← inferTm a
  let bTm ← checkTm ty b
  let tyTm ← ty.reify
  return Tm.const `Eq |>.apps [tyTm, aTm, bTm]

private partial def checkPi {n} : Frontend.Ast.TypedBinder → Frontend.Ast.Term → TermM n (Tm n)
  | ⟨_src, x, dom⟩, cod => do
      let domTm ← checkTm .u dom
      let ctx ← read
      let domVal ← (Ty.el domTm).eval ctx.env
      let ctx := ctx.bind x domVal
      let codTm ← checkTm .u cod ctx
      return .piHat x domTm codTm

partial def checkTy {n} : Frontend.Ast.Term → TermM n (Ty n)
  | .missing src => throw (.typecheckMissing src)
  | .u _src => return .u
  | .pi _src ⟨_annSrc, x, dom⟩ cod => do
      let dom ← checkTy dom
      let ctx ← read
      let domVal ← dom.eval ctx.env
      let ctx' := ctx.bind x domVal
      let cod ← checkTy cod ctx'
      return .pi ⟨x, dom⟩ cod
  | .eq _src a b => return .el (← checkEq a b)
  | t => return .el (← checkTm .u t)

partial def inferTm {n} : Frontend.Ast.Term → TermM n (Tm n × VTy n)
  | .missing src => throw (.typecheckMissing src)
  | .ident src x => inferIdent src x
  | .app src f a => do
      let (fTm, fTy) ← inferTm f
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | let ctx ← read
          throw (.expectedFunctionType src ctx.names (← fTy.quote))
      let aTm ← checkTm aTy a
      let ctx ← read
      let aVal ← aTm.eval ctx.env
      let bTyVal ← bTy.eval (env.cons aVal)
      return (fTm.app aTm, bTyVal)
  | .u src => throw (.higherUniverse src)
  | .lam src binder body => do
      let .typed ⟨_src, x, ty⟩ := binder
        | throw (.inferUnannotatedLambda src)
      let aTy ← checkTy ty
      let ctx ← read
      let aTyVal ← aTy.eval ctx.env
      let ctx' := ctx.bind x aTyVal
      let (bodyTm, bodyTy) ← inferTm body ctx'
      let clos := ⟨ctx.env, ← bodyTy.quote⟩
      return (.lam ⟨x, aTy⟩ bodyTm, .pi ⟨x, aTyVal⟩ clos)
  | .pi _src binder cod => return (← checkPi binder cod, .u)
  | .eq _src a b => return (← checkEq a b, .u)
  | .pair _src a b => do
      let (aTm, aTy) ← inferTm a
      let (bTm, bTy) ← inferTm b
      let aCode ← aTy.reify
      let bCode ← bTy.reify
      let prodCode := Tm.const `Prod |>.apps [aCode, bCode]
      let pairTm := Tm.const `Prod.mk |>.apps [aCode, bCode, aTm, bTm]
      let ctx ← read
      let pairTy ← (Ty.el prodCode).eval ctx.env
      return (pairTm, pairTy)
  | .letE _src name tyOpt rhs body => do
      let (rhsTm, rhsTySyn, rhsVal, ctx') ← processLetRhs name tyOpt rhs
      let (body, bodyTyVal) ← inferTm body ctx'
      let bodyTy ← bodyTyVal.quote
      let ctx ← read
      let ty ← bodyTy.eval (ctx.env.cons rhsVal)
      return (.letE name rhsTySyn rhsTm body, ty)
  | .ann _src e ty => inferAnn e ty
  | .sorry src => throw (.inferSorry src)

partial def checkTm {n} (expected : VTy n) : Frontend.Ast.Term → TermM n (Tm n)
  | .missing src => throw (.typecheckMissing src)
  | .ident _src name => do
      let (tm, ty) ← inferIdent _src name
      if !(← ty.defEq expected) then
        let ctx ← read
        throw (.typeMismatch _src ctx.names (← expected.quote) (← ty.quote))
      return tm
  | tm@(.lam src binder body) => do
      let .pi ⟨_, a⟩ ⟨env, b⟩ := expected
        | let ctx ← read
          throw (.typeMismatch src ctx.names (← expected.quote) (← (← inferTm tm).snd.quote))
      match binder with
      | .untyped _src x =>
          let ctx ← read
          let ctx' := ctx.bind x a
          let b ← b.eval (env.weaken.cons (VTm.varAt n))
          let b ← checkTm b body ctx'
          return .lam ⟨x, ← a.quote⟩ b
      | .typed ⟨annSrc, x, ann⟩ =>
          let ann ← checkTy ann
          let ctx ← read
          let ann ← ann.eval ctx.env
          if !(← ann.defEq a) then
            throw (.typeMismatch annSrc ctx.names (← a.quote) (← ann.quote))
          let ctx' := ctx.bind x a
          let b ← b.eval (env.weaken.cons (VTm.varAt n))
          let body ← checkTm b body ctx'
          return .lam ⟨x, ← a.quote⟩ body
  | .pair src a b => do
      let .el (Head.apps (.const `Prod) [aCodeVal, bCodeVal]) := expected
        | let aCode ← (← inferTm a).snd.reify
          let bCode ← (← inferTm b).snd.reify
          let prodCode := Ty.el (Tm.const `Prod |>.apps [aCode, bCode])
          let ctx ← read
          throw (.typeMismatch src ctx.names (← expected.quote) (← (← prodCode.eval ctx.env).quote))
      let fstTy ← doEl aCodeVal
      let sndTy ← doEl bCodeVal
      let aTm ← checkTm fstTy a
      let bTm ← checkTm sndTy b
      let aCodeTm ← aCodeVal.quote
      let bCodeTm ← bCodeVal.quote
      return Tm.const `Prod.mk |>.apps [aCodeTm, bCodeTm, aTm, bTm]
  | .letE _src name tyOpt rhs body => do
      let (rhsTm, rhsTySyn, _rhsVal, ctx') ← processLetRhs name tyOpt rhs
      let body ← checkTm expected.weaken body ctx'
      return .letE name rhsTySyn rhsTm body
  | .sorry src => do
      let metaContext ← readThe MetaContext
      let metaState ← getModify fun st => { st with sorryId := st.sorryId + 1 }
      let sorryName := metaContext.currentDecl.str "_sorry" |>.num metaState.sorryId
      let ctx ← read
      let locals ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨name, ← vty.quote⟩
      let ty ← expected.quote
      let ty := Ty.pis locals ty
      Global.addEntry sorryName (.axiom ⟨ty⟩)
      let args := List.finRange n |>.map (fun i => .var i.rev)
      return Tm.const sorryName |>.apps args
  | .pi src binder cod => do
      if !(← expected.defEq .u) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) .u)
      checkPi binder cod
  | .eq _src a b => do
      if !(← expected.defEq .u) then
        let ctx ← read
        throw (.typeMismatch _src ctx.names (← expected.quote) .u)
      checkEq a b
  | .ann _src e ty => do
      let (tm, ty) ← inferAnn e ty
      if !(← expected.defEq ty) then
        let ctx ← read
        throw (.typeMismatch _src ctx.names (← expected.quote) (← ty.quote))
      return tm
  | .u src => throw (.higherUniverse src)
  | .app src f a => do
      let (fTm, fTy) ← inferTm f
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | let ctx ← read
          throw (.expectedFunctionType src ctx.names (← fTy.quote))
      let aTm ← checkTm aTy a
      let ctx ← read
      let aVal ← aTm.eval ctx.env
      let tyVal ← bTy.eval (env.cons aVal)
      if !(← tyVal.defEq expected) then
        throw (.typeMismatch src ctx.names (← expected.quote) (← tyVal.quote))
      return .app fTm aTm
end

end Qdt
