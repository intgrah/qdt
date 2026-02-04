import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.DefinitionalEquality
import Qdt.Quote

namespace Qdt

open Lean (Name)

private def checkUniverseLevel (src : Frontend.Src) (level : Universe) : MetaM Unit := do
  let metaState ← getThe MetaState
  let univParams := metaState.univParams
  for name in level.levelNames do
    if !univParams.contains name then
      throw (.unboundUniverseVariable src name)

private def instantiateLevels {n} (src : Frontend.Src) (name : Name) (declParams : List Name) (ty : Ty 0) (univs : List Universe) :
    TermM n (Ty 0) := do
  if univs.length != declParams.length then
    throw (.universeArgCountMismatch src name declParams.length univs.length)
  return ty.substLevels (declParams.zip univs)

private def inferIdent {n} (src : Frontend.Src) (name : Name) (univs : List Universe) :
    TermM n (Tm n × VTy n) := do
  let ctx ← read
  if let some (i, ty) := ctx.findName? name then
    return (.var src i, ty)
  else if let some info := (← fetchConstantInfo name) then
    for univ in univs do
      checkUniverseLevel src univ
    let ty ←
      if univs.isEmpty && info.univParams.isEmpty then pure info.ty
      else instantiateLevels src name info.univParams info.ty univs
    return (.const src name univs, ← ty.eval .nil)
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

private partial def checkEq {n} (src : Frontend.Src) (a b : Frontend.Ast.Term) : TermM n (Tm n × Universe) := do
  let (aTm, ty) ← inferTm a
  let bTm ← checkTm ty b
  let tyTm ← ty.reify
  let ctx ← read
  let level ← ty.inferLevel ctx.ctx
  return (Tm.const src `Eq [level] |>.apps [tyTm, aTm, bTm], level)

private partial def inferPi {n} (src : Frontend.Src) : Frontend.Ast.TypedBinder → Frontend.Ast.Term → TermM n (Tm n × Universe)
  | ⟨binderSrc, x, dom⟩, cod => do
      let (domTm, domTy) ← inferTm dom
      let .u domLevel := domTy
        | throw (.expectedType (dom.src) (← read).names (← domTy.quote))
      let ctx ← read
      let domVal ← (Ty.el dom.src domTm).eval ctx.env
      let ctx := ctx.bind x domVal
      let (codTm, codTy) ← inferTm cod ctx
      let .u codLevel := codTy
        | throw (.expectedType (cod.src) (← read).names (← codTy.quote))
      return (.pi' src ⟨binderSrc, x, domTm⟩ codTm, .max domLevel codLevel)

partial def checkTyWithLevel {n} : Frontend.Ast.Term → TermM n (Ty n × Universe)
  | .missing src => throw (.typecheckMissing src)
  | .u src level => do
      checkUniverseLevel src level
      return (.u src level, level.succ)
  | .pi src ⟨annSrc, x, dom⟩ cod => do
      let (dom, domLevel) ← checkTyWithLevel dom
      let ctx ← read
      let domVal ← dom.eval ctx.env
      let ctx' := ctx.bind x domVal
      let (cod, codLevel) ← checkTyWithLevel cod ctx'
      return (.pi src ⟨annSrc, x, dom⟩ cod, .max domLevel codLevel)
  | .eq src a b => do
      let (tm, level) ← checkEq src a b
      return (.el src tm, level)
  | t => do
      let (tm, ty) ← inferTm t
      let .u level := ty | throw (.expectedType (t.src) (← read).names (← ty.quote))
      return (.el t.src tm, level)

partial def checkTy {n} (term : Frontend.Ast.Term) : TermM n (Ty n) :=
  return (← checkTyWithLevel term).fst

partial def inferTm {n} : Frontend.Ast.Term → TermM n (Tm n × VTy n)
  | .missing src => throw (.typecheckMissing src)
  | .ident src x univs => inferIdent src x univs
  | .app src f a => do
      let (fTm, fTy) ← inferTm f
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | let ctx ← read
          throw (.expectedFunctionType src ctx.names (← fTy.quote))
      let aTm ← checkTm aTy a
      let ctx ← read
      let aVal ← aTm.eval ctx.env
      let bTyVal ← bTy.eval (env.cons aVal)
      return (.app src fTm aTm, bTyVal)
  | .u src level => return (.u' src level, .u level.succ)
  | .lam src binder body => do
      let .typed ⟨binderSrc, x, ty⟩ := binder
        | throw (.inferUnannotatedLambda src)
      let aTy ← checkTy ty
      let ctx ← read
      let aTyVal ← aTy.eval ctx.env
      let ctx' := ctx.bind x aTyVal
      let (bodyTm, bodyTy) ← inferTm body ctx'
      let clos := ⟨ctx.env, ← bodyTy.quote⟩
      return (.lam src ⟨binderSrc, x, aTy⟩ bodyTm, .pi ⟨x, aTyVal⟩ clos)
  | .pi src binder cod => do
      let (tm, level) ← inferPi src binder cod
      return (tm, .u level)
  | .eq src a b => do
      let (tm, level) ← checkEq src a b
      return (tm, .u level)
  -- | .pair src a b => do
  --     let (aTm, aTy) ← inferTm a
  --     let (bTm, bTy) ← inferTm b
  --     let aCode ← aTy.reify
  --     let bCode ← bTy.reify
  --     let ctx ← read
  --     let aLevel ← aTy.inferLevel ctx.ctx
  --     let bLevel ← bTy.inferLevel ctx.ctx
  --     let prodCode := Tm.const src `Prod [aLevel, bLevel] |>.apps [aCode, bCode]
  --     let pairTm := Tm.const src `Prod.mk [aLevel, bLevel] |>.apps [aCode, bCode, aTm, bTm]
  --     let pairTy ← (Ty.el src prodCode).eval ctx.env
  --     return (pairTm, pairTy)
  | .letE src name tyOpt rhs body => do
      let (rhsTm, rhsTySyn, rhsVal, ctx') ← processLetRhs name tyOpt rhs
      let (body, bodyTyVal) ← inferTm body ctx'
      let bodyTy ← bodyTyVal.quote
      let ctx ← read
      let ty ← bodyTy.eval (ctx.env.cons rhsVal)
      return (.letE src name rhsTySyn rhsTm body, ty)
  | .ann _src e ty => inferAnn e ty
  | .sorry src => throw (.inferSorry src)

partial def checkTm {n} (expected : VTy n) : Frontend.Ast.Term → TermM n (Tm n)
  | .missing src => throw (.typecheckMissing src)
  | .ident src name univs => do
      let (tm, ty) ← inferIdent src name univs
      if !(← ty.defEq expected) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) (← ty.quote))
      return tm
  | tm@(.lam src binder body) => do
      let .pi ⟨_, a⟩ ⟨env, b⟩ := expected
        | let ctx ← read
          throw (.typeMismatch src ctx.names (← expected.quote) (← (← inferTm tm).snd.quote))
      match binder with
      | .untyped binderSrc x =>
          let ctx ← read
          let ctx' := ctx.bind x a
          let b ← b.eval (env.weaken.cons (VTm.varAt n))
          let b ← checkTm b body ctx'
          return .lam src ⟨binderSrc, x, ← a.quote⟩ b
      | .typed ⟨annSrc, x, ann⟩ =>
          let ann ← checkTy ann
          let ctx ← read
          let annVal ← ann.eval ctx.env
          if !(← annVal.defEq a) then
            throw (.typeMismatch annSrc ctx.names (← a.quote) (← annVal.quote))
          let ctx' := ctx.bind x a
          let b ← b.eval (env.weaken.cons (VTm.varAt n))
          let body ← checkTm b body ctx'
          return .lam src ⟨annSrc, x, ← a.quote⟩ body
  -- | .pair src a b => do
  --     let .el (Head.apps (.const `Prod us) [aCodeVal, bCodeVal]) := expected
  --       | let (_, aTy) ← inferTm a
  --         let (_, bTy) ← inferTm b
  --         let aCode ← aTy.reify
  --         let bCode ← bTy.reify
  --         let ctx ← read
  --         let aLevel ← aTy.inferLevel ctx.ctx
  --         let bLevel ← bTy.inferLevel ctx.ctx
  --         let prodCode := Ty.el src (Tm.const src `Prod [aLevel, bLevel] |>.apps [aCode, bCode])
  --         throw (.typeMismatch src ctx.names (← expected.quote) (← (← prodCode.eval ctx.env).quote))
  --     let fstTy ← doEl aCodeVal
  --     let sndTy ← doEl bCodeVal
  --     let aTm ← checkTm fstTy a
  --     let bTm ← checkTm sndTy b
  --     let aCodeTm ← aCodeVal.quote
  --     let bCodeTm ← bCodeVal.quote
  --     return Tm.const src `Prod.mk us |>.apps [aCodeTm, bCodeTm, aTm, bTm]
  | .letE src name tyOpt rhs body => do
      let (rhsTm, rhsTySyn, _rhsVal, ctx') ← processLetRhs name tyOpt rhs
      let body ← checkTm expected.weaken body ctx'
      return .letE src name rhsTySyn rhsTm body
  | .sorry src => do
      let metaContext ← readThe MetaContext
      let metaState ← getModify fun st => { st with sorryId := st.sorryId + 1 }
      let sorryName := metaContext.currentDecl.str "_sorry" |>.num metaState.sorryId
      let ctx ← read
      let locals ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨none, name, ← vty.quote⟩
      let ty ← expected.quote
      let ty := Ty.pis locals ty
      let univParams := metaState.univParams
      Global.addEntry sorryName (.axiom { univParams, ty })
      let args := List.finRange n |>.map (fun i => Tm.var src i.rev)
      let sorryUnivs := univParams.map Universe.level
      return Tm.const src sorryName sorryUnivs |>.apps args
  | .pi src binder cod => do
      let (tm, level) ← inferPi src binder cod
      if !(← expected.defEq (.u level)) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) (.u none level))
      return tm
  | .eq src a b => do
      let (tm, level) ← checkEq src a b
      if !(← expected.defEq (.u level)) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) (.u none level))
      return tm
  | .ann src e ty => do
      let (tm, ty) ← inferAnn e ty
      if !(← expected.defEq ty) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) (← ty.quote))
      return tm
  | .u src level => do
      if !(← expected.defEq (.u level.succ)) then
        let ctx ← read
        throw (.typeMismatch src ctx.names (← expected.quote) (.u none level.succ))
      return .u' src level
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
      return .app src fTm aTm
end

end Qdt
