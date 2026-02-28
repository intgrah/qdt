import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.DefinitionalEquality
import Qdt.Quote

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

def withChildTm {n α} (i : Nat) (action : TermM n α) : TermM n α := fun ctx =>
  withChild i (action ctx)

def emitType {n} (ty : VTy n) : TermM n Unit := do
  let ctx ← read
  let tySyn ← ty.quote
  emitTypeInfo (toString (tySyn.fmt ctx.names Prec.min))

partial def checkAstUniverse : Ast → MetaM Universe
  | .node `Level.zero _ => return .zero
  | .node `Level.succ cs => return .succ (← withChild 0 (checkAstUniverse cs[0]!))
  | .node `Level.max cs => return .max (← withChild 0 (checkAstUniverse cs[0]!)) (← withChild 1 (checkAstUniverse cs[1]!))
  | .node `Level.name cs => return .level cs[0]!.getName
  | _ => throw (.syntaxError)

def checkAstUniverses (univs : Array Ast) : MetaM (List Universe) :=
  univs.toList.mapM checkAstUniverse

private def checkUniverseLevel (level : Universe) : MetaM Unit := do
  let metaState ← getThe MetaState
  let univParams := metaState.univParams
  for name in level.levelNames do
    if name ∉ univParams then
      throw (.unboundUniverseVariable name)

private def instantiateLevels {n} (name : Name) (declParams : List Name) (ty : Ty 0) (univs : List Universe) :
    TermM n (Ty 0) := do
  if univs.length != declParams.length then
    throw (.universeArgCountMismatch name declParams.length univs.length)
  return ty.substLevels (declParams.zip univs)

private def inferIdent {n} (name : Name) (univs : List Universe) :
    TermM n (Tm n × VTy n) := do
  let ctx ← read
  if let some (i, ty) := ctx.findName? name then
    return (.var i, ty)
  else if let some info := (← fetchConstantInfo name) then
    for univ in univs do
      checkUniverseLevel univ
    let ty ←
      if univs.isEmpty && info.univParams.isEmpty then pure info.ty
      else instantiateLevels name info.univParams info.ty univs
    return (.const name univs, ← ty.eval .nil)
  else throw (.unboundVariable name)

private def isTypedBinder : Ast → Bool
  | .node `Binder.typed _ => true
  | _ => false

private def isUntypedBinder : Ast → Bool
  | .node `Binder.untyped _ => true
  | _ => false

private def getBinderName : Ast → Name
  | .node _ cs => cs[0]!.getName
  | _ => .anonymous

private def getBinderType : Ast → Ast
  | .node _ cs => cs[1]!
  | _ => .missing

mutual

private partial def processLetRhs {n}
    (name : Name)
    (tyOpt : Ast)
    (rhs : Ast) :
    TermM n (Tm n × Ty n × VTm n × TermContext (n + 1)) := do
  let (rhs, rhsTyVal, rhsTySyn) ←
    match tyOpt with
    | .missing =>
        let (rhsTm, rhsTy) ← withChildTm 2 (inferTm rhs)
        pure (rhsTm, rhsTy, ← rhsTy.quote)
    | ty =>
        let ty ← withChildTm 1 (checkTy ty)
        let ctx ← read
        let tyVal ← ty.eval ctx.env
        pure (← withChildTm 2 (checkTm tyVal rhs), tyVal, ty)
  withChildTm 0 (emitType rhsTyVal)
  let ctx ← read
  let rhsVal ← rhs.eval ctx.env
  let ctx' := ctx.define name rhsTyVal rhsVal
  return (rhs, rhsTySyn, rhsVal, ctx')

private partial def inferAnn {n} (e ann : Ast) : TermM n (Tm n × VTy n) := do
  let ann ← withChildTm 1 (checkTy ann)
  let ctx ← read
  let annVal ← ann.eval ctx.env
  return (← withChildTm 0 (checkTm annVal e), annVal)

private partial def checkEq {n} (a b : Ast) : TermM n (Tm n × Universe) := do
  let (aTm, ty) ← withChildTm 0 (inferTm a)
  let bTm ← withChildTm 1 (checkTm ty b)
  let tyTm ← ty.reify
  let ctx ← read
  let level ← ty.inferLevel ctx.ctx
  return (Tm.const `Eq [level] |>.apps [tyTm, aTm, bTm], level)

private partial def inferPi {n} (x : Name) (dom cod : Ast) : TermM n (Tm n × Universe) := do
  let (domTm, domTy) ← withChildTm 0 (withChildTm 1 (inferTm dom))
  let .u domLevel := domTy
    | throw (.expectedType (← read).names (← domTy.quote))
  let ctx ← read
  let domVal ← (Ty.el domTm).eval ctx.env
  withChildTm 0 (withChildTm 0 (emitType domVal))
  let ctx := ctx.bind x domVal
  let (codTm, codTy) ← withChildTm 1 (inferTm cod) ctx
  let .u codLevel := codTy
    | throw (.expectedType (← read).names (← codTy.quote))
  return (.pi' ⟨x, domTm⟩ codTm, .max domLevel codLevel)

partial def checkTyWithLevel {n} : Ast → TermM n (Ty n × Universe)
  | .missing => throw (.syntaxError)
  | .node `Term.u cs => do
      let level ← withChild 0 (checkAstUniverse cs[0]!)
      checkUniverseLevel level
      emitType (.u level.succ)
      return (.u level, level.succ)
  | .node `Term.pi cs => do
      let binder := cs[0]!
      if !isTypedBinder binder then throw (.syntaxError)
      let x := getBinderName binder
      let dom := getBinderType binder
      let (dom, domLevel) ← withChildTm 0 (withChildTm 1 (checkTyWithLevel dom))
      let ctx ← read
      let domVal ← dom.eval ctx.env
      withChildTm 0 (withChildTm 0 (emitType domVal))
      let ctx' := ctx.bind x domVal
      let (cod, codLevel) ← withChildTm 1 (checkTyWithLevel cs[1]!) ctx'
      return (.pi ⟨x, dom⟩ cod, .max domLevel codLevel)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq cs[0]! cs[1]!
      return (.el tm, level)
  | ast => do
      let (tm, ty) ← inferTm ast
      let .u level := ty | throw (.expectedType (← read).names (← ty.quote))
      return (.el tm, level)

partial def checkTy {n} (term : Ast) : TermM n (Ty n) :=
  return (← checkTyWithLevel term).fst

partial def inferTm {n} : Ast → TermM n (Tm n × VTy n)
  | .missing => throw (.syntaxError)
  | .node `Term.ident cs => do
      let .node _ univs := cs[1]! | throw (.syntaxError)
      let univs ← withChild 1 (checkAstUniverses univs)
      let result ← inferIdent cs[0]!.getName univs
      emitType result.snd
      return result
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChildTm 0 (inferTm cs[0]!)
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | let ctx ← read
          throw (.expectedFunctionType ctx.names (← fTy.quote))
      let aTm ← withChildTm 1 (checkTm aTy cs[1]!)
      let ctx ← read
      let aVal ← aTm.eval ctx.env
      let bTyVal ← bTy.eval (env.cons aVal)
      emitType bTyVal
      return (.app fTm aTm, bTyVal)
  | .node `Term.u cs => do
      let level ← withChild 0 (checkAstUniverse cs[0]!)
      let ty : VTy n := .u level.succ
      emitType ty
      return (.u' level, ty)
  | .node `Term.lam cs => do
      let binder := cs[0]!
      if !isTypedBinder binder then throw (.inferUnannotatedLambda)
      let x := getBinderName binder
      let ty := getBinderType binder
      let aTy ← withChildTm 0 (withChildTm 1 (checkTy ty))
      let ctx ← read
      let aTyVal ← aTy.eval ctx.env
      withChildTm 0 (withChildTm 0 (emitType aTyVal))
      let ctx' := ctx.bind x aTyVal
      let (bodyTm, bodyTy) ← withChildTm 1 (inferTm cs[1]!) ctx'
      let clos := ⟨ctx.env, ← bodyTy.quote⟩
      let resultTy : VTy n := .pi ⟨x, aTyVal⟩ clos
      emitType resultTy
      return (.lam ⟨x, aTy⟩ bodyTm, resultTy)
  | .node `Term.pi cs => do
      let binder := cs[0]!
      if !isTypedBinder binder then throw (.syntaxError)
      let (tm, level) ← inferPi (getBinderName binder) (getBinderType binder) cs[1]!
      let ty : VTy n := .u level
      emitType ty
      return (tm, ty)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq cs[0]! cs[1]!
      let ty : VTy n := .u level
      emitType ty
      return (tm, ty)
  | .node `Term.letE cs => do
      let (rhsTm, rhsTySyn, rhsVal, ctx') ← processLetRhs cs[0]!.getName cs[1]! cs[2]!
      let (body, bodyTyVal) ← withChildTm 3 (inferTm cs[3]!) ctx'
      let bodyTy ← bodyTyVal.quote
      let ctx ← read
      let ty ← bodyTy.eval (ctx.env.cons rhsVal)
      emitType ty
      return (.letE cs[0]!.getName rhsTySyn rhsTm body, ty)
  | .node `Term.ann cs => do
      let result ← inferAnn cs[0]! cs[1]!
      emitType result.snd
      return result
  | .node `Term.sorry _ => throw (.inferSorry)
  | _ => throw (.syntaxError)

partial def checkTm {n} (expected : VTy n) : Ast → TermM n (Tm n)
  | .missing => throw (.syntaxError)
  | .node `Term.ident cs => do
      let .node _ univs := cs[1]! | throw (.syntaxError)
      let univs ← withChild 1 (checkAstUniverses univs)
      let (tm, ty) ← inferIdent cs[0]!.getName univs
      if !(← ty.defEq expected) then
        let ctx ← read
        throw (.typeMismatch ctx.names (← expected.quote) (← ty.quote))
      emitType expected
      return tm
  | .node `Term.lam cs => do
      let binder := cs[0]!
      let body := cs[1]!
      let .pi ⟨_, a⟩ ⟨env, b⟩ := expected
        | let ctx ← read
          throw (.typeMismatch ctx.names (← expected.quote) (← (← inferTm (.node `Term.lam cs)).snd.quote))
      if isUntypedBinder binder then
        let x := getBinderName binder
        let ctx ← read
        withChildTm 0 (withChildTm 0 (emitType a))
        let ctx' := ctx.bind x a
        let b ← b.eval (env.weaken.cons (VTm.varAt n))
        let b ← withChildTm 1 (checkTm b body) ctx'
        emitType expected
        return .lam ⟨x, ← a.quote⟩ b
      else if isTypedBinder binder then
        let x := getBinderName binder
        let ann ← withChildTm 0 (withChildTm 1 (checkTy (getBinderType binder)))
        let ctx ← read
        let annVal ← ann.eval ctx.env
        if !(← annVal.defEq a) then
          throw (.typeMismatch ctx.names (← a.quote) (← annVal.quote))
        withChildTm 0 (withChildTm 0 (emitType a))
        let ctx' := ctx.bind x a
        let b ← b.eval (env.weaken.cons (VTm.varAt n))
        let body ← withChildTm 1 (checkTm b body) ctx'
        emitType expected
        return .lam ⟨x, ← a.quote⟩ body
      else throw (.syntaxError)
  | .node `Term.letE cs => do
      let name := cs[0]!.getName
      let (rhsTm, rhsTySyn, _rhsVal, ctx') ← processLetRhs name cs[1]! cs[2]!
      let body ← withChildTm 3 (checkTm expected.weaken cs[3]!) ctx'
      emitType expected
      return .letE name rhsTySyn rhsTm body
  | .node `Term.sorry _ => do
      let metaContext ← readThe MetaContext
      let metaState ← getModify fun st => { st with sorryId := st.sorryId + 1 }
      let sorryName := metaContext.currentDecl.str "_sorry" |>.num metaState.sorryId
      let ctx ← read
      let locals ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨name, ← vty.quote⟩
      let ty ← expected.quote
      let ty := Ty.pis locals ty
      let univParams := metaState.univParams
      let _ ← Global.addEntry sorryName (.axiom { univParams, ty })
      let args := List.finRange n |>.map (fun i => Tm.var i.rev)
      let sorryUnivs := univParams.map Universe.level
      emitType expected
      return Tm.const sorryName sorryUnivs |>.apps args
  | .node `Term.pi cs => do
      let binder := cs[0]!
      if !isTypedBinder binder then throw (.syntaxError)
      let (tm, level) ← inferPi (getBinderName binder) (getBinderType binder) cs[1]!
      if !(← expected.defEq (.u level)) then
        let ctx ← read
        throw (.typeMismatch ctx.names (← expected.quote) (.u level))
      emitType expected
      return tm
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq cs[0]! cs[1]!
      if !(← expected.defEq (.u level)) then
        let ctx ← read
        throw (.typeMismatch ctx.names (← expected.quote) (.u level))
      emitType expected
      return tm
  | .node `Term.ann cs => do
      let (tm, ty) ← inferAnn cs[0]! cs[1]!
      if !(← expected.defEq ty) then
        let ctx ← read
        throw (.typeMismatch ctx.names (← expected.quote) (← ty.quote))
      emitType expected
      return tm
  | .node `Term.u cs => do
      let level ← withChild 0 (checkAstUniverse cs[0]!)
      if !(← expected.defEq (.u level.succ)) then
        let ctx ← read
        throw (.typeMismatch ctx.names (← expected.quote) (.u level.succ))
      emitType expected
      return .u' level
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChildTm 0 (inferTm cs[0]!)
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | let ctx ← read
          throw (.expectedFunctionType ctx.names (← fTy.quote))
      let aTm ← withChildTm 1 (checkTm aTy cs[1]!)
      let ctx ← read
      let aVal ← aTm.eval ctx.env
      let tyVal ← bTy.eval (env.cons aVal)
      if !(← tyVal.defEq expected) then
        throw (.typeMismatch ctx.names (← expected.quote) (← tyVal.quote))
      emitType expected
      return .app fTm aTm
  | _ => throw (.syntaxError)
end

end Qdt
