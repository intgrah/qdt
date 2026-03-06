import Qdt.Control
import Qdt.Frontend.Ast
import Qdt.DefinitionalEquality
import Qdt.Quote

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

def emitType {n : Nat} (ctx : TermContext n) (ty : VTy n) : MetaM Unit := do
  if !(← readThe CoreContext).collectHovers then return
  emitHover (.typeOnly ctx.names (← ty.quote))

private def emitIdentHover {n : Nat} (ctx : TermContext n) (name : Name) (tm : Tm n) (ty : VTy n) : MetaM Unit := do
  if let .const constName _ := tm then
    if let some info ← fetchConstantInfo constName then
      emitHover (.signature constName .nil info.ty)
      return
  emitHover (.localVar name ctx.names (← ty.quote))

partial def checkAstUniverse : Ast → OptionT MetaM Universe
  | .node `Level.zero _ => return .zero
  | .node `Level.succ cs => do return .succ (← checkAstUniverse cs[0]!)
  | .node `Level.max cs => do return .max (← checkAstUniverse cs[0]!) (← checkAstUniverse cs[1]!)
  | .node `Level.name cs => return .level cs[0]!.getName
  | _ => raiseError .syntaxError

def checkAstUniverses : Ast → OptionT MetaM (List Universe)
  | .node _ cs => cs.toList.mapM checkAstUniverse
  | _ => return []

private def checkUniverseLevel (level : Universe) : OptionT MetaM Unit := do
  let univParams ← getUnivParams
  for name in level.levelNames do
    if name ∉ univParams then
      raiseError (.unboundUniverseVariable name)

private def instantiateLevels (name : Name) (declParams : List Name) (ty : Ty 0) (univs : List Universe) :
    OptionT MetaM (Ty 0) := do
  if univs.length != declParams.length then
    raiseError (.universeArgCountMismatch name declParams.length univs.length)
  return ty.substLevels (declParams.zip univs)

private def inferIdent {n : Nat} (ctx : TermContext n) (name : Name) (univs : List Universe) :
    OptionT MetaM (Tm n × VTy n) := do
  if let some (i, ty) := ctx.findName? name then
    return (.var i, ty)
  else
    match ← liftM (fetchConstantInfo name) with
    | some info =>
        for univ in univs do
          checkUniverseLevel univ
        let ty ←
          if univs.isEmpty then pure info.ty
          else instantiateLevels name info.univParams info.ty univs
        return (.const name univs, ← ty.eval .nil)
    | none => raiseError (.unboundVariable name)

private def emitSorryTm {n : Nat}
    (ctx : TermContext n)
    (expected : VTy n) :
    MetaM (Tm n) := do
  let decl ← currentDecl
  let id ← modifyGet fun s => (s.sorryId, { s with sorryId := s.sorryId + 1 })
  let sorryName := decl.str "_sorry" |>.num id
  let locals ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨name, ← vty.quote⟩
  let ty ← expected.quote
  let ty := Ty.pis locals ty
  let univParams ← getUnivParams
  let _ ← addConstant sorryName (.axiom { univParams, ty })
  let args := List.finRange n |>.map (fun i => Tm.var i.rev)
  let sorryUnivs := univParams.map Universe.level
  emitType ctx expected
  return Tm.const sorryName sorryUnivs |>.apps args

mutual

private partial def processLetRhs {n : Nat}
    (ctx : TermContext n)
    (name : Name)
    (tyOpt : Ast)
    (rhs : Ast) :
    OptionT MetaM (Tm n × Ty n × VTm n × TermContext (n + 1)) := do
  let (rhs, rhsTyVal, rhsTySyn) ←
    match tyOpt with
    | .missing =>
        let (rhsTm, rhsTy) ← withChild 2 (inferTm ctx rhs)
        pure (rhsTm, rhsTy, ← rhsTy.quote)
    | ty =>
        let ty ← withChild 1 (checkTy ctx ty)
        let tyVal ← ty.eval ctx.env
        pure (← withChild 2 (checkTmCore ctx tyVal rhs), tyVal, ty)
  withChild 0 (emitType ctx rhsTyVal)
  let rhsVal ← rhs.eval ctx.env
  let ctx' := ctx.define name rhsTyVal rhsVal
  return (rhs, rhsTySyn, rhsVal, ctx')

private partial def inferAnn {n : Nat} (ctx : TermContext n) (e : Ast) (ann : Ast) : OptionT MetaM (Tm n × VTy n) := do
  let ann ← withChild 1 (checkTy ctx ann)
  let annVal ← ann.eval ctx.env
  return (← withChild 0 (checkTmCore ctx annVal e), annVal)

private partial def checkEq {n : Nat}
    (ctx : TermContext n)
    (a : Ast)
    (b : Ast) :
    OptionT MetaM (Tm n × Universe) := do
  let (aTm, ty) ← withChild 0 (inferTm ctx a)
  let bTm ← withChild 1 (checkTmCore ctx ty b)
  let tyTm ← ty.reify
  let level ← ty.inferLevel ctx.ctx
  return (Tm.const `Eq [level] |>.apps [tyTm, aTm, bTm], level)

private partial def inferPi {n : Nat}
    (ctx : TermContext n)
    (x : Name)
    (dom : Ast)
    (cod : Ast) :
    OptionT MetaM (Tm n × Universe) := do
  let (domTm, domTy) ← withChild 0 (withChild 1 (inferTm ctx dom))
  let .u domLevel := domTy
    | raiseError (.expectedType ctx.names (← domTy.quote))
  let domVal ← (Ty.el domTm).eval ctx.env
  withChild 0 (withChild 0 (emitType ctx domVal))
  let ctx' := ctx.bind x domVal
  let (codTm, codTy) ← withChild 1 (inferTm ctx' cod)
  let .u codLevel := codTy
    | raiseError (.expectedType ctx'.names (← codTy.quote))
  return (.pi' ⟨x, domTm⟩ codTm, .max domLevel codLevel)

partial def checkTyWithLevel {n : Nat} (ctx : TermContext n) : Ast → OptionT MetaM (Ty n × Universe)
  | .missing => raiseError .syntaxError
  | .node `Term.u cs => do
      let level ← checkAstUniverse cs[0]!
      checkUniverseLevel level
      emitType ctx (.u level.succ)
      return (.u level, level.succ)
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | raiseError .syntaxError
      let x := bs[0]!.getName
      let (dom, domLevel) ← withChild 0 (withChild 1 (checkTyWithLevel ctx bs[1]!))
      let domVal ← dom.eval ctx.env
      withChild 0 (withChild 0 (emitType ctx domVal))
      let ctx' := ctx.bind x domVal
      let (cod, codLevel) ← withChild 1 (checkTyWithLevel ctx' cs[1]!)
      emitType ctx (.u (.max domLevel codLevel))
      return (.pi ⟨x, dom⟩ cod, .max domLevel codLevel)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      return (.el tm, level)
  | ast => do
      let (tm, ty) ← inferTm ctx ast
      let .u level := ty | raiseError (.expectedType ctx.names (← ty.quote))
      return (.el tm, level)

partial def checkTy {n : Nat} (ctx : TermContext n) (ast : Ast) : OptionT MetaM (Ty n) :=
  return (← checkTyWithLevel ctx ast).fst

partial def inferTm {n : Nat} (ctx : TermContext n) : Ast → OptionT MetaM (Tm n × VTy n)
  | .missing => raiseError .syntaxError
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses cs[1]!
      let result ← inferIdent ctx cs[0]!.getName univs
      emitIdentHover ctx cs[0]!.getName result.fst result.snd
      return result
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChild 0 (inferTm ctx cs[0]!)
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | raiseError (.expectedFunctionType ctx.names (← fTy.quote))
      let aTm ← OptionT.lift (withChild 1 (checkTm ctx aTy cs[1]!))
      let aVal ← aTm.eval ctx.env
      let bTyVal ← bTy.eval (env.cons aVal)
      emitType ctx bTyVal
      return (.app fTm aTm, bTyVal)
  | .node `Term.u cs => do
      let level ← checkAstUniverse cs[0]!
      let ty : VTy n := .u level.succ
      emitType ctx ty
      return (.u' level, ty)
  | .node `Term.lam cs => do
      let .node `Binder.typed bs := cs[0]! | raiseError .inferUnannotatedLambda
      let x := bs[0]!.getName
      let aTy ← withChild 0 (withChild 1 (checkTy ctx bs[1]!))
      let aTyVal ← aTy.eval ctx.env
      withChild 0 (withChild 0 (emitType ctx aTyVal))
      let ctx' := ctx.bind x aTyVal
      let (bodyTm, bodyTy) ← withChild 1 (inferTm ctx' cs[1]!)
      let clos := ⟨ctx.env, ← bodyTy.quote⟩
      let resultTy : VTy n := .pi ⟨x, aTyVal⟩ clos
      emitType ctx resultTy
      return (.lam ⟨x, aTy⟩ bodyTm, resultTy)
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | raiseError .syntaxError
      let (tm, level) ← inferPi ctx bs[0]!.getName bs[1]! cs[1]!
      let ty : VTy n := .u level
      emitType ctx ty
      return (tm, ty)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      let ty : VTy n := .u level
      emitType ctx ty
      return (tm, ty)
  | .node `Term.letE cs => do
      let name := cs[0]!.getName
      let (rhsTm, rhsTySyn, rhsVal, ctx') ← processLetRhs ctx name cs[1]! cs[2]!
      let (body, bodyTyVal) ← withChild 3 (inferTm ctx' cs[3]!)
      let bodyTy ← bodyTyVal.quote
      let ty ← bodyTy.eval (ctx.env.cons rhsVal)
      emitType ctx ty
      return (.letE name rhsTySyn rhsTm body, ty)
  | .node `Term.ann cs => do
      let result ← inferAnn ctx cs[0]! cs[1]!
      emitType ctx result.snd
      return result
  | .node `Term.sorry _ => raiseError .inferSorry
  | _ => raiseError .syntaxError

partial def checkTmCore {n : Nat} (ctx : TermContext n) (expected : VTy n) : Ast → OptionT MetaM (Tm n)
  | .missing => raiseError .syntaxError
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses cs[1]!
      let (tm, ty) ← inferIdent ctx cs[0]!.getName univs
      if !(← ty.defEq expected) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (← ty.quote))
      emitIdentHover ctx cs[0]!.getName tm ty
      return tm
  | ast@(.node `Term.lam cs) => do
      let body := cs[1]!
      let .pi ⟨_, a⟩ ⟨env, b⟩ := expected
        | raiseError (.typeMismatch ctx.names (← expected.quote) (← (← inferTm ctx ast).snd.quote))
      match cs[0]! with
      | .node `Binder.untyped bs =>
        let x := bs[0]!.getName
        withChild 0 (withChild 0 (emitType ctx a))
        let ctx' := ctx.bind x a
        let b ← b.eval (env.weaken.cons (VTm.varAt n))
        let b ← withChild 1 (checkTmCore ctx' b body)
        emitType ctx expected
        return .lam ⟨x, ← a.quote⟩ b
      | .node `Binder.typed bs =>
        let x := bs[0]!.getName
        let ann ← withChild 0 (withChild 1 (checkTy ctx bs[1]!))
        let annVal : VTy n ← ann.eval ctx.env
        if !(← annVal.defEq a) then
          raiseError (.typeMismatch ctx.names (← a.quote) (← annVal.quote))
        withChild 0 (withChild 0 (emitType ctx a))
        let ctx' := ctx.bind x a
        let b ← b.eval (env.weaken.cons (VTm.varAt n))
        let body ← withChild 1 (checkTmCore ctx' b body)
        emitType ctx expected
        return .lam ⟨x, ← a.quote⟩ body
      | _ => raiseError .syntaxError
  | .node `Term.letE cs => do
      let name := cs[0]!.getName
      let (rhsTm, rhsTySyn, _rhsVal, ctx') ← processLetRhs ctx name cs[1]! cs[2]!
      let body ← withChild 3 (checkTmCore ctx' expected.weaken cs[3]!)
      emitType ctx expected
      return .letE name rhsTySyn rhsTm body
  | .node `Term.sorry _ => emitSorryTm ctx expected
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | raiseError .syntaxError
      let (tm, level) ← inferPi ctx bs[0]!.getName bs[1]! cs[1]!
      if !(← expected.defEq (.u level)) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (.u level))
      emitType ctx expected
      return tm
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      if !(← expected.defEq (.u level)) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (.u level))
      emitType ctx expected
      return tm
  | .node `Term.ann cs => do
      let (tm, ty) ← inferAnn ctx cs[0]! cs[1]!
      if !(← expected.defEq ty) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (← ty.quote))
      emitType ctx expected
      return tm
  | .node `Term.u cs => do
      let level ← checkAstUniverse cs[0]!
      if !(← expected.defEq (.u level.succ)) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (.u level.succ))
      emitType ctx expected
      return .u' level
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChild 0 (inferTm ctx cs[0]!)
      let .pi ⟨_, aTy⟩ ⟨env, bTy⟩ := fTy
        | raiseError (.expectedFunctionType ctx.names (← fTy.quote))
      let aTm ← OptionT.lift (withChild 1 (checkTm ctx aTy cs[1]!))
      let aVal ← aTm.eval ctx.env
      let tyVal ← bTy.eval (env.cons aVal)
      if !(← tyVal.defEq expected) then
        raiseError (.typeMismatch ctx.names (← expected.quote) (← tyVal.quote))
      emitType ctx expected
      return .app fTm aTm
  | _ => raiseError .syntaxError

partial def checkTm {n : Nat} (ctx : TermContext n) (expected : VTy n) (ast : Ast) : MetaM (Tm n) := do
  match ← OptionT.run (checkTmCore ctx expected ast) with
  | some tm => return tm
  | none => emitSorryTm ctx expected
end

end Qdt
