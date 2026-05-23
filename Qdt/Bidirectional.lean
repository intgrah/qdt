module

public import Qdt.Conversion
public import Qdt.Quote
public import Qdt.Unify

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

def freshMeta' {n : Nat} (anchor : Path) (ctx : TermContext n) (expected : VTy n) :
    ElabM q₀ (MVarId × Tm n) := do
  let decl ← currentDecl q₀
  let localPis ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨name, ← vty.quote q₀⟩
  let expectedTy ← expected.quote q₀
  let closedTy : Ty 0 := Ty.pis localPis expectedTy
  let info : MetaInfo := {
    arity := n
    ctxNames := ctx.names
    ty := closedTy
    solution := none
    path := anchor
    decl := decl
  }
  let id ← freshMetaId q₀ info
  let args : List (Tm n) := (List.finRange n).map (fun i => Tm.var i.rev)
  return (id, Tm.apps (.mvar id) args)

def freshMeta {n : Nat} (anchor : Path) (ctx : TermContext n) (expected : VTy n) :
    ElabM q₀ (Tm n) :=
  return (← freshMeta' q₀ anchor ctx expected).2

@[inline] def emitType {n : Nat} (ctx : TermContext n) (ty : VTy n) : ElabM q₀ Unit := do
  if !(← readThe ElabContext).collectHovers then return
  emitHover q₀ (.typeOnly ctx.names (← ty.quote q₀))

def emitIdentHover {n : Nat} (ctx : TermContext n) (name : Name) (tm : Tm n) (ty : VTy n) : ElabM q₀ Unit := do
  if let .const constName _ := tm then
    if let some info ← fetchConstantInfo q₀ constName then
      emitHover q₀ (.signature constName .nil info.ty)
      return
  emitHover q₀ (.localVar name ctx.names (← ty.quote q₀))

public partial def checkAstUniverse : Ast → OptionT (ElabM q₀) Universe
  | .node `Level.zero _ => do return .zero
  | .node `Level.succ cs => do return (← checkAstUniverse cs[0]!).mkSucc
  | .node `Level.max cs => do return (← checkAstUniverse cs[0]!).mkMax (← checkAstUniverse cs[1]!)
  | .node `Level.name cs => do
      let name := cs[0]!.getName
      let univParams ← getUnivParams q₀
      let some idx := univParams.findIdx? (· == name)
        | raiseError q₀ (.unboundUniverseVariable name)
      return .level idx
  | _ => failure

def checkAstUniverses : Ast → OptionT (ElabM q₀) (List Universe)
  | .node _ cs => cs.toList.mapM (checkAstUniverse q₀)
  | _ => return []

def checkUniverseLevel (level : Universe) : OptionT (ElabM q₀) Unit := do
  let univParams ← getUnivParams q₀
  if let .error i := level.checkLevels univParams.length then
    raiseError q₀ (.unboundUniverseVariable ((`_univ).num i))

def instantiateLevels (name : Name) (numDeclParams : Nat) (ty : Ty 0) (univs : List Universe) :
    OptionT (ElabM q₀) (Ty 0) := do
  if univs.length != numDeclParams then
    raiseError q₀ (.universeArgCountMismatch name numDeclParams univs.length)
  return ty.substLevels univs

def inferIdent {n : Nat} (ctx : TermContext n) (name : Name) (univs : List Universe) :
    OptionT (ElabM q₀) (Tm n × VTy n) := do
  if let some (i, ty) := ctx.findName? name then
    return (.var i, ty)
  else
    match ← liftM (fetchConstantInfo q₀ name) with
    | some info =>
        for univ in univs do
          checkUniverseLevel q₀ univ
        let univs ←
          if univs.isEmpty && info.numUnivParams > 0 then
            (List.range info.numUnivParams).mapM fun _ => do
              let id ← Universe.freshUMVar q₀
              pure (Universe.mvar id)
          else pure univs
        let ty ←
          if info.numUnivParams = 0 then pure info.ty
          else instantiateLevels q₀ name info.numUnivParams info.ty univs
        return (.const name univs, ← ty.eval q₀ .nil)
    | none => raiseError q₀ (.unboundVariable name)

def emitSorryAxiom {n : Nat}
    (ctx : TermContext n)
    (retTy : Ty n) :
    ElabM q₀ (Tm n) := do
  let decl ← currentDecl q₀
  let id ← modifyGet fun s => (s.sorryId, { s with sorryId := s.sorryId + 1 })
  let sorryName := decl.str "_sorry" |>.num id
  let locals ← ctx.ctx.mapM fun ⟨name, vty⟩ => return ⟨name, ← vty.quote q₀⟩
  let univParams ← getUnivParams q₀
  let _ ← addConstant q₀ sorryName (.axiom {
    numUnivParams := univParams.length
    ty := Ty.pis locals retTy
    synthetic := true
  })
  let args := List.finRange n |>.map (fun i => Tm.var i.rev)
  let sorryUnivs := List.finRange univParams.length |>.map fun i => Universe.level i.val
  return Tm.const sorryName sorryUnivs |>.apps args

def emitSorryTm {n : Nat}
    (ctx : TermContext n)
    (expected : VTy n) :
    ElabM q₀ (Tm n) := do
  let tm ← emitSorryAxiom q₀ ctx (← expected.quote q₀)
  emitType q₀ ctx expected
  return tm

def emitSorryTy {n : Nat}
    (ctx : TermContext n) :
    ElabM q₀ (Ty n × Universe) := do
  let tm ← emitSorryAxiom q₀ ctx (Ty.u .zero)
  return (.el tm, .zero)

@[inline] def isSyntheticSorryName (name : Name) : ElabM q₀ Bool := do
  match ← fetchConstant q₀ name with
  | some (.axiom info) => return info.synthetic
  | _ => return false

mutual
partial def Tm.hasSyntheticSorry {n} : Tm n → ElabM q₀ Bool
  | .u' _ => return false
  | .var _ => return false
  | .const name _ => isSyntheticSorryName q₀ name
  | .lam _ ty body => do return (← ty.hasSyntheticSorry) || (← body.hasSyntheticSorry)
  | .app f a => do return (← f.hasSyntheticSorry) || (← a.hasSyntheticSorry)
  | .pi' _ a b => do return (← a.hasSyntheticSorry) || (← b.hasSyntheticSorry)
  | .proj _ t => t.hasSyntheticSorry
  | .letE _ ty rhs body => do
      return (← ty.hasSyntheticSorry) || (← rhs.hasSyntheticSorry) || (← body.hasSyntheticSorry)
  | .mvar id => metaIsErrored q₀ id

partial def Ty.hasSyntheticSorry {n} : Ty n → ElabM q₀ Bool
  | .u _ => return false
  | .pi _ a b => do return (← a.hasSyntheticSorry) || (← b.hasSyntheticSorry)
  | .el t => t.hasSyntheticSorry
end

mutual
partial def Tm.markMetasErrored {n} : Tm n → ElabM q₀ Unit
  | .u' _ | .var _ | .const _ _ => return
  | .lam _ ty body => do ty.markMetasErrored; body.markMetasErrored
  | .app f a => do f.markMetasErrored; a.markMetasErrored
  | .pi' _ a b => do a.markMetasErrored; b.markMetasErrored
  | .proj _ t => t.markMetasErrored
  | .letE _ ty rhs body => do
      ty.markMetasErrored; rhs.markMetasErrored; body.markMetasErrored
  | .mvar id => markMetaErrored q₀ id

partial def Ty.markMetasErrored {n} : Ty n → ElabM q₀ Unit
  | .u _ => return
  | .pi _ a b => do a.markMetasErrored; b.markMetasErrored
  | .el t => t.markMetasErrored
end

def raiseTypeMismatch {n} {α : Type}
    (ctx : TermContext n) (expected actual : Ty n) :
    OptionT (ElabM q₀) α := do
  if (← expected.hasSyntheticSorry q₀) || (← actual.hasSyntheticSorry q₀) then
    expected.markMetasErrored q₀
    actual.markMetasErrored q₀
    failure
  expected.markMetasErrored q₀
  actual.markMetasErrored q₀
  raiseError q₀ (.typeMismatch ctx.names expected actual)

def raiseExpectedFunctionType {n} {α : Type}
    (ctx : TermContext n) (got : Ty n) :
    OptionT (ElabM q₀) α := do
  if (← got.hasSyntheticSorry q₀) then
    got.markMetasErrored q₀
    failure
  got.markMetasErrored q₀
  raiseError q₀ (.expectedFunctionType ctx.names got)

def raiseExpectedType {n} {α : Type}
    (ctx : TermContext n) (got : Ty n) :
    OptionT (ElabM q₀) α := do
  if (← got.hasSyntheticSorry q₀) then
    got.markMetasErrored q₀
    failure
  got.markMetasErrored q₀
  raiseError q₀ (.expectedType ctx.names got)

mutual

partial def processLetRhs {n : Nat}
    (ctx : TermContext n)
    (name : Name)
    (tyOpt : Ast)
    (rhs : Ast) :
    OptionT (ElabM q₀) (Tm n × Ty n × VTm n × TermContext (n + 1)) := do
  let (rhs, rhsTyVal, rhsTySyn) ←
    match tyOpt with
    | .missing =>
        let (rhsTm, rhsTy) ← withChild q₀ 2 (inferTm ctx rhs)
        pure (rhsTm, rhsTy, ← rhsTy.quote q₀)
    | ty =>
        let ty ← OptionT.lift (withChild q₀ 1 (checkTy ctx ty))
        let tyVal ← ty.eval q₀ ctx.env
        pure (← withChild q₀ 2 (checkTmCore ctx tyVal rhs), tyVal, ty)
  withChild q₀ 0 (emitType q₀ ctx rhsTyVal)
  let rhsVal ← rhs.eval q₀ ctx.env
  let ctx' := ctx.define name rhsTyVal rhsVal
  return (rhs, rhsTySyn, rhsVal, ctx')

partial def inferAnn {n : Nat} (ctx : TermContext n) (e : Ast) (ann : Ast) : OptionT (ElabM q₀) (Tm n × VTy n) := do
  let ann ← OptionT.lift (withChild q₀ 1 (checkTy ctx ann))
  let annVal ← ann.eval q₀ ctx.env
  return (← withChild q₀ 0 (checkTmCore ctx annVal e), annVal)

partial def checkEq {n : Nat}
    (ctx : TermContext n)
    (a : Ast)
    (b : Ast) :
    OptionT (ElabM q₀) (Tm n × Universe) := do
  let anchor ← currentPath q₀
  let levelId ← Universe.freshUMVar q₀
  let level : Universe := .mvar levelId
  let (_, tyTm) ← freshMeta' q₀ anchor ctx (.u level)
  let tyVal : VTy n ← (Ty.el tyTm).eval q₀ ctx.env
  let aTm ← withChild q₀ 0 (checkTmCore ctx tyVal a)
  let bTm ← withChild q₀ 1 (checkTmCore ctx tyVal b)
  return (Tm.const `Eq [level] |>.apps [tyTm, aTm, bTm], level)

partial def inferPi {n : Nat}
    (ctx : TermContext n)
    (x : Name)
    (dom : Ast)
    (cod : Ast) :
    OptionT (ElabM q₀) (Tm n × Universe) := do
  let (domTm, domTy) ← withChild q₀ 0 (withChild q₀ 1 (inferTm ctx dom))
  let .u domLevel := domTy
    | raiseExpectedType q₀ ctx (← domTy.quote q₀)
  let domVal ← (Ty.el domTm).eval q₀ ctx.env
  withChild q₀ 0 (withChild q₀ 0 (emitType q₀ ctx domVal))
  let ctx' := ctx.bind x domVal
  let (codTm, codTy) ← withChild q₀ 1 (inferTm ctx' cod)
  let .u codLevel := codTy
    | raiseExpectedType q₀ ctx' (← codTy.quote q₀)
  return (.pi' x domTm codTm, domLevel.mkMax codLevel)

partial def checkTyWithLevelCore {n : Nat} (ctx : TermContext n) : Ast → OptionT (ElabM q₀) (Ty n × Universe)
  | .missing => failure
  | .node `Term.hole _ => OptionT.lift do
      let anchor ← currentPath q₀
      let (id, tm) ← freshMeta' q₀ anchor ctx (.u .zero)
      emitHover q₀ (.hole id ctx.names (Ty.u (n := n) .zero))
      return (.el tm, .zero)
  | .node `Term.u cs => do
      let level ← checkAstUniverse q₀ cs[0]!
      checkUniverseLevel q₀ level
      emitType q₀ ctx (.u level.mkSucc)
      return (.u level, level.mkSucc)
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | failure
      let x := bs[0]!.getName
      let (dom, domLevel) ← withChild q₀ 0 (withChild q₀ 1 (checkTyWithLevelCore ctx bs[1]!))
      let domVal ← dom.eval q₀ ctx.env
      withChild q₀ 0 (withChild q₀ 0 (emitType q₀ ctx domVal))
      let ctx' := ctx.bind x domVal
      let (cod, codLevel) ← withChild q₀ 1 (checkTyWithLevelCore ctx' cs[1]!)
      let piLevel := domLevel.mkMax codLevel
      emitType q₀ ctx (.u piLevel)
      return (.pi x dom cod, piLevel)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      return (.el tm, level)
  | ast => do
      let (tm, ty) ← inferTm ctx ast
      let .u level := ty | raiseExpectedType q₀ ctx (← ty.quote q₀)
      return (.el tm, level)

public partial def checkTyWithLevel {n : Nat} (ctx : TermContext n) (ast : Ast) : ElabM q₀ (Ty n × Universe) := do
  match ← OptionT.run (checkTyWithLevelCore ctx ast) with
  | some result => return result
  | none => emitSorryTy q₀ ctx

public partial def checkTy {n : Nat} (ctx : TermContext n) (ast : Ast) : ElabM q₀ (Ty n) :=
  return (← checkTyWithLevel ctx ast).fst

public partial def inferTm {n : Nat} (ctx : TermContext n) : Ast → OptionT (ElabM q₀) (Tm n × VTy n)
  | .missing => failure
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses q₀ cs[1]!
      let result ← inferIdent q₀ ctx cs[0]!.getName univs
      emitIdentHover q₀ ctx cs[0]!.getName result.fst result.snd
      return result
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChild q₀ 0 (inferTm ctx cs[0]!)
      let .pi _ aTy ⟨env, bTy⟩ := fTy
        | raiseExpectedFunctionType q₀ ctx (← fTy.quote q₀)
      let aTm ← OptionT.lift (withChild q₀ 1 (checkTm ctx aTy cs[1]!))
      let aVal ← aTm.eval q₀ ctx.env
      let bTyVal ← bTy.eval q₀ (env.cons aVal)
      emitType q₀ ctx bTyVal
      return (.app fTm aTm, bTyVal)
  | .node `Term.u cs => do
      let level ← checkAstUniverse q₀ cs[0]!
      let ty : VTy n := .u level.mkSucc
      emitType q₀ ctx (.u level.mkSucc)
      return (.u' level, ty)
  | .node `Term.lam cs => do
      let .node `Binder.typed bs := cs[0]! | raiseError q₀ .inferUnannotatedLambda
      let x := bs[0]!.getName
      let aTy ← OptionT.lift (withChild q₀ 0 (withChild q₀ 1 (checkTy ctx bs[1]!)))
      let aTyVal ← aTy.eval q₀ ctx.env
      withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names aTy)))
      let ctx' := ctx.bind x aTyVal
      let (bodyTm, bodyTy) ← withChild q₀ 1 (inferTm ctx' cs[1]!)
      let clos := ⟨ctx.env, ← bodyTy.quote q₀⟩
      let resultTy : VTy n := .pi x aTyVal clos
      emitType q₀ ctx resultTy
      return (.lam x aTy bodyTm, resultTy)
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | failure
      let (tm, level) ← inferPi ctx bs[0]!.getName bs[1]! cs[1]!
      let ty : VTy n := .u level
      emitType q₀ ctx ty
      return (tm, ty)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      let ty : VTy n := .u level
      emitType q₀ ctx ty
      return (tm, ty)
  | .node `Term.letE cs => do
      let name := cs[0]!.getName
      let (rhsTm, rhsTySyn, rhsVal, ctx') ← processLetRhs ctx name cs[1]! cs[2]!
      let (body, bodyTyVal) ← withChild q₀ 3 (inferTm ctx' cs[3]!)
      let bodyTy ← bodyTyVal.quote q₀
      let ty ← bodyTy.eval q₀ (ctx.env.cons rhsVal)
      emitType q₀ ctx ty
      return (.letE name rhsTySyn rhsTm body, ty)
  | .node `Term.ann cs => do
      let result ← inferAnn ctx cs[0]! cs[1]!
      emitType q₀ ctx result.snd
      return result
  | .node `Term.sorry _ => raiseError q₀ .inferSorry
  | .node `Term.hole _ => raiseError q₀ .inferHole
  | _ => failure

partial def checkTmCore {n : Nat} (ctx : TermContext n) (expected : VTy n) : Ast → OptionT (ElabM q₀) (Tm n)
  | .missing => failure
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses q₀ cs[1]!
      let (tm, ty) ← inferIdent q₀ ctx cs[0]!.getName univs
      if !(← VTy.conv q₀ ty expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← ty.quote q₀)
      emitIdentHover q₀ ctx cs[0]!.getName tm ty
      return tm
  | ast@(.node `Term.lam cs) => do
      let body := cs[1]!
      match expected with
      | .pi _ a ⟨env, b⟩ =>
        match cs[0]! with
        | .node `Binder.untyped bs =>
          let x := bs[0]!.getName
          withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names (← a.quote q₀))))
          let ctx' := ctx.bind x a
          let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
          let b ← withChild q₀ 1 (checkTmCore ctx' b body)
          emitType q₀ ctx expected
          return .lam x (← a.quote q₀) b
        | .node `Binder.typed bs =>
          let x := bs[0]!.getName
          let ann ← OptionT.lift (withChild q₀ 0 (withChild q₀ 1 (checkTy ctx bs[1]!)))
          let annVal : VTy n ← ann.eval q₀ ctx.env
          if !(← VTy.conv q₀ annVal a) then
            raiseTypeMismatch q₀ ctx (← a.quote q₀) (← annVal.quote q₀)
          withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names (← a.quote q₀))))
          let ctx' := ctx.bind x a
          let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
          let body ← withChild q₀ 1 (checkTmCore ctx' b body)
          emitType q₀ ctx expected
          return .lam x (← a.quote q₀) body
        | _ => failure
      | _ =>
        let (inferredTm, inferredTy) ← inferTm ctx ast
        if !(← VTy.conv q₀ inferredTy expected) then
          raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← inferredTy.quote q₀)
        emitType q₀ ctx expected
        return inferredTm
  | .node `Term.letE cs => do
      let name := cs[0]!.getName
      let (rhsTm, rhsTySyn, _rhsVal, ctx') ← processLetRhs ctx name cs[1]! cs[2]!
      let body ← withChild q₀ 3 (checkTmCore ctx' expected.weaken cs[3]!)
      emitType q₀ ctx expected
      return .letE name rhsTySyn rhsTm body
  | .node `Term.sorry _ => OptionT.lift (emitSorryTm q₀ ctx expected)
  | .node `Term.hole _ => OptionT.lift do
      let anchor ← currentPath q₀
      let (id, tm) ← freshMeta' q₀ anchor ctx expected
      emitHover q₀ (.hole id ctx.names (← expected.quote q₀))
      return tm
  | .node `Term.pi cs => do
      let .node `Binder.typed bs := cs[0]! | failure
      let (tm, level) ← inferPi ctx bs[0]!.getName bs[1]! cs[1]!
      if !(← expected.conv q₀ (.u level)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level)
      emitType q₀ ctx expected
      return tm
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      if !(← expected.conv q₀ (.u level)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level)
      emitType q₀ ctx expected
      return tm
  | .node `Term.ann cs => do
      let (tm, ty) ← inferAnn ctx cs[0]! cs[1]!
      if !(← VTy.conv q₀ ty expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← ty.quote q₀)
      emitType q₀ ctx expected
      return tm
  | .node `Term.u cs => do
      let level ← checkAstUniverse q₀ cs[0]!
      if !(← expected.conv q₀ (.u level.mkSucc)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level.mkSucc)
      emitType q₀ ctx expected
      return .u' level
  | .node `Term.app cs => do
      let (fTm, fTy) ← withChild q₀ 0 (inferTm ctx cs[0]!)
      let .pi _ aTy ⟨env, bTy⟩ := fTy
        | raiseExpectedFunctionType q₀ ctx (← fTy.quote q₀)
      let aTm ← OptionT.lift (withChild q₀ 1 (checkTm ctx aTy cs[1]!))
      let aVal ← aTm.eval q₀ ctx.env
      let tyVal ← bTy.eval q₀ (env.cons aVal)
      if !(← VTy.conv q₀ tyVal expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← tyVal.quote q₀)
      emitType q₀ ctx expected
      return .app fTm aTm
  | _ => failure

public partial def checkTm {n : Nat} (ctx : TermContext n) (expected : VTy n) (ast : Ast) : ElabM q₀ (Tm n) := do
  match ← OptionT.run (checkTmCore ctx expected ast) with
  | some tm => return tm
  | none => emitSorryTm q₀ ctx expected
end

mutual

public partial def Tm.zonk {n} (q₀ : Key) : Tm n → ElabM q₀ (Tm n)
  | .u' u => return .u' (← Universe.zonk q₀ u)
  | .var i => return .var i
  | .const c us => return .const c (← us.mapM (Universe.zonk q₀))
  | .lam x ty body => return .lam x (← ty.zonk q₀) (← body.zonk q₀)
  | .app f a => return .app (← f.zonk q₀) (← a.zonk q₀)
  | .pi' x a b => return .pi' x (← a.zonk q₀) (← b.zonk q₀)
  | .proj i t => return .proj i (← t.zonk q₀)
  | .letE x ty rhs body =>
      return .letE x (← ty.zonk q₀) (← rhs.zonk q₀) (← body.zonk q₀)
  | .mvar id => do
      match ← getMetaInfo q₀ id with
      | some info =>
          match info.solution with
          | some closedBody =>
              let v0 ← closedBody.eval q₀ (Env.nil : Env 0 0)
              let vn : VTm n := v0.weaken (Nat.zero_le n)
              vn.quote q₀
          | none => return .mvar id
      | none => return .mvar id

public partial def Ty.zonk {n} (q₀ : Key) : Ty n → ElabM q₀ (Ty n)
  | .u u => return .u (← Universe.zonk q₀ u)
  | .pi x dom cod => return .pi x (← dom.zonk q₀) (← cod.zonk q₀)
  | .el t => return .el (← t.zonk q₀)

end

public def reportUnsolvedMetas : ElabM q₀ Bool := do
  let st ← get
  let mut hadUnsolved := false
  for h : i in [:st.metas.size] do
    let info := st.metas[i]
    if info.solution.isNone then
      hadUnsolved := true
      unless info.errored do
        emitDiagnosticAt q₀ info.path (.unsolvedMetavariable info.decl i info.ty)
  return hadUnsolved

partial def resolveHoleHover (metaId : MVarId) {n : Nat} (ctxNames : List Name) (ty : Ty n) :
    ElabM q₀ HoverContent := do
  let ty ← ty.zonk q₀
  let some info ← getMetaInfo q₀ metaId
    | return .typeOnly ctxNames ty
  if info.solution.isNone then
    return .typeOnly ctxNames ty
  let args : List (Tm n) := (List.finRange n).map (fun i => .var i.rev)
  let v ← (Tm.apps (.mvar metaId) args).eval q₀ (Env.identity n) >>= (·.whnf q₀)
  let tm ← v.quote q₀
  match tm with
  | .const c _ =>
      match ← fetchConstantInfo q₀ c with
      | some constInfo => return .signature c .nil constInfo.ty
      | none => return .typeOnly ctxNames ty
  | .var ⟨i, _⟩ =>
      match ctxNames[i]? with
      | some name => return .localVar name ctxNames ty
      | none => return .typeOnly ctxNames ty
  | _ => return .typeOnly ctxNames ty

public def zonkHover : HoverContent → ElabM q₀ HoverContent
  | .signature name params retTy => do
      let params ← params.mapM (m := ElabM q₀) fun ⟨n, t⟩ => return ⟨n, ← t.zonk q₀⟩
      return .signature name params (← retTy.zonk q₀)
  | .localVar name ctxNames ty => do
      return .localVar name ctxNames (← ty.zonk q₀)
  | .typeOnly ctxNames ty => do
      return .typeOnly ctxNames (← ty.zonk q₀)
  | h@(.hole _ _ _) => return h

public def resolveHoleHovers : ElabM q₀ Unit := do
  let st ← get
  let mut newHovers : Array HoverInfo := Array.emptyWithCapacity st.hovers.size
  for h in st.hovers do
    let resolved ← match h.hover with
      | .hole metaId ctxNames ty => resolveHoleHover q₀ metaId ctxNames ty
      | other => zonkHover q₀ other
    newHovers := newHovers.push { h with hover := resolved }
  modify fun st => { st with hovers := newHovers }

end Qdt
