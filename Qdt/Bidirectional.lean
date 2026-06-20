module

public import Qdt.Conversion
public import Qdt.Quote
public import Qdt.Unify
public import Qdt.Theory.Substitution.Basic

public section

namespace Qdt

open Lean (Name)
open Frontend (Ast Path)

variable (q₀ : Key)

def freshMeta' {n : Nat} (anchor : Path) (ctx : TermContext n) (expected : VTy n) :
    ElabM q₀ (MVarId × Tm n) := do
  let decl ← currentDecl q₀
  let view := ctx.view
  let ty : Ty view.arity := (← expected.quote q₀).subst view.subst
  let id ← freshMetaId q₀ {
    arity := view.arity
    ctx := view.tys
    ty
    ctxNames := ctx.names
    path := anchor
    decl
  }
  let args : List (Tm n) := view.origLvls.toList.map fun lvl => Tm.var lvl.rev
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
      withReader (fun (c : ElabContext) => { c with univParams := info.univParams }) do
        emitHover q₀ (.signature constName .nil info.ty)
      return
  emitHover q₀ (.localVar name ctx.names (← ty.quote q₀))

public partial def checkAstUniverse : Ast → OptionT (ElabM q₀) Universe
  | .node `Level.zero _ => do return .zero
  | .node `Level.succ cs => do return (← checkAstUniverse cs[0]!).mkSucc
  | .node `Level.max cs => do
      if h : cs.size = 0 then failure
      else
        let last ← checkAstUniverse cs[cs.size - 1]
        cs.extract 0 (cs.size - 1) |>.foldrM (init := last) fun c acc => do
          return (← checkAstUniverse c).mkMax acc
  | .node `Level.name cs => do
      let name := cs[0]!.getName
      let univParams ← getUnivParams q₀
      if name ∈ univParams then return .param name
      else raiseError q₀ (.unboundUniverseVariable name)
  | _ => failure

def checkAstUniverses : Ast → OptionT (ElabM q₀) (List Universe)
  | .node _ cs => cs.toList.mapM (checkAstUniverse q₀)
  | _ => return []

def checkUniverseLevel (level : Universe) : OptionT (ElabM q₀) Unit := do
  let univParams ← getUnivParams q₀
  if let .error n := level.checkParams univParams then
    raiseError q₀ (.unboundUniverseVariable n)

def instantiateLevels (name : Name) (declParams : List Name) (ty : Ty 0) (univs : List Universe) :
    OptionT (ElabM q₀) (Ty 0) := do
  if univs.length != declParams.length then
    raiseError q₀ (.universeArgCountMismatch name declParams.length univs.length)
  return ty.instantiateParams declParams univs

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
          else instantiateLevels q₀ name info.univParams info.ty univs
        return (.const name univs, ← ty.eval q₀ .nil)
    | none => raiseError q₀ (.unboundVariable name)

def forceTy {n} (ty : VTy n) : ElabM q₀ (VTy n) := do
  match ty with
  | .el ne => doEl q₀ (.neutral ne)
  | _ => return ty

partial def insertImplicits {n : Nat} (ctx : TermContext n)
    (fTm : Tm n) (fTy : VTy n) : ElabM q₀ (Tm n × VTy n) := do
  match ← forceTy q₀ fTy with
  | .pi _ .implicit aTy ⟨env, bTy⟩ =>
      let anchor ← currentPath q₀
      let mTm ← freshMeta q₀ anchor ctx aTy
      let mVal ← mTm.eval q₀ ctx.env
      let bTyVal ← bTy.eval q₀ (env.cons mVal)
      insertImplicits ctx (.app fTm mTm) bTyVal
  | _ => return (fTm, fTy)

partial def isExplicitHead : Ast → Bool
  | .node `Term.explicit _ => true
  | .node `Term.app cs => isExplicitHead cs[0]!
  | _ => false

def blockImplicitLambda : Ast → Bool
  | .node `Term.hole _ => true
  | .node `Term.ann _ => true
  | .node `Term.lam #[.node `Binder.implicit _, _] => true
  | ast => isExplicitHead ast

def emitSorryAxiom {n : Nat}
    (ctx : TermContext n)
    (retTy : Ty n) :
    ElabM q₀ (Tm n) := do
  let decl ← currentDecl q₀
  let id ← modifyGet fun s => (s.sorryId, { s with sorryId := s.sorryId + 1 })
  let sorryName := decl.str "_sorry" |>.num id
  let univParams ← getUnivParams q₀
  let sorryUnivs := univParams.map Universe.param
  let view := ctx.view
  let _ ← addConstant q₀ sorryName (.axiom {
    univParams
    ty := Ty.pis view.tys (retTy.subst view.subst)
    synthetic := true
  })
  let args : List (Tm n) := view.origLvls.toList.map fun lvl => Tm.var lvl.rev
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
  | .u' _ | .var _ => return false
  | .const name _ => isSyntheticSorryName q₀ name
  | .lam _ _ ty body => do return (← ty.hasSyntheticSorry) || (← body.hasSyntheticSorry)
  | .app f a => do return (← f.hasSyntheticSorry) || (← a.hasSyntheticSorry)
  | .pi' _ _ a b => do return (← a.hasSyntheticSorry) || (← b.hasSyntheticSorry)
  | .proj _ t => t.hasSyntheticSorry
  | .letE _ ty rhs body => do
      return (← ty.hasSyntheticSorry) || (← rhs.hasSyntheticSorry) || (← body.hasSyntheticSorry)
  | .mvar id => metaIsErrored q₀ id

partial def Ty.hasSyntheticSorry {n} : Ty n → ElabM q₀ Bool
  | .u _ => return false
  | .pi _ _ a b => do return (← a.hasSyntheticSorry) || (← b.hasSyntheticSorry)
  | .el t => t.hasSyntheticSorry
end

mutual
partial def Tm.markMetasErrored {n} : Tm n → ElabM q₀ Unit
  | .u' _ | .var _ | .const _ _ => return
  | .lam _ _ ty body => do ty.markMetasErrored; body.markMetasErrored
  | .app f a => do f.markMetasErrored; a.markMetasErrored
  | .pi' _ _ a b => do a.markMetasErrored; b.markMetasErrored
  | .proj _ t => t.markMetasErrored
  | .letE _ ty rhs body => do
      ty.markMetasErrored; rhs.markMetasErrored; body.markMetasErrored
  | .mvar id => markMetaErrored q₀ id

partial def Ty.markMetasErrored {n} : Ty n → ElabM q₀ Unit
  | .u _ => return
  | .pi _ _ a b => do a.markMetasErrored; b.markMetasErrored
  | .el t => t.markMetasErrored
end

mutual
def Tm.hasExprMVar {n} : Tm n → Bool
  | .u' _ | .var _ | .const _ _ => false
  | .lam _ _ ty body => ty.hasExprMVar || body.hasExprMVar
  | .app f a => f.hasExprMVar || a.hasExprMVar
  | .pi' _ _ a b => a.hasExprMVar || b.hasExprMVar
  | .proj _ t => t.hasExprMVar
  | .letE _ ty rhs body => ty.hasExprMVar || rhs.hasExprMVar || body.hasExprMVar
  | .mvar _ => true

def Ty.hasExprMVar {n} : Ty n → Bool
  | .u _ => false
  | .pi _ _ a b => a.hasExprMVar || b.hasExprMVar
  | .el t => t.hasExprMVar
end

def Constant.hasExprMVar : Constant → Bool
  | .definition info => info.ty.hasExprMVar || info.tm.hasExprMVar
  | .opaque info | .axiom info | .constructor info | .inductive info => info.ty.hasExprMVar
  | .recursor info => info.ty.hasExprMVar || info.recRules.toList.any (·.rhs.hasExprMVar)

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

partial def collectSpineAst : Ast → Ast × List Ast
  | .node `Term.app cs =>
      let (h, as) := collectSpineAst cs[0]!
      (h, as ++ [cs[1]!])
  | other => (other, [])

partial def stripExplicit {n} (explicit : Bool) (k : Nat) (ty : VTy n) : ElabM q₀ (Option (VTy n)) := do
  let rec go (k : Nat) (ty : VTy (n + 1)) : ElabM q₀ (Option (VTy (n + 1))) := do
    match ← forceTy q₀ ty with
    | .pi x .implicit dom ⟨env, codTy⟩ =>
        if explicit then
          if k == 0 then return some (.pi x .implicit dom ⟨env, codTy⟩)
          let cod ← codTy.eval q₀ (env.cons (VTm.varAt n))
          go (k - 1) cod
        else
          if k == 0 then return none
          let cod ← codTy.eval q₀ (env.cons (VTm.varAt n))
          go k cod
    | ty =>
        if k == 0 then return some ty
        match ty with
        | .pi _ _ _ ⟨env, codTy⟩ =>
            let cod ← codTy.eval q₀ (env.cons (VTm.varAt n))
            go (k - 1) cod
        | _ => return none
  match ← go k ty.weaken with
  | none => return none
  | some res =>
      match (← res.quote q₀).rename fun
          | ⟨0, _⟩ => none
          | ⟨v + 1, _⟩ => some ⟨v, by omega⟩ with
      | none => return none
      | some strengthened => return some (← strengthened.eval q₀ (Env.identity n))

def freshInaccessible (base : Name) : ElabM q₀ Name := do
  let i ← modifyGet fun st => (st.inaccessibleId, { st with inaccessibleId := st.inaccessibleId + 1 })
  return mkInaccessible base i

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
  let ctx' ← ctx.defineV q₀ name rhsTyVal rhsVal
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
    (x : Name) (bi : BinderInfo)
    (dom : Ast)
    (cod : Ast) :
    OptionT (ElabM q₀) (Tm n × Universe) := do
  let (domTm, domTy) ← withChild q₀ 0 (withChild q₀ 1 (inferTm ctx dom))
  let .u domLevel := ← OptionT.lift (forceTy q₀ domTy)
    | raiseExpectedType q₀ ctx (← domTy.quote q₀)
  let domVal ← (Ty.el domTm).eval q₀ ctx.env
  withChild q₀ 0 (withChild q₀ 0 (emitType q₀ ctx domVal))
  let ctx' ← ctx.bindV q₀ x domVal
  let (codTm, codTy) ← withChild q₀ 1 (inferTm ctx' cod)
  let .u codLevel := ← OptionT.lift (forceTy q₀ codTy)
    | raiseExpectedType q₀ ctx' (← codTy.quote q₀)
  return (.pi' x bi domTm codTm, domLevel.mkMax codLevel)

partial def checkTyWithLevelCore {n : Nat} (ctx : TermContext n) : Ast → OptionT (ElabM q₀) (Ty n × Universe)
  | .missing => failure
  | .node `Term.hole _ => OptionT.lift do
      let anchor ← currentPath q₀
      let level : Universe := .mvar (← Universe.freshUMVar q₀)
      let (id, tm) ← freshMeta' q₀ anchor ctx (.u level)
      emitHover q₀ (.hole id ctx.names (Ty.u (n := n) level))
      return (.el tm, level)
  | .node `Term.u cs => do
      let level ← checkAstUniverse q₀ cs[0]!
      checkUniverseLevel q₀ level
      emitType q₀ ctx (.u level.mkSucc)
      return (.u level, level.mkSucc)
  | .node `Term.pi cs => do
      let (x, bi, tyAst) ← match cs[0]! with
        | .node `Binder.typed bs => pure (bs[0]!.getName, .explicit, bs[1]!)
        | .node `Binder.implicit bs => pure (bs[0]!.getName, .implicit, bs[1]!)
        | _ => failure
      let (dom, domLevel) ← withChild q₀ 0 (withChild q₀ 1 (checkTyWithLevelCore ctx tyAst))
      let domVal ← dom.eval q₀ ctx.env
      withChild q₀ 0 (withChild q₀ 0 (emitType q₀ ctx domVal))
      let ctx' ← ctx.bindV q₀ x domVal
      let (cod, codLevel) ← withChild q₀ 1 (checkTyWithLevelCore ctx' cs[1]!)
      let piLevel := domLevel.mkMax codLevel
      emitType q₀ ctx (.u piLevel)
      return (.pi x bi dom cod, piLevel)
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      return (.el tm, level)
  | ast => do
      let (tm, ty) ← inferTm ctx ast
      let .u level := ← OptionT.lift (forceTy q₀ ty) | raiseExpectedType q₀ ctx (← ty.quote q₀)
      return (.el tm, level)

public partial def checkTyWithLevel {n : Nat} (ctx : TermContext n) (ast : Ast) : ElabM q₀ (Ty n × Universe) := do
  match ← OptionT.run (checkTyWithLevelCore ctx ast) with
  | some result => return result
  | none => emitSorryTy q₀ ctx

public partial def checkTy {n : Nat} (ctx : TermContext n) (ast : Ast) : ElabM q₀ (Ty n) :=
  return (← checkTyWithLevel ctx ast).fst

public partial def elabAppLoop {n : Nat} (ctx : TermContext n) (expected? : Option (VTy n))
    (explicit : Bool) (nArgs : Nat) (fTm : Tm n) (fTy : VTy n) (rest : List Ast)
    (consumed : Nat) (propagated : Bool) : OptionT (ElabM q₀) (Tm n × VTy n) := do
  let fTy ← OptionT.lift (forceTy q₀ fTy)
  match fTy with
  | .pi _ bi domVTy ⟨env, codTy⟩ =>
      if bi != .explicit && !explicit then
          let anchor ← OptionT.lift (currentPath q₀)
          let mTm ← OptionT.lift (freshMeta q₀ anchor ctx domVTy)
          let mVal ← OptionT.lift (mTm.eval q₀ ctx.env)
          let cod ← OptionT.lift (codTy.eval q₀ (env.cons mVal))
          elabAppLoop ctx expected? explicit nArgs (.app fTm mTm) cod rest consumed propagated
      else
          match rest with
          | argAst :: rest' =>
              let propagated ←
                if propagated then pure true
                else match expected? with
                  | some exp =>
                      OptionT.lift do
                        match ← stripExplicit q₀ explicit rest.length fTy with
                        | some res =>
                          let saved ← get
                          if ← VTy.conv q₀ ctx.ctx exp res then
                            pure true
                          else
                            set saved
                            pure false
                        | none => pure false
                  | none => pure true
              let domVTy ← OptionT.lift (forceTy q₀ domVTy)
              let argPath := List.replicate (nArgs - 1 - consumed) 0 ++ [1]
              let argTm ← OptionT.lift (argPath.foldr (fun k a => withChild q₀ k a) (checkTm ctx domVTy argAst))
              let argVal ← OptionT.lift (argTm.eval q₀ ctx.env)
              let cod ← OptionT.lift (codTy.eval q₀ (env.cons argVal))
              elabAppLoop ctx expected? explicit nArgs (.app fTm argTm) cod rest' (consumed + 1) propagated
          | [] => return (fTm, fTy)
  | _ =>
      match rest with
      | [] => return (fTm, fTy)
      | _ =>
          match fTy with
          | .el (.mk (.mvar _) _) =>
              if (← read).mayPostpone then
                modify fun st => { st with postponeSignal := true }
                failure
              else raiseExpectedFunctionType q₀ ctx (← fTy.quote q₀)
          | _ => raiseExpectedFunctionType q₀ ctx (← fTy.quote q₀)

partial def revertTrailing {n} (ctx : TermContext n) :
    List Ast → Ty n → OptionT (ElabM q₀) (Ty n × List (Tm n))
  | [], expected => return (expected, [])
  | ast :: rest, expected => do
      let (argTm, argTy) ← inferTm ctx ast
      let (restReverted, restTms) ← revertTrailing ctx rest expected
      let abstracted ← OptionT.lift (Ty.kabstract q₀ ctx `_ argTy argTm restReverted)
      return (.pi `_ .explicit (← argTy.quote q₀) abstracted, argTm :: restTms)

partial def buildMotive {n} (ctx : TermContext n) :
    List (Lean.Name × VTy n × Tm n) → Ty n → OptionT (ElabM q₀) (Tm n)
  | [], T => return T.toTm
  | (nm, dty, dval) :: rest, T => do
      let inner ← buildMotive ctx rest T
      let innerAbs ← OptionT.lift (Tm.kabstract q₀ ctx nm dty dval inner)
      return .lam nm .explicit (← dty.quote q₀) innerAbs

partial def elabElimWalk {n} (ctx : TermContext n) (info : RecursorInfo) (pos : Nat)
    (fTy : VTy n) (params : List (Tm n)) (motive? : Option (MVarId × Tm n))
    (minors : List (Ast × VTy n × Tm n)) (discrs : List (Lean.Name × VTy n × Tm n))
    (args : List Ast) :
    OptionT (ElabM q₀)
      (List (Tm n) × Tm n × List (Ast × VTy n × Tm n) × List (Lean.Name × VTy n × Tm n)) := do
  let fTy ← OptionT.lift (forceTy q₀ fTy)
  match fTy with
  | .pi name _ domVTy ⟨env, codTy⟩ =>
      let anchor ← OptionT.lift (currentPath q₀)
      let minorEnd := info.numParams + info.numMotives + info.numMinors
      if pos < info.numParams then
          let mTm ← OptionT.lift (freshMeta q₀ anchor ctx domVTy)
          let cod ← OptionT.lift (codTy.eval q₀ (env.cons (← mTm.eval q₀ ctx.env)))
          elabElimWalk ctx info (pos + 1) cod (params ++ [mTm]) motive? minors discrs args
      else if pos == info.numParams then
          let (id, mTm) ← OptionT.lift (freshMeta' q₀ anchor ctx domVTy)
          let cod ← OptionT.lift (codTy.eval q₀ (env.cons (← mTm.eval q₀ ctx.env)))
          elabElimWalk ctx info (pos + 1) cod params (some (id, mTm)) minors discrs args
      else if pos < minorEnd then
          match args with
          | [] => failure
          | ast :: rest =>
              let placeholder ← OptionT.lift (freshMeta q₀ anchor ctx domVTy)
              let cod ← OptionT.lift (codTy.eval q₀ (env.cons (← placeholder.eval q₀ ctx.env)))
              elabElimWalk ctx info (pos + 1) cod params motive? (minors ++ [(ast, domVTy, placeholder)]) discrs rest
      else if pos < minorEnd + info.numIndices then
          let idxMeta ← OptionT.lift (freshMeta q₀ anchor ctx domVTy)
          let cod ← OptionT.lift (codTy.eval q₀ (env.cons (← idxMeta.eval q₀ ctx.env)))
          elabElimWalk ctx info (pos + 1) cod params motive? minors (discrs ++ [(name, domVTy, idxMeta)]) args
      else
          match args, motive? with
          | ast :: _, some (_, motiveTm) =>
              let majorTm ← checkTm ctx domVTy ast
              return (params, motiveTm, minors, discrs ++ [(name, domVTy, majorTm)])
          | _, _ => failure
  | _ => failure

partial def elabAsElim {n} (ctx : TermContext n) (recTm : Tm n) (info : RecursorInfo)
    (recTy : VTy n) (argAsts : List Ast) (expected : VTy n) :
    OptionT (ElabM q₀) (Tm n × VTy n) := do
  if info.numMotives != 1 then failure
  let (params, motiveTm, minors, discrs) ←
    elabElimWalk ctx info 0 recTy [] none [] [] argAsts
  let trailing := argAsts.drop (info.numMinors + 1)
  let (reverted, trailingTms) ← revertTrailing ctx trailing (← expected.quote q₀)
  let motiveLam ← buildMotive ctx discrs reverted
  let motiveTmVal ← OptionT.lift (motiveTm.eval q₀ ctx.env)
  let motiveLamVal ← OptionT.lift (motiveLam.eval q₀ ctx.env)
  unless ← OptionT.lift (VTm.conv q₀ ctx.ctx motiveTmVal motiveLamVal) do failure
  let minorTms ← minors.mapM fun (ast, ty, ph) => do
    let mt ← OptionT.lift (checkTm ctx ty ast)
    unless ← VTm.conv q₀ ctx.ctx (← ph.eval q₀ ctx.env) (← mt.eval q₀ ctx.env) do failure
    return mt
  let recApp := Tm.apps recTm (params ++ [motiveTm] ++ minorTms ++ discrs.map (·.2.2))
  return (Tm.apps recApp trailingTms, expected)

public partial def elabAppSpine {n : Nat} (ctx : TermContext n) (headAst : Ast)
    (argAsts : List Ast) (expected? : Option (VTy n)) : OptionT (ElabM q₀) (Tm n × VTy n) := do
  let nArgs := argAsts.length
  let zeros := List.replicate nArgs 0
  let headRes : OptionT (ElabM q₀) (Bool × Tm n × VTy n) :=
    match headAst with
    | .node `Term.explicit ecs =>
        match ecs[0]! with
        | .node `Term.ident is =>
            (zeros ++ [0]).foldr (fun k a => withChild q₀ k a)
              (do
                let univs ← checkAstUniverses q₀ is[1]!
                let (tm, ty) ← inferIdent q₀ ctx is[0]!.getName univs
                emitIdentHover q₀ ctx is[0]!.getName tm ty
                return (true, tm, ty))
        | other =>
            (zeros ++ [0]).foldr (fun k a => withChild q₀ k a)
              (do let (tm, ty) ← inferTm ctx other; return (true, tm, ty))
    | .node `Term.ident cs =>
        zeros.foldr (fun k a => withChild q₀ k a)
          (do
            let univs ← checkAstUniverses q₀ cs[1]!
            let (tm, ty) ← inferIdent q₀ ctx cs[0]!.getName univs
            emitIdentHover q₀ ctx cs[0]!.getName tm ty
            return (false, tm, ty))
    | other =>
        zeros.foldr (fun k a => withChild q₀ k a)
          (do let (tm, ty) ← inferTm ctx other; return (false, tm, ty))
  let (explicit, headTm, headTy) ← headRes
  let ordinary := elabAppLoop ctx expected? explicit nArgs headTm headTy argAsts 0 false
  match headTm, expected?, explicit with
  | .const recName _, some exp, false =>
      match ← OptionT.lift (fetchConstant q₀ recName) with
      | some (.recursor info) =>
          let saved ← OptionT.lift get
          elabAsElim ctx headTm info headTy argAsts exp <|> (do OptionT.lift (set saved); ordinary)
      | _ => ordinary
  | _, _, _ => ordinary

public partial def inferTm {n : Nat} (ctx : TermContext n) : Ast → OptionT (ElabM q₀) (Tm n × VTy n)
  | .missing => failure
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses q₀ cs[1]!
      let (tm, ty) ← inferIdent q₀ ctx cs[0]!.getName univs
      emitIdentHover q₀ ctx cs[0]!.getName tm ty
      OptionT.lift (insertImplicits q₀ ctx tm ty)
  | .node `Term.explicit cs =>
      match cs[0]! with
      | .node `Term.ident is =>
          let act : OptionT (ElabM q₀) (Tm n × VTy n) := do
            let univs ← checkAstUniverses q₀ is[1]!
            let (tm, ty) ← inferIdent q₀ ctx is[0]!.getName univs
            emitIdentHover q₀ ctx is[0]!.getName tm ty
            return (tm, ty)
          withChild q₀ 0 act
      | other => withChild q₀ 0 (inferTm ctx other)
  | .node `Term.app cs => do
      let (head, args) := collectSpineAst (.node `Term.app cs)
      elabAppSpine ctx head args none
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
      let ctx' ← ctx.bindV q₀ x aTyVal
      let (bodyTm, bodyTy) ← withChild q₀ 1 (inferTm ctx' cs[1]!)
      let clos := ⟨ctx.env, ← bodyTy.quote q₀⟩
      let resultTy : VTy n := .pi x .explicit aTyVal clos
      emitType q₀ ctx resultTy
      return (.lam x .explicit aTy bodyTm, resultTy)
  | .node `Term.pi cs => do
      let (x, bi, dom) ← match cs[0]! with
        | .node `Binder.typed bs => pure (bs[0]!.getName, .explicit, bs[1]!)
        | .node `Binder.implicit bs => pure (bs[0]!.getName, .implicit, bs[1]!)
        | _ => failure
      let (tm, level) ← inferPi ctx x bi dom cs[1]!
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

partial def checkTmCoreBody {n : Nat} (ctx : TermContext n) (expected : VTy n) : Ast → OptionT (ElabM q₀) (Tm n)
  | .missing => failure
  | .node `Term.explicit cs => do
      let (tm, tyVal) ← elabAppSpine ctx (.node `Term.explicit cs) [] (some expected)
      if !(← VTy.conv q₀ ctx.ctx tyVal expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← tyVal.quote q₀)
      emitType q₀ ctx expected
      return tm
  | .node `Term.ident cs => do
      let univs ← checkAstUniverses q₀ cs[1]!
      let (tm, ty) ← inferIdent q₀ ctx cs[0]!.getName univs
      let (tm, ty) ← OptionT.lift (insertImplicits q₀ ctx tm ty)
      if !(← VTy.conv q₀ ctx.ctx ty expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← ty.quote q₀)
      emitIdentHover q₀ ctx cs[0]!.getName tm ty
      return tm
  | ast@(.node `Term.lam cs) => do
      let body := cs[1]!
      match expected with
      | .pi _ bi a ⟨env, b⟩ =>
        match cs[0]! with
        | .node `Binder.untyped bs =>
          let x := bs[0]!.getName
          withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names (← a.quote q₀))))
          let ctx' ← ctx.bindV q₀ x a
          let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
          let b ← withChild q₀ 1 (checkTmCore ctx' b body)
          emitType q₀ ctx expected
          return .lam x bi (← a.quote q₀) b
        | .node `Binder.typed bs =>
          let x := bs[0]!.getName
          let ann ← OptionT.lift (withChild q₀ 0 (withChild q₀ 1 (checkTy ctx bs[1]!)))
          let annVal : VTy n ← ann.eval q₀ ctx.env
          if !(← VTy.conv q₀ ctx.ctx annVal a) then
            raiseTypeMismatch q₀ ctx (← a.quote q₀) (← annVal.quote q₀)
          withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names (← a.quote q₀))))
          let ctx' ← ctx.bindV q₀ x a
          let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
          let body ← withChild q₀ 1 (checkTmCore ctx' b body)
          emitType q₀ ctx expected
          return .lam x bi (← a.quote q₀) body
        | .node `Binder.implicit bs =>
          if bi != .implicit then
            raiseError q₀ (.binderMismatch ctx.names (← expected.quote q₀))
          let x := bs[0]!.getName
          match bs[1]! with
          | .missing => pure ()
          | annAst =>
            let ann ← OptionT.lift (withChild q₀ 0 (withChild q₀ 1 (checkTy ctx annAst)))
            let annVal : VTy n ← ann.eval q₀ ctx.env
            if !(← VTy.conv q₀ ctx.ctx annVal a) then
              raiseTypeMismatch q₀ ctx (← a.quote q₀) (← annVal.quote q₀)
          withChild q₀ 0 (withChild q₀ 0 (emitHover q₀ (.localVar x ctx.names (← a.quote q₀))))
          let ctx' ← ctx.bindV q₀ x a
          let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
          let body ← withChild q₀ 1 (checkTmCore ctx' b body)
          emitType q₀ ctx expected
          return .lam x .implicit (← a.quote q₀) body
        | _ => failure
      | _ =>
        let (inferredTm, inferredTy) ← inferTm ctx ast
        if !(← VTy.conv q₀ ctx.ctx inferredTy expected) then
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
      let (x, bi, dom) ← match cs[0]! with
        | .node `Binder.typed bs => pure (bs[0]!.getName, .explicit, bs[1]!)
        | .node `Binder.implicit bs => pure (bs[0]!.getName, .implicit, bs[1]!)
        | _ => failure
      let (tm, level) ← inferPi ctx x bi dom cs[1]!
      if !(← expected.conv q₀ ctx.ctx (.u level)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level)
      emitType q₀ ctx expected
      return tm
  | .node `Term.eq cs => do
      let (tm, level) ← checkEq ctx cs[0]! cs[1]!
      if !(← expected.conv q₀ ctx.ctx (.u level)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level)
      emitType q₀ ctx expected
      return tm
  | .node `Term.ann cs => do
      let (tm, ty) ← inferAnn ctx cs[0]! cs[1]!
      if !(← VTy.conv q₀ ctx.ctx ty expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← ty.quote q₀)
      emitType q₀ ctx expected
      return tm
  | .node `Term.u cs => do
      let level ← checkAstUniverse q₀ cs[0]!
      if !(← expected.conv q₀ ctx.ctx (.u level.mkSucc)) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (.u level.mkSucc)
      emitType q₀ ctx expected
      return .u' level
  | .node `Term.app cs => do
      let (head, args) := collectSpineAst (.node `Term.app cs)
      let (tm, tyVal) ← elabAppSpine ctx head args (some expected)
      if !(← VTy.conv q₀ ctx.ctx tyVal expected) then
        raiseTypeMismatch q₀ ctx (← expected.quote q₀) (← tyVal.quote q₀)
      emitType q₀ ctx expected
      return tm
  | _ => failure

partial def checkTmCore {n : Nat} (ctx : TermContext n) (expected : VTy n) (ast : Ast) :
    OptionT (ElabM q₀) (Tm n) := do
  let forced ← OptionT.lift (forceTy q₀ expected)
  match forced with
  | .pi x .implicit a ⟨env, b⟩ =>
      if blockImplicitLambda ast then
        checkTmCoreBody ctx forced ast
      else
        let x ← OptionT.lift (freshInaccessible q₀ x)
        let b ← b.eval q₀ (env.weaken.cons (VTm.varAt n))
        let ctx' ← ctx.bindV q₀ x a
        let body ← checkTmCore ctx' b ast
        return .lam x .implicit (← a.quote q₀) body
  | _ => checkTmCoreBody ctx forced ast

public partial def checkTm {n : Nat} (ctx : TermContext n) (expected : VTy n) (ast : Ast) : ElabM q₀ (Tm n) := do
  match ← OptionT.run (checkTmCore ctx expected ast) with
  | some tm => return tm
  | none =>
      if (← get).postponeSignal then
        modify fun st => { st with postponeSignal := false }
        let anchor ← currentPath q₀
        let ph ← freshMeta q₀ anchor ctx expected
        let univParams ← getUnivParams q₀
        let entry : PostponeEntry :=
          { ctx, expected, ast, placeholder := ph, path := anchor, univParams }
        modify fun st => { st with postponed := st.postponed.push entry }
        return ph
      else emitSorryTm q₀ ctx expected
end

public partial def resumePostponed (mayPost : Bool) : ElabM q₀ Unit := do
  let entries := (← get).postponed
  if entries.isEmpty then return
  modify fun st => { st with postponed := #[] }
  let mut progress := false
  for entry in entries do
    let r ← withReader (fun (c : ElabContext) =>
              { c with path := entry.path, univParams := entry.univParams, mayPostpone := mayPost })
              (OptionT.run (checkTmCore q₀ entry.ctx entry.expected entry.ast))
    match r with
    | some realTm =>
        let pVal ← entry.placeholder.eval q₀ entry.ctx.env
        let rVal ← realTm.eval q₀ entry.ctx.env
        let _ ← VTm.conv q₀ entry.ctx.ctx pVal rVal
        progress := true
    | none =>
        if (← get).postponeSignal then
          modify fun st => { st with postponeSignal := false, postponed := st.postponed.push entry }
        else pure ()
  if progress then resumePostponed mayPost
  else if mayPost then resumePostponed false
  else modify fun st => { st with postponed := #[] }

mutual

public partial def Tm.zonk {n} (q₀ : Key) : Tm n → ElabM q₀ (Tm n)
  | .u' u => return .u' (← Universe.zonk q₀ u)
  | .var i => return .var i
  | .const c us => return .const c (← us.mapM (Universe.zonk q₀))
  | .lam x bi ty body => return .lam x bi (← ty.zonk q₀) (← body.zonk q₀)
  | t@(.app _ _) => do
      let (head, args) := Tm.splitApps t
      let args ← args.mapM (Tm.zonk q₀)
      match head with
      | .mvar id => zonkMVarApp q₀ id args
      | other =>
          let other ← Tm.zonk q₀ other
          return (Tm.apps other args).headBeta
  | .pi' x bi a b => return .pi' x bi (← a.zonk q₀) (← b.zonk q₀)
  | .proj i t => return .proj i (← t.zonk q₀)
  | .letE x ty rhs body =>
      return .letE x (← ty.zonk q₀) (← rhs.zonk q₀) (← body.zonk q₀)
  | .mvar id => zonkMVarApp q₀ id []

private partial def zonkMVarApp {n} (q₀ : Key) (id : MVarId) (args : List (Tm n)) :
    ElabM q₀ (Tm n) := do
  let info ← getMetaInfo q₀ id
  let some body := info.solution | return Tm.apps (.mvar id) args
  let firstA := args.take info.arity
  if h : firstA.length = info.arity then
    let body ← Tm.zonk q₀ body
    return (Tm.apps (body.subst (Subst.fromArgs firstA h)) (args.drop info.arity)).headBeta
  else
    panic! "zonkMVarApp: meta ?{id} applied to {args.length} args, expected ≥ {info.arity}"

public partial def Ty.zonk {n} (q₀ : Key) : Ty n → ElabM q₀ (Ty n)
  | .u u => return .u (← Universe.zonk q₀ u)
  | .pi x bi dom cod => return .pi x bi (← dom.zonk q₀) (← cod.zonk q₀)
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
        emitDiagnosticAt q₀ info.path (.unsolvedMetavariable info.decl i (Ty.pis info.ctx info.ty))
  return hadUnsolved

partial def resolveHoleHover (metaId : MVarId) {n : Nat} (ctxNames : List Name) (ty : Ty n) :
    ElabM q₀ HoverContent := do
  let ty ← ty.zonk q₀
  let info ← getMetaInfo q₀ metaId
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
      let params ← params.mapM fun ⟨n, bi, t⟩ => return ⟨n, bi, ← t.zonk q₀⟩
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
