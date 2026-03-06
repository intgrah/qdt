import Qdt.Control
import Qdt.Nbe
import Qdt.Quote

namespace Qdt

open Lean (Name)



private def ClosTy.openAt {n} (clos : ClosTy n) : MetaM (VTy (n + 1)) :=
  let ⟨env, body⟩ := clos
  body.eval (env.weaken.cons (VTm.varAt n))

private def ClosTm.openAt {n} (clos : ClosTm n) : MetaM (VTm (n + 1)) :=
  let ⟨env, body⟩ := clos
  body.eval (env.weaken.cons (VTm.varAt n))

private def ClosTy.applyArg {n} (clos : ClosTy n) (arg : VTm n) : MetaM (VTy n) :=
  let ⟨env, body⟩ := clos
  body.eval (.cons arg env)

mutual

private partial def VTm.typeOf {n} (ctx : TermContext n) : VTm n → MetaM (VTy n)
  | .u' i => return .u i.succ
  | .pi' x dom cod => do
      let domTy ← dom.typeOf ctx
      let .u domLevel := domTy
        | raiseError (.msg "typeOf pi': domain is not a type")
      let domVal ← doEl dom
      let tctx' := ctx.bind x domVal
      let codVal ← cod.openAt
      let codTy ← codVal.typeOf tctx'
      let .u codLevel := codTy
        | raiseError (.msg "typeOf pi': codomain is not a type")
      return .u (Universe.max domLevel codLevel |>.normalise)
  | .lam ⟨x, dom⟩ body => do
      let tctx' := ctx.bind x dom
      let bodyVal ← body.openAt
      let bodyTy ← bodyVal.typeOf tctx'
      let clos := ⟨ctx.env, ← bodyTy.quote⟩
      return .pi ⟨x, dom⟩ clos
  | .neutral ne => ne.typeOf ctx

private partial def Neutral.typeOf {n} (ctx : TermContext n) : Neutral n → MetaM (VTy n)
  | ⟨hd, sp⟩ => do
      let hdTy ← hd.typeOf ctx
      sp.typeOf ctx (.neutral ⟨hd, .nil⟩) hdTy

private partial def Head.typeOf {n} (ctx : TermContext n) : Head n → MetaM (VTy n)
  | .var lvl => do
      return ctx.ctx.lookup lvl.rev
  | .const name us => do
      let some info ← fetchConstantInfo name
        | raiseError (.msg s!"typeOf: unknown constant {name}")
      let ty := info.ty.substLevels (info.univParams.zip us)
      ty.eval .nil

private partial def Spine.typeOf {n} (ctx : TermContext n) (currentVal : VTm n) (headTy : VTy n) : Spine n → MetaM (VTy n)
  | .nil => return headTy
  | .app sp arg => do
      let .neutral ne := currentVal
        | raiseError (.msg "typeOf app: expected neutral")
      let fnTy ← sp.typeOf ctx (.neutral ⟨ne.head, sp⟩) headTy
      let .pi _ clos := fnTy
        | raiseError (.msg "typeOf app: expected function type")
      clos.applyArg arg
  | .proj sp i => do
      let .neutral ne := currentVal
        | raiseError (.msg "typeOf proj: expected neutral")
      let partialVal := VTm.neutral ⟨ne.head, sp⟩
      let structTy ← sp.typeOf ctx partialVal headTy
      structTy.projTy ctx partialVal i

private partial def VTy.projTy {n} (ctx : TermContext n) (structVal : VTm n) (i : Nat) : VTy n → MetaM (VTy n)
  | .el ⟨.const indName us, sp⟩ => do
      let some indInfo ← fetchInductive indName
        | raiseError (.msg s!"projTy: unknown inductive {indName}")
      if h : 0 < indInfo.numMinors then
        let ctorName := indInfo.ctorNames[0]
        let some ctorInfo ← fetchConstantInfo ctorName
          | raiseError (.msg s!"projTy: unknown constructor {ctorName}")
        let ctorTy := ctorInfo.ty.substLevels (ctorInfo.univParams.zip us)
        let ctorTyV ← ctorTy.eval .nil
        let some args := sp.toAppList
          | raiseError (.msg "projTy: spine has projections")
        let params := args.take indInfo.numParams
        let ctorTyApplied ← params.foldlM (init := ctorTyV) fun ty arg => do
          let .pi _ clos := ty
            | raiseError (.msg "projTy: expected pi in ctor type")
          clos.applyArg arg
        getFieldTy structVal ctorTyApplied i
      else raiseError (.msg "projTy: no constructors")
  | _ => raiseError (.msg "projTy: expected inductive type")

private partial def getFieldTy {n} (structVal : VTm n) (ty : VTy n) (i : Nat) : MetaM (VTy n) :=
  go 0 ty i
where
  go (fieldIdx : Nat) (ty : VTy n) : Nat → MetaM (VTy n)
    | 0 => match ty with
        | .pi ⟨_, dom⟩ _ => return dom
        | _ => raiseError (.msg "getFieldTy: expected pi type")
    | i + 1 => match ty with
        | .pi _ clos => do
            let fieldVal ← structVal.proj fieldIdx
            let ty' ← clos.applyArg fieldVal
            go (fieldIdx + 1) ty' i
        | _ => raiseError (.msg "getFieldTy: expected pi type")

end

def Tm.typeOf {n} (ctx : TermContext n) (tm : Tm n) : MetaM (VTy n) := do
  let val ← tm.eval ctx.env
  val.typeOf ctx

end Qdt
