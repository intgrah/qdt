import Qdt.Control
import Qdt.Nbe
import Qdt.Quote

namespace Qdt

open Lean (Name)

private def ClosTy.openAt {n} (clos : ClosTy n) : TermM (n + 1) (VTy (n + 1)) :=
  let ⟨env, body⟩ := clos
  body.eval (env.weaken.cons (VTm.varAt n))

private def ClosTm.openAt {n} (clos : ClosTm n) : TermM (n + 1) (VTm (n + 1)) :=
  let ⟨env, body⟩ := clos
  body.eval (env.weaken.cons (VTm.varAt n))

private def ClosTy.applyArg {n} (clos : ClosTy n) (arg : VTm n) : MetaM (VTy n) :=
  let ⟨env, body⟩ := clos
  body.eval (.cons arg env)

mutual

private partial def VTm.typeOf {n} : VTm n → TermM n (VTy n)
  | .u' i => return .u i.succ
  | .pi' x dom cod => do
      let domTy ← dom.typeOf
      let .u domLevel := domTy
        | throw (.msg "typeOf pi': domain is not a type")
      let domVal ← doEl dom
      let tctx ← read
      let tctx' := tctx.bind x domVal
      let codVal ← cod.openAt tctx'
      let codTy ← codVal.typeOf tctx'
      let .u codLevel := codTy
        | throw (.msg "typeOf pi': codomain is not a type")
      return .u (Universe.max domLevel codLevel |>.normalise)
  | .lam ⟨x, dom⟩ body => do
      let tctx ← read
      let tctx' := tctx.bind x dom
      let bodyVal ← body.openAt tctx'
      let bodyTy ← bodyVal.typeOf tctx'
      let clos := ⟨tctx.env, ← bodyTy.quote⟩
      return .pi ⟨x, dom⟩ clos
  | .neutral ne => ne.typeOf

private partial def Neutral.typeOf {n} : Neutral n → TermM n (VTy n)
  | ⟨hd, sp⟩ => do
      let hdTy ← hd.typeOf
      sp.typeOf (.neutral ⟨hd, .nil⟩) hdTy

private partial def Head.typeOf {n} : Head n → TermM n (VTy n)
  | .var lvl => do
      let tctx ← read
      return tctx.ctx.lookup lvl.rev
  | .const name us => do
      let some info ← fetchConstantInfo name
        | throw (.msg s!"typeOf: unknown constant {name}")
      let ty := info.ty.substLevels (info.univParams.zip us)
      ty.eval .nil

private partial def Spine.typeOf {n} (currentVal : VTm n) (headTy : VTy n) : Spine n → TermM n (VTy n)
  | .nil => return headTy
  | .app sp arg => do
      let .neutral ne := currentVal
        | throw (.msg "typeOf app: expected neutral")
      let fnTy ← sp.typeOf (.neutral ⟨ne.head, sp⟩) headTy
      let .pi _ clos := fnTy
        | throw (.msg "typeOf app: expected function type")
      clos.applyArg arg
  | .proj sp i => do
      let .neutral ne := currentVal
        | throw (.msg "typeOf proj: expected neutral")
      let partialVal := VTm.neutral ⟨ne.head, sp⟩
      let structTy ← sp.typeOf partialVal headTy
      structTy.projTy partialVal i

private partial def VTy.projTy {n} (structVal : VTm n) (i : Nat) : VTy n → TermM n (VTy n)
  | .el ⟨.const indName us, sp⟩ => do
      let some indInfo ← fetchInductive indName
        | throw (.msg s!"projTy: unknown inductive {indName}")
      if h : 0 < indInfo.numMinors then
        let ctorName := indInfo.ctorNames[0]
        let some ctorInfo ← fetchConstantInfo ctorName
          | throw (.msg s!"projTy: unknown constructor {ctorName}")
        let ctorTy := ctorInfo.ty.substLevels (ctorInfo.univParams.zip us)
        let ctorTyV ← ctorTy.eval .nil
        let some args := sp.toAppList
          | throw (.msg "projTy: spine has projections")
        let params := args.take indInfo.numParams
        let ctorTyApplied ← params.foldlM (init := ctorTyV) fun ty arg => do
          let .pi _ clos := ty
            | throw (.msg "projTy: expected pi in ctor type")
          clos.applyArg arg
        getFieldTy structVal ctorTyApplied i
      else throw (.msg "projTy: no constructors")
  | _ => throw (.msg "projTy: expected inductive type")

private partial def getFieldTy {n} (structVal : VTm n) (ty : VTy n) (i : Nat) : TermM n (VTy n) :=
  go 0 ty i
where
  go (fieldIdx : Nat) (ty : VTy n) : Nat → TermM n (VTy n)
    | 0 => match ty with
        | .pi ⟨_, dom⟩ _ => return dom
        | _ => throw (.msg "getFieldTy: expected pi type")
    | i + 1 => match ty with
        | .pi _ clos => do
            let fieldVal ← structVal.proj fieldIdx
            let ty' ← clos.applyArg fieldVal
            go (fieldIdx + 1) ty' i
        | _ => throw (.msg "getFieldTy: expected pi type")

end

def Tm.typeOf {n} (tm : Tm n) : TermM n (VTy n) := do
  let ctx ← read
  let val ← tm.eval ctx.env
  val.typeOf

end Qdt
