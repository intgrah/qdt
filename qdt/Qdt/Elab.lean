import Qdt.Conv

namespace Qdt

mutual
  partial def checkTyBinderGroup (ctx : Context) (names : List Name) (a : Raw) (b : Raw)
      (mk : Name → Ty → Ty → Ty) : ElabM Ty := do
    let a' ← checkTy ctx a
    let av ← evalTy ctx.env a'
    let rec go (ctx : Context) : List Name → ElabM Ty
      | [] => checkTy ctx b
      | x :: xs => do
          let ctx' := ctx.bind x av
          return mk x a' (← go ctx' xs)
    go ctx names

  partial def checkTy (ctx : Context) : Raw → ElabM Ty
    | .u => return .u
    | .ident x => do
        match ctx.lookupVar x with
        | some (lvl, .u) => return .el (.var (ctx.lvl - lvl - 1))
        | some (_, ty) =>
            let ty' ← quoteTy ctx.lvl ty
            throw (.msg s!"Variable {x} has type {repr ty'}, expected U")
        | none => throw (.msg s!"Type variable not in scope: {x}")
    | .pi (names, a) b => checkTyBinderGroup ctx names a b (fun x a b => .pi x a b)
    | .arrow a b => return .arrow (← checkTy ctx a) (← checkTy ctx b)
    | .sigma (names, a) b => checkTyBinderGroup ctx names a b (fun x a b => .sigma x a b)
    | .prod a b => return .prod (← checkTy ctx a) (← checkTy ctx b)
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq a b => do
        let (a', ty) ← inferTm ctx a
        return .eq a' (← checkTm ctx b ty) (← quoteTy ctx.lvl ty)
    | raw@(.app _ _) | raw@(.ann _ _) => do
        return .el (← checkTm ctx raw .u)
    | raw => throw (.msg s!"Expected a type, but got: {repr raw}")

  partial def checkTm (ctx : Context) (raw : Raw) (ty : VTy) : ElabM Tm := do
    match raw, ty with
    | .lam [] body, ty => checkTm ctx body ty
    | .lam ((x, aAnn) :: rest) body, .pi _ aTy env bTy => do
        match aAnn with
        | some aAnnRaw =>
            let a' ← checkTy ctx aAnnRaw
            let aVal ← evalTy ctx.env a'
            convTy ctx aTy aVal
        | none => pure ()
        let var := VTm.neutral (.mk (.var ctx.lvl) .nil)
        let ctx' := ctx.bind x aTy
        let bVal ← instClosTy env bTy var
        let b' ← quoteTy ctx'.lvl bVal
        let body' ← checkTm ctx' (.lam rest body) bVal
        return .lam x (← quoteTy ctx.lvl aTy) b' body'
    | .lam ((x, aAnn) :: rest) body, .arrow aTy bTy => do
        match aAnn with
        | some aAnnRaw =>
            let a' ← checkTy ctx aAnnRaw
            let aVal ← evalTy ctx.env a'
            convTy ctx aTy aVal
        | none => pure ()
        let ctx' := ctx.bind x aTy
        let b' ← quoteTy ctx.lvl bTy
        let body' ← checkTm ctx' (.lam rest body) bTy
        return .lam x (← quoteTy ctx.lvl aTy) b' body'
    | .pair a b, .sigma _ aTy env bTy => do
        let a' ← checkTm ctx a aTy
        let aVal ← evalTm ctx.env a'
        let bTyVal ← instClosTy env bTy aVal
        let b' ← checkTm ctx b bTyVal
        let aTy' ← quoteTy ctx.lvl aTy
        let var := VTm.neutral (.mk (.var ctx.lvl) .nil)
        let bTy' ← quoteTy (ctx.lvl + 1) (← instClosTy env bTy var)
        return .mkSigma aTy' bTy' a' b'
    | .pair a b, .prod aTy bTy => do
        let a' ← checkTm ctx a aTy
        let b' ← checkTm ctx b bTy
        let aTy' ← quoteTy ctx.lvl aTy
        let bTy' ← quoteTy ctx.lvl bTy
        return .mkSigma aTy' bTy' a' b'
    | .refl e, .eq e1 e2 a => do
        let e' ← checkTm ctx e a
        let eVal ← evalTm ctx.env e'
        if !(← eqTm ctx.lvl e1 e2) then
          throw (.msg "refl: sides of equality are not definitionally equal")
        if !(← eqTm ctx.lvl eVal e1) then
          throw (.msg "refl: term does not match the sides of the equality")
        return .refl (← quoteTy ctx.lvl a) e'
    | .unit, .unit => return .unit
    | .absurd e, ty => do
        let e' ← checkTm ctx e .empty
        return .absurd (← quoteTy ctx.lvl ty) e'
    | .sorry, ty => return .sorry (← quoteTy ctx.lvl ty)
    | .let x tyOpt t body, expectedTy => do
        match tyOpt with
        | some tyRaw =>
            let ty' ← checkTy ctx tyRaw
            let tyVal ← evalTy ctx.env ty'
            let t' ← checkTm ctx t tyVal
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tyVal tVal
            let body' ← checkTm ctx' body expectedTy
            return .let x ty' t' body'
        | none =>
            let (t', tTy) ← inferTm ctx t
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tTy tVal
            let body' ← checkTm ctx' body expectedTy
            return .let x (← quoteTy ctx.lvl tTy) t' body'
    | .ann e tyRaw, expectedTy => do
        let ty' ← checkTy ctx tyRaw
        let tyVal ← evalTy ctx.env ty'
        convTy ctx expectedTy tyVal
        checkTm ctx e tyVal
    | raw, ty => do
        let (t', inferredTy) ← inferTm ctx raw
        convTy ctx ty inferredTy
        return t'

  partial def inferTmPi (ctx : Context) (names : List Name) (a : Raw) (b : Raw) : ElabM (Tm × VTy) := do
    let (a', aTy) ← inferTm ctx a
    convTy ctx aTy .u
    let aVal ← evalTm ctx.env a'
    let aEl ← doEl ctx.env aVal
    let rec go (ctx : Context) : List Name → ElabM (Tm × VTy)
      | [] => inferTm ctx b
      | x :: xs => do
          let ctx' := ctx.bind x aEl
          let (b', bTy) ← go ctx' xs
          convTy ctx' bTy .u
          return (.piHat x a' b', .u)
    go ctx names

  partial def inferTmSigma (ctx : Context) (names : List Name) (a : Raw) (b : Raw) : ElabM (Tm × VTy) := do
    let (a', aTy) ← inferTm ctx a
    convTy ctx aTy .u
    let aVal ← evalTm ctx.env a'
    let aEl ← doEl ctx.env aVal
    let rec go (ctx : Context) : List Name → ElabM (Tm × VTy)
      | [] => inferTm ctx b
      | x :: xs => do
          let ctx' := ctx.bind x aEl
          let (b', bTy) ← go ctx' xs
          convTy ctx' bTy .u
          return (.sigmaHat x a' b', .u)
    go ctx names

  partial def inferTm (ctx : Context) : Raw → ElabM (Tm × VTy)
    | .ident x => do
        match ctx.lookupVar x with
        | some (lvl, ty) => return (.var (ctx.lvl - lvl - 1), ty)
        | none => throw (.msg s!"Variable not in scope: {x}")
    | .app f a => do
        let (f', fTy) ← inferTm ctx f
        match fTy with
        | .pi _ aTy env bTy =>
            let a' ← checkTm ctx a aTy
            let aVal ← evalTm ctx.env a'
            let bVal ← instClosTy env bTy aVal
            return (.app f' a', bVal)
        | .arrow aTy bTy =>
            let a' ← checkTm ctx a aTy
            return (.app f' a', bTy)
        | _ => throw (.msg s!"Application: expected function type")
    | .proj1 p => do
        let (p', pTy) ← inferTm ctx p
        match pTy with
        | .sigma _ a _ _ => return (.proj1 p', a)
        | .prod a _ => return (.proj1 p', a)
        | _ => throw (.msg "proj1: expected sigma/product type")
    | .proj2 p => do
        let (p', pTy) ← inferTm ctx p
        match pTy with
        | .sigma _ _ env bTy =>
            let proj1Tm := Tm.proj1 p'
            let proj1Val ← evalTm ctx.env proj1Tm
            let bVal ← instClosTy env bTy proj1Val
            return (.proj2 p', bVal)
        | .prod _ b => return (.proj2 p', b)
        | _ => throw (.msg "proj2: expected sigma/product type")
    | .unitTm => return (.unit, .unit)
    | .intLit n => return (.intLit n, .int)
    | .let x tyOpt t body => do
        match tyOpt with
        | some tyRaw =>
            let ty' ← checkTy ctx tyRaw
            let tyVal ← evalTy ctx.env ty'
            let t' ← checkTm ctx t tyVal
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tyVal tVal
            let (body', bodyTy) ← inferTm ctx' body
            return (.let x ty' t' body', bodyTy)
        | none =>
            let (t', tTy) ← inferTm ctx t
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tTy tVal
            let (body', bodyTy) ← inferTm ctx' body
            return (.let x (← quoteTy ctx.lvl tTy) t' body', bodyTy)
    | .lam [] body => inferTm ctx body
    | .lam ((_, none) :: _) _ =>
        throw (.msg "Cannot infer type of unannotated lambda")
    | .lam ((x, some tyRaw) :: rest) body => do
        let a' ← checkTy ctx tyRaw
        let aVal ← evalTy ctx.env a'
        let ctx' := ctx.bind x aVal
        let (body', bVal) ← inferTm ctx' (.lam rest body)
        let b' ← quoteTy ctx'.lvl bVal
        return (.lam x a' b' body', .pi x aVal ctx.env b')
    | .refl e => do
        let (e', eTy) ← inferTm ctx e
        let eVal ← evalTm ctx.env e'
        return (.refl (← quoteTy ctx.lvl eTy) e', .eq eVal eVal eTy)
    | .pair a b => do
        let (a', aTy) ← inferTm ctx a
        let (b', bTy) ← inferTm ctx b
        let aTy' ← quoteTy ctx.lvl aTy
        let bTy' ← quoteTy ctx.lvl bTy
        return (.mkSigma aTy' bTy' a' b', .prod aTy bTy)
    | .unit => return (.unitHat, .u)
    | .empty => return (.emptyHat, .u)
    | .int => return (.intHat, .u)
    | .absurd _ => throw (.msg "Cannot infer type of absurd")
    | .eq a b => do
        let (a', aTy) ← inferTm ctx a
        let b' ← checkTm ctx b aTy
        let aTyQuoted ← quoteTy ctx.lvl aTy
        let code ← tyToCode aTyQuoted
        return (.eqHat code a' b', .u)
    | .pi (names, a) b => inferTmPi ctx names a b
    | .arrow a b => do
        let (a', aTy) ← inferTm ctx a
        convTy ctx aTy .u
        let (b', bTy) ← inferTm ctx b
        convTy ctx bTy .u
        return (.arrowHat a' b', .u)
    | .sigma (names, a) b => inferTmSigma ctx names a b
    | .prod a b => do
        let (a', aTy) ← inferTm ctx a
        convTy ctx aTy .u
        let (b', bTy) ← inferTm ctx b
        convTy ctx bTy .u
        return (.prodHat a' b', .u)
    | .add a b => do
        let a' ← checkTm ctx a .int
        let b' ← checkTm ctx b .int
        return (.add a' b', .int)
    | .sub a b => do
        let a' ← checkTm ctx a .int
        let b' ← checkTm ctx b .int
        return (.sub a' b', .int)
    | .ann e ty => do
        let ty' ← checkTy ctx ty
        let tyVal ← evalTy ctx.env ty'
        let e' ← checkTm ctx e tyVal
        return (e', tyVal)
    | .u => throw (.msg "Cannot infer type of Type")
    | .sorry => throw (.msg "Cannot infer type of sorry")
end

def elabProgram (program : RawProgram) : ElabM (List (String × Tm × Ty)) := do
  let rec go (defs : RawProgram) (acc : List (String × Tm × Ty)) (ctx : Context) : ElabM (List (String × Tm × Ty)) :=
    match defs with
    | [] => return acc.reverse
    | (name, body) :: rest => do
        let (term, tyVal) ← inferTm ctx body
        let termVal ← evalTm ctx.env term
        let termNf ← quoteTm 0 termVal
        let tyNf ← quoteTy 0 tyVal
        let ctx' := ctx.define name tyVal termVal
        go rest ((name, termNf, tyNf) :: acc) ctx'
  go program [] .empty

end Qdt
