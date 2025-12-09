import Qdt.Conv

namespace Qdt

def freshSorryId : ElabM Nat := do
  let id ← get
  modify Nat.succ
  return id

mutual
  partial def checkTy (genv : GlobalEnv) (ctx : Context) (raw : Raw) : ElabM Ty := do
    let rec binders (names : List Name) (a : Raw) (b : Raw)
        (mk : Name → Ty → Ty → Ty) : ElabM Ty := do
      let a' ← checkTy genv ctx a
      let av ← evalTy ctx.env a'
      let rec go (ctx : Context) (ns : List Name) : ElabM Ty :=
        match ns with
        | [] => checkTy genv ctx b
        | x :: xs => do
            let ctx' := ctx.bind x av
            return mk x a' (← go ctx' xs)
      go ctx names
    match raw with
    | .u => return .u
    | .ident x => do
        match ctx.lookupVar x with
        | some (lvl, .u) => return .el (.var (ctx.lvl - lvl - 1))
        | some (_, ty) =>
            let ty' ← quoteTy ctx.lvl ty
            throw (.msg s!"Variable {x} has type {repr ty'}, expected U")
        | none =>
            match GlobalEnv.find? genv x with
            | some entry =>
                if ← eqTy genv ctx.lvl entry.ty .u then
                  return .el (.const x)
                else
                  let ty' ← quoteTy ctx.lvl entry.ty
                  throw (.msg s!"Global {x} has type {repr ty'}, expected U")
            | none => throw (.msg s!"Type variable not in scope: {x}")
    | .pi group b => binders group.fst group.snd b (fun x a b => .pi x a b)
    | .arrow a b => binders [none] a b (fun x a b => .pi x a b)
    | .sigma group b => binders group.fst group.snd b (fun x a b => .sigma x a b)
    | .prod a b => binders [none] a b (fun x a b => .sigma x a b)
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq a b => do
        let (a', ty) ← inferTm genv ctx a
        return .eq a' (← checkTm genv ctx b ty) (← quoteTy ctx.lvl ty)
    | raw@(.app _ _) | raw@(.ann _ _) | raw@(.let _ _ _ _) | raw@(.proj1 _) | raw@(.proj2 _) =>
        return .el (← checkTm genv ctx raw .u)
    | raw =>
        throw (.msg s!"Expected a type, but got: {repr raw}")

  partial def checkTm (genv : GlobalEnv) (ctx : Context) (raw : Raw) (ty : VTy) :
      ElabM Tm := do
    let ty ← forceTy genv ty
    match raw, ty with
    | (.lam [] body), ty => checkTm genv ctx body ty
    | (.lam ((x, aAnn) :: rest) body), .pi _ aTy env bTy => do
        match aAnn with
        | some aAnnRaw =>
            let a' ← checkTy genv ctx aAnnRaw
            let aVal ← evalTy ctx.env a'
            convTy genv ctx aTy aVal
        | none => pure ()
        let var := VTm.neutral (.mk (.var ctx.lvl) [])
        let ctx' := ctx.bind x aTy
        let bVal ← instClosTy env bTy var
        let body' ← checkTm genv ctx' (.lam rest body) bVal
        return .lam x (← quoteTy ctx.lvl aTy) body'
    | .pair a b, .sigma _ aTy env bTy => do
        let a' ← checkTm genv ctx a aTy
        let aVal ← evalTm ctx.env a'
        let bTyVal ← instClosTy env bTy aVal
        let b' ← checkTm genv ctx b bTyVal
        let aTy' ← quoteTy ctx.lvl aTy
        let var := VTm.neutral (.mk (.var ctx.lvl) [])
        let bTy' ← quoteTy (ctx.lvl + 1) (← instClosTy env bTy var)
        return .mkSigma aTy' bTy' a' b'
    | .refl e, .eq e1 e2 a => do
        let e' ← checkTm genv ctx e a
        let eVal ← evalTm ctx.env e'
        if !(← eqTm genv ctx.lvl e1 e2) then
          throw (.msg "refl: sides of equality are not definitionally equal")
        if !(← eqTm genv ctx.lvl eVal e1) then
          throw (.msg "refl: term does not match the sides of the equality")
        return .refl (← quoteTy ctx.lvl a) e'
    | .unit, .unit => return .unit
    | .absurd e, ty => return .absurd (← quoteTy ctx.lvl ty) (← checkTm genv ctx e .empty)
    | .sorry, ty => do
        let id ← freshSorryId
        return .sorry id (← quoteTy ctx.lvl ty)
    | .let x tyOpt t body, expectedTy => do
        match tyOpt with
        | some tyRaw =>
            let ty' ← checkTy genv ctx tyRaw
            let tyVal ← evalTy ctx.env ty'
            let t' ← checkTm genv ctx t tyVal
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tyVal tVal
            let body' ← checkTm genv ctx' body expectedTy
            return .let x ty' t' body'
        | none =>
            let (t', tTy) ← inferTm genv ctx t
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tTy tVal
            let body' ← checkTm genv ctx' body expectedTy
            return .let x (← quoteTy ctx.lvl tTy) t' body'
    | .ann e tyRaw, expectedTy => do
        let ty' ← checkTy genv ctx tyRaw
        let tyVal ← evalTy ctx.env ty'
        convTy genv ctx expectedTy tyVal
        checkTm genv ctx e tyVal
    | raw, ty => do
        let (t', inferredTy) ← inferTm genv ctx raw
        convTy genv ctx ty inferredTy
        return t'

  partial def inferTm (genv : GlobalEnv) (ctx : Context) : Raw → ElabM (Tm × VTy) :=
    let binders (group : List Name × Raw) (b : Raw)
        (mk : Name → Tm → Tm → Tm) : ElabM (Tm × VTy) := do
      let a' ← checkTm genv ctx group.snd .u
      let aVal ← evalTm ctx.env a'
      let aEl ← doEl aVal
      let rec go (ctx : Context) : List Name → ElabM (Tm × VTy)
        | [] => inferTm genv ctx b
        | x :: xs => do
            let ctx' := ctx.bind x aEl
            let (b', bTy) ← go ctx' xs
            convTy genv ctx' bTy .u
            return (mk x a' b', .u)
      go ctx group.fst
    fun raw =>
    match raw with
    | .ident x => do
        match ctx.lookupVar x with
        | some (lvl, ty) => return (.var (ctx.lvl - lvl - 1), ty)
        | none =>
            match GlobalEnv.find? genv x with
            | some entry => return (.const x, entry.ty)
            | none => throw (.msg s!"Variable not in scope: {x}")
    | .app f a => do
        let (f', fTy) ← inferTm genv ctx f
        match ← forceTy genv fTy with
        | .pi _ aTy env bTy =>
            let a' ← checkTm genv ctx a aTy
            let aVal ← evalTm ctx.env a'
            let bVal ← instClosTy env bTy aVal
            return (.app f' a', bVal)
        | _ => throw (.msg s!"Application: expected function type")
    | .proj1 p => do
        let (p', pTy) ← inferTm genv ctx p
        match ← forceTy genv pTy with
        | .sigma _ a _ _ => return (.proj1 p', a)
        | _ => throw (.msg "proj1: expected sigma type")
    | .proj2 p => do
        let (p', pTy) ← inferTm genv ctx p
        match ← forceTy genv pTy with
        | .sigma _ _ env bTy =>
            let proj1Tm := Tm.proj1 p'
            let proj1Val ← evalTm ctx.env proj1Tm
            let bVal ← instClosTy env bTy proj1Val
            return (.proj2 p', bVal)
        | _ => throw (.msg "proj2: expected sigma type")
    | .unitTm => return (.unit, .unit)
    | .intLit n => return (.intLit n, .int)
    | .let x tyOpt t body => do
        match tyOpt with
        | some tyRaw =>
            let ty' ← checkTy genv ctx tyRaw
            let tyVal ← evalTy ctx.env ty'
            let t' ← checkTm genv ctx t tyVal
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tyVal tVal
            let (body', bodyTy) ← inferTm genv ctx' body
            return (.let x ty' t' body', bodyTy)
        | none =>
            let (t', tTy) ← inferTm genv ctx t
            let tVal ← evalTm ctx.env t'
            let ctx' := ctx.define x tTy tVal
            let (body', bodyTy) ← inferTm genv ctx' body
            return (.let x (← quoteTy ctx.lvl tTy) t' body', bodyTy)
    | .lam [] body => inferTm genv ctx body
    | .lam ((_, none) :: _) _ =>
        throw (.msg "Cannot infer type of unannotated lambda, no unifier :(")
    | .lam ((x, some tyRaw) :: rest) body => do
        let a' ← checkTy genv ctx tyRaw
        let aVal ← evalTy ctx.env a'
        let ctx' := ctx.bind x aVal
        let (body', bVal) ← inferTm genv ctx' (.lam rest body)
        let b' ← quoteTy ctx'.lvl bVal
        return (.lam x a' body', .pi x aVal ctx.env b')
    | .refl e => do
        let (e', eTy) ← inferTm genv ctx e
        let eVal ← evalTm ctx.env e'
        return (.refl (← quoteTy ctx.lvl eTy) e', .eq eVal eVal eTy)
    | .pair a b => do
        let (a', aTy) ← inferTm genv ctx a
        let ctx' := ctx.bind none aTy
        let (b', bTy) ← inferTm genv ctx b
        let aTy' ← quoteTy ctx.lvl aTy
        let bTy' ← quoteTy ctx'.lvl bTy
        return (.mkSigma aTy' bTy' a' b', .sigma none aTy ctx.env bTy')
    | .unit => return (.unitHat, .u)
    | .empty => return (.emptyHat, .u)
    | .int => return (.intHat, .u)
    | .absurd _ => throw (.msg "Cannot infer type of absurd")
    | .eq a b => do
        let (a', aTy) ← inferTm genv ctx a
        let b' ← checkTm genv ctx b aTy
        let aTy' ← quoteTy ctx.lvl aTy
        return (.eqHat a' b' aTy', .u)
    | .pi group b => binders group b (fun x a b => .piHat x a b)
    | .arrow a b => binders ([none], a) b (fun x a b => .piHat x a b)
    | .sigma group b => binders group b (fun x a b => .sigmaHat x a b)
    | .prod a b => binders ([none], a) b (fun x a b => .sigmaHat x a b)
    | .add a b => return (.add (← checkTm genv ctx a .int) (← checkTm genv ctx b .int), .int)
    | .sub a b => return (.sub (← checkTm genv ctx a .int) (← checkTm genv ctx b .int), .int)
    | .ann e ty => do
        let ty' ← checkTy genv ctx ty
        let tyVal ← evalTy ctx.env ty'
        return (← checkTm genv ctx e tyVal, tyVal)
    | .u => throw (.msg "Cannot infer type of Type")
    | .sorry => throw (.msg "Cannot infer type of sorry")
end

def elabProgramM (program : RawProgram) : ElabM (List (String × Tm × Ty)) := do
  let rec go (acc : List (String × Tm × Ty)) (ctx : Context) (genv : GlobalEnv)
      (items : RawProgram) : ElabM (List (String × Tm × Ty)) :=
    match items with
    | [] => return acc.reverse
    | RawItem.defn name body :: rest => do
        let (term, tyVal) ← inferTm genv ctx body
        let termVal ← evalTm ctx.env term
        let genv' := GlobalEnv.add genv name tyVal termVal
        let tyOut ← quoteTy 0 tyVal
        let ctx' := ctx.define name tyVal termVal
        go ((name, term, tyOut) :: acc) ctx' genv' rest
    | RawItem.example body :: rest => do
        let (term, tyVal) ← inferTm genv ctx body
        let termVal ← evalTm ctx.env term
        let _ ← quoteTm 0 termVal
        let _ ← quoteTy 0 tyVal
        go acc ctx genv rest
  go [] Context.empty GlobalEnv.empty program

def elabProgram (program : RawProgram) : Except ElabError (List (String × Tm × Ty)) :=
  match (elabProgramM program).run 0 with
  | .ok (result, _) => .ok result
  | .error e => .error e

end Qdt
