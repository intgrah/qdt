import Qdt.Syntax

namespace Qdt

inductive ElabError where
  | msg : String → ElabError
  deriving Repr, Inhabited

abbrev ElabM := Except ElabError

def doAdd : VTm → VTm → VTm
  | .intLit n, .intLit m => .intLit (n + m)
  | a, b => .add a b

def doSub : VTm → VTm → VTm
  | .intLit n, .intLit m => .intLit (n - m)
  | a, b => .sub a b

def mkNeutralVar (l : Lvl) : Neutral := .mk (.var l) []

mutual
  partial def evalTy (env : Env) : Ty → ElabM VTy
    | .u => return .u
    | .pi x a b => return .pi x (← evalTy env a) env b
    | .arrow a b => return .arrow (← evalTy env a) (← evalTy env b)
    | .sigma x a b => return .sigma x (← evalTy env a) env b
    | .prod a b => return .prod (← evalTy env a) (← evalTy env b)
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq e1 e2 a => return .eq (← evalTm env e1) (← evalTm env e2) (← evalTy env a)
    | .el t => do doEl env (← evalTm env t)

  partial def evalTm (env : Env) : Tm → ElabM VTm
    | .var idx => do
        let envLen := env.length
        if idx < envLen then
          match env.get? idx with
          | some v => return v
          | none => return .neutral (mkNeutralVar (envLen - idx - 1))
        else
          return .neutral (mkNeutralVar (envLen - idx - 1))
    | .lam x a _ body => return .lam x (← evalTy env a) env body
    | .app f a => do doApp (← evalTm env f) (← evalTm env a)
    | .piHat x a b => return .piHat x (← evalTm env a) env b
    | .arrowHat a b => return .arrowHat (← evalTm env a) (← evalTm env b)
    | .sigmaHat x a b => return .sigmaHat x (← evalTm env a) env b
    | .prodHat a b => return .prodHat (← evalTm env a) (← evalTm env b)
    | .mkSigma a b t u => return .mkSigma none (← evalTy env a) env b (← evalTm env t) (← evalTm env u)
    | .proj1 p => do doProj1 (← evalTm env p)
    | .proj2 p => do doProj2 (← evalTm env p)
    | .unit => return .unit
    | .absurd c e => return .absurd (← evalTy env c) (← evalTm env e)
    | .intLit n => return .intLit n
    | .unitHat => return .unitHat
    | .emptyHat => return .emptyHat
    | .intHat => return .intHat
    | .eqHat a t u => return .eqHat (← evalTm env a) (← evalTm env t) (← evalTm env u)
    | .refl a e => return .refl (← evalTy env a) (← evalTm env e)
    | .add a b => return doAdd (← evalTm env a) (← evalTm env b)
    | .sub a b => return doSub (← evalTm env a) (← evalTm env b)
    | .sorry ty => return .sorry (← evalTy env ty)
    | .let _ _ t body => do
        let tv ← evalTm env t
        evalTm (.cons tv env) body

  partial def doEl (env : Env) : VTm → ElabM VTy
    | .piHat x a env' b => do
        let a' ← doEl env a
        return .pi x a' env' (.el b)
    | .arrowHat a b => return .arrow (← doEl env a) (← doEl env b)
    | .sigmaHat x a env' b => do
        let a' ← doEl env a
        return .sigma x a' env' (.el b)
    | .prodHat a b => return .prod (← doEl env a) (← doEl env b)
    | .unitHat => return .unit
    | .emptyHat => return .empty
    | .intHat => return .int
    | .eqHat a t u => return .eq t u (← doEl env a)
    | .neutral n => return .el n
    | _ => throw (.msg "doEl: expected type code or neutral")

  partial def doApp : VTm → VTm → ElabM VTm
    | .lam _ _ env body, a => instClosTm env body a
    | .neutral n, a => return .neutral (n.snoc (.app a))
    | _, _ => throw (.msg "doApp: expected lambda or neutral")

  partial def doProj1 : VTm → ElabM VTm
    | .mkSigma _ _ _ _ t _ => return t
    | .neutral n => return .neutral (n.snoc .proj1)
    | _ => throw (.msg "doProj1: expected pair or neutral")

  partial def doProj2 : VTm → ElabM VTm
    | .mkSigma _ _ _ _ _ u => return u
    | .neutral n => return .neutral (n.snoc .proj2)
    | _ => throw (.msg "doProj2: expected pair or neutral")

  partial def instClosTy (env : Env) (body : Ty) (v : VTm) : ElabM VTy :=
    evalTy (.cons v env) body

  partial def instClosTm (env : Env) (body : Tm) (v : VTm) : ElabM VTm :=
    evalTm (.cons v env) body
end

def lvlToIdx (l : Lvl) (x : Lvl) : Lvl := l - x - 1

def mkVar (l : Lvl) : VTm := .neutral (mkNeutralVar l)

mutual
  partial def quoteTy (l : Lvl) : VTy → ElabM Ty
    | .u => return .u
    | .pi x a env b => do
        let a' ← quoteTy l a
        let var := mkVar l
        let b' ← quoteTy (l + 1) (← instClosTy env b var)
        return .pi x a' b'
    | .arrow a b => return .arrow (← quoteTy l a) (← quoteTy l b)
    | .sigma x a env b => do
        let a' ← quoteTy l a
        let var := mkVar l
        let b' ← quoteTy (l + 1) (← instClosTy env b var)
        return .sigma x a' b'
    | .prod a b => return .prod (← quoteTy l a) (← quoteTy l b)
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq e1 e2 a => return .eq (← quoteTm l e1) (← quoteTm l e2) (← quoteTy l a)
    | .el n => return .el (← quoteNeutral l n)

  partial def quoteTm (l : Lvl) : VTm → ElabM Tm
    | .neutral n => quoteNeutral l n
    | .lam x a env body => do
        let var := mkVar l
        let a' ← quoteTy l a
        let b' ← quoteTy (l + 1) .u
        let body' ← quoteTm (l + 1) (← instClosTm env body var)
        return .lam x a' b' body'
    | .piHat x a env b => do
        let a' ← quoteTm l a
        let var := mkVar l
        let b' ← quoteTm (l + 1) (← instClosTm env b var)
        return .piHat x a' b'
    | .arrowHat a b => return .arrowHat (← quoteTm l a) (← quoteTm l b)
    | .sigmaHat x a env b => do
        let a' ← quoteTm l a
        let var := mkVar l
        let b' ← quoteTm (l + 1) (← instClosTm env b var)
        return .sigmaHat x a' b'
    | .prodHat a b => return .prodHat (← quoteTm l a) (← quoteTm l b)
    | .mkSigma _ aTy env bTy t u => do
        let a ← quoteTy l aTy
        let var := mkVar l
        let b ← quoteTy (l + 1) (← instClosTy env bTy var)
        return .mkSigma a b (← quoteTm l t) (← quoteTm l u)
    | .unit => return .unit
    | .absurd c e => return .absurd (← quoteTy l c) (← quoteTm l e)
    | .intLit n => return .intLit n
    | .unitHat => return .unitHat
    | .emptyHat => return .emptyHat
    | .intHat => return .intHat
    | .eqHat a t u => return .eqHat (← quoteTm l a) (← quoteTm l t) (← quoteTm l u)
    | .refl a e => return .refl (← quoteTy l a) (← quoteTm l e)
    | .add a b => return .add (← quoteTm l a) (← quoteTm l b)
    | .sub a b => return .sub (← quoteTm l a) (← quoteTm l b)
    | .sorry ty => return .sorry (← quoteTy l ty)

  partial def quoteNeutral (l : Lvl) (n : Neutral) : ElabM Tm := do
    let headTm := match n.head with
      | .var x => Tm.var (lvlToIdx l x)
      | .global _ => panic! "quoteNeutral: globals not yet supported"
    quoteSpine l headTm n.spine

  partial def quoteSpine (l : Lvl) (tm : Tm) : List Frame → ElabM Tm
    | [] => return tm
    | .app a :: rest => do quoteSpine l (.app tm (← quoteTm l a)) rest
    | .proj1 :: rest => quoteSpine l (.proj1 tm) rest
    | .proj2 :: rest => quoteSpine l (.proj2 tm) rest
end

def nfTy (env : Env) (t : Ty) : ElabM Ty := do
  quoteTy env.length (← evalTy env t)

def nfTm (env : Env) (t : Tm) : ElabM Tm := do
  quoteTm env.length (← evalTm env t)

def tyToCode : Ty → ElabM Tm
  | .unit => return .unitHat
  | .empty => return .emptyHat
  | .int => return .intHat
  | .el t => return t
  | .pi x a b => return .piHat x (← tyToCode a) (← tyToCode b)
  | .arrow a b => return .arrowHat (← tyToCode a) (← tyToCode b)
  | .sigma x a b => return .sigmaHat x (← tyToCode a) (← tyToCode b)
  | .prod a b => return .prodHat (← tyToCode a) (← tyToCode b)
  | .eq a b t => return .eqHat (← tyToCode t) a b
  | .u => throw (.msg "tyToCode: U has no code")

end Qdt
