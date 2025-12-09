import Qdt.Syntax

namespace Qdt

inductive ElabError where
  | msg : String → ElabError
  deriving Repr, Inhabited

abbrev ElabM := StateT Nat (Except ElabError)

def doAdd : VTm → VTm → VTm
  | .intLit n, .intLit m => .intLit (n + m)
  | a, b => .add a b

def doSub : VTm → VTm → VTm
  | .intLit n, .intLit m => .intLit (n - m)
  | a, b => .sub a b

def mkNeutralVar (l : Nat) : Neutral := .mk (.var l) []

mutual
  partial def evalTy (env : Env) : Ty → ElabM VTy
    | .u => return .u
    | .pi x a b => return .pi x (← evalTy env a) env b
    | .sigma x a b => return .sigma x (← evalTy env a) env b
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq e1 e2 a => return .eq (← evalTm env e1) (← evalTm env e2) (← evalTy env a)
    | .el t => do doEl (← evalTm env t)

  partial def evalTm (env : Env) : Tm → ElabM VTm
    | .var idx => do
        let envLen := env.length
        if idx < envLen then
          match env.get? idx with
          | some v => return v
          | none => return .neutral (mkNeutralVar (envLen - idx - 1))
        else
          return .neutral (mkNeutralVar (envLen - idx - 1))
    | .const name => return .neutral (.mk (.const name) [])
    | .lam x a body => return .lam x (← evalTy env a) env body
    | .app f a => do doApp (← evalTm env f) (← evalTm env a)
    | .piHat x a b => return .piHat x (← evalTm env a) env b
    | .sigmaHat x a b => return .sigmaHat x (← evalTm env a) env b
    | .mkSigma a b t u => return .mkSigma none (← evalTy env a) env b (← evalTm env t) (← evalTm env u)
    | .proj1 p => do doProj1 (← evalTm env p)
    | .proj2 p => do doProj2 (← evalTm env p)
    | .unit => return .unit
    | .absurd c e => do doAbsurd (← evalTy env c) (← evalTm env e)
    | .intLit n => return .intLit n
    | .unitHat => return .unitHat
    | .emptyHat => return .emptyHat
    | .intHat => return .intHat
    | .eqHat t u a => return .eqHat (← evalTm env t) (← evalTm env u) (← evalTy env a)
    | .refl a e => return .refl (← evalTy env a) (← evalTm env e)
    | .add a b => do
        match (← evalTm env a, ← evalTm env b) with
        | (.intLit n, .intLit m) => return .intLit (n + m)
        | (a', b') => return .add a' b'
    | .sub a b => do
        match (← evalTm env a, ← evalTm env b) with
        | (.intLit n, .intLit m) => return .intLit (n - m)
        | (a', b') => return .sub a' b'
    | .sorry id ty => return .neutral (.mk (.sorry id (← evalTy env ty)) [])
    | .let _ _ t body => do
        let tv ← evalTm env t
        evalTm (.cons tv env) body

  partial def doEl : VTm → ElabM VTy
    | .piHat x a env' b => do
        let a' ← doEl a
        return .pi x a' env' (.el b)
    | .sigmaHat x a env' b => do
        let a' ← doEl a
        return .sigma x a' env' (.el b)
    | .unitHat => return .unit
    | .emptyHat => return .empty
    | .intHat => return .int
    | .eqHat t u a => return .eq t u a
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

  partial def doAbsurd (c : VTy) : VTm → ElabM VTm
    | .neutral n => return .neutral (n.snoc (.absurd c))
    | _ => throw (.msg "doAbsurd: expected neutral")

  partial def instClosTy (env : Env) (body : Ty) (v : VTm) : ElabM VTy :=
    evalTy (.cons v env) body

  partial def instClosTm (env : Env) (body : Tm) (v : VTm) : ElabM VTm :=
    evalTm (.cons v env) body
end

def lvlToIdx (l : Nat) (x : Nat) : Nat := l - x - 1

def mkVar (l : Nat) : VTm := .neutral (mkNeutralVar l)

mutual
  partial def quoteTy (l : Nat) : VTy → ElabM Ty
    | .u => return .u
    | .pi x a env b => do
        let a' ← quoteTy l a
        let var := mkVar l
        let b' ← quoteTy (l + 1) (← instClosTy env b var)
        return .pi x a' b'
    | .sigma x a env b => do
        let a' ← quoteTy l a
        let var := mkVar l
        let b' ← quoteTy (l + 1) (← instClosTy env b var)
        return .sigma x a' b'
    | .unit => return .unit
    | .empty => return .empty
    | .int => return .int
    | .eq e1 e2 a => return .eq (← quoteTm l e1) (← quoteTm l e2) (← quoteTy l a)
    | .el n => return .el (← quoteNeutral l n)

  partial def quoteTm (l : Nat) : VTm → ElabM Tm
    | .neutral n => quoteNeutral l n
    | .lam x a env body => do
        let var := mkVar l
        let a' ← quoteTy l a
        let body' ← quoteTm (l + 1) (← instClosTm env body var)
        return .lam x a' body'
    | .piHat x a env b => do
        let a' ← quoteTm l a
        let var := mkVar l
        let b' ← quoteTm (l + 1) (← instClosTm env b var)
        return .piHat x a' b'
    | .sigmaHat x a env b => do
        let a' ← quoteTm l a
        let var := mkVar l
        let b' ← quoteTm (l + 1) (← instClosTm env b var)
        return .sigmaHat x a' b'
    | .mkSigma _ aTy env bTy t u => do
        let a ← quoteTy l aTy
        let var := mkVar l
        let b ← quoteTy (l + 1) (← instClosTy env bTy var)
        return .mkSigma a b (← quoteTm l t) (← quoteTm l u)
    | .unit => return .unit
    | .intLit n => return .intLit n
    | .unitHat => return .unitHat
    | .emptyHat => return .emptyHat
    | .intHat => return .intHat
    | .eqHat t u a => return .eqHat (← quoteTm l t) (← quoteTm l u) (← quoteTy l a)
    | .refl a e => return .refl (← quoteTy l a) (← quoteTm l e)
    | .add a b => return .add (← quoteTm l a) (← quoteTm l b)
    | .sub a b => return .sub (← quoteTm l a) (← quoteTm l b)

  partial def quoteNeutral (l : Nat) (n : Neutral) : ElabM Tm := do
    match n.head with
    | .var x => quoteSpine l (Tm.var (lvlToIdx l x)) n.spine
    | .const name => quoteSpine l (Tm.const name) n.spine
    | .sorry id ty => do
        let ty' ← quoteTy l ty
        quoteSpine l (Tm.sorry id ty') n.spine

  partial def quoteSpine (l : Nat) (tm : Tm) : List Frame → ElabM Tm
    | [] => return tm
    | .app a :: rest => do quoteSpine l (.app tm (← quoteTm l a)) rest
    | .proj1 :: rest => quoteSpine l (.proj1 tm) rest
    | .proj2 :: rest => quoteSpine l (.proj2 tm) rest
    | .absurd c :: rest => do quoteSpine l (.absurd (← quoteTy l c) tm) rest
end

end Qdt
