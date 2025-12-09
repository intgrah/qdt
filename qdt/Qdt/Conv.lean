import Qdt.Context

namespace Qdt

partial def applySpine (v : VTm) : List Frame → ElabM VTm
  | [] => return v
  | .app a :: rest => do applySpine (← doApp v a) rest
  | .proj1 :: rest => do applySpine (← doProj1 v) rest
  | .proj2 :: rest => do applySpine (← doProj2 v) rest
  | .absurd c :: rest => do applySpine (← doAbsurd c v) rest

partial def forceNeutral (genv : GlobalEnv) (n : Neutral) : ElabM (Option VTm) :=
  match n.head with
  | .const name =>
      match GlobalEnv.unfold genv name with
      | some v => return some (← applySpine v n.spine)
      | none => return none
  | .var _ => return none
  | .sorry _ _ => return none

partial def forceTy (genv : GlobalEnv) : VTy → ElabM VTy
  | .el n => do
      match ← forceNeutral genv n with
      | some v => forceTy genv (← doEl v)
      | none => return .el n
  | ty => return ty

mutual
  partial def eqTy (genv : GlobalEnv) (l : Nat) : VTy → VTy → ElabM Bool
    | .u, .u => return true
    | .pi _ a1 env1 b1, .pi _ a2 env2 b2 => do
        if !(← eqTy genv l a1 a2) then
          return false
        let var := mkVar l
        eqTy genv (l + 1) (← instClosTy env1 b1 var) (← instClosTy env2 b2 var)
    | .sigma _ a1 env1 b1, .sigma _ a2 env2 b2 => do
        if !(← eqTy genv l a1 a2) then
          return false
        let var := mkVar l
        eqTy genv (l + 1) (← instClosTy env1 b1 var) (← instClosTy env2 b2 var)
    | .unit, .unit => return true
    | .empty, .empty => return true
    | .int, .int => return true
    | .eq e1 e2 a, .eq e1' e2' a' =>
        return (← eqTm genv l e1 e1') && (← eqTm genv l e2 e2') && (← eqTy genv l a a')
    | .el n1, .el n2 => eqNeutral genv l n1 n2
    | .el n, ty
    | ty, .el n => do
        match ← forceNeutral genv n with
        | some v => eqTy genv l (← doEl v) ty
        | none => return false
    | _, _ => return false

  partial def eqTm (genv : GlobalEnv) (l : Nat) : VTm → VTm → ElabM Bool
    | .neutral n1, .neutral n2 => eqNeutral genv l n1 n2
    | .lam _ _ env1 body1, .lam _ _ env2 body2 => do
        let var := mkVar l
        eqTm genv (l + 1) (← instClosTm env1 body1 var) (← instClosTm env2 body2 var)
    | .lam _ _ env body, t
    | t, .lam _ _ env body => do
        let var := mkVar l
        eqTm genv (l + 1) (← instClosTm env body var) (← doApp t var)
    | .mkSigma _ _ _ _ t1 u1, .mkSigma _ _ _ _ t2 u2 =>
        return (← eqTm genv l t1 t2) && (← eqTm genv l u1 u2)
    | .mkSigma _ _ _ _ t u, p
    | p, .mkSigma _ _ _ _ t u => do
        return (← eqTm genv l t (← doProj1 p)) && (← eqTm genv l u (← doProj2 p))
    | .piHat _ a1 env1 b1, .piHat _ a2 env2 b2 => do
        if !(← eqTm genv l a1 a2) then
          return false
        let var := mkVar l
        eqTm genv (l + 1) (← instClosTm env1 b1 var) (← instClosTm env2 b2 var)
    | .sigmaHat _ a1 env1 b1, .sigmaHat _ a2 env2 b2 => do
        if !(← eqTm genv l a1 a2) then
          return false
        let var := mkVar l
        eqTm genv (l + 1) (← instClosTm env1 b1 var) (← instClosTm env2 b2 var)
    | .unit, .unit => return true
    | .intLit n1, .intLit n2 => return n1 == n2
    | .unitHat, .unitHat => return true
    | .emptyHat, .emptyHat => return true
    | .intHat, .intHat => return true
    | .eqHat t1 u1 a1, .eqHat t2 u2 a2 =>
        return (← eqTm genv l t1 t2) && (← eqTm genv l u1 u2) && (← eqTy genv l a1 a2)
    | .refl a1 e1, .refl a2 e2 =>
        return (← eqTy genv l a1 a2) && (← eqTm genv l e1 e2)
    | .add a1 b1, .add a2 b2 =>
        return (← eqTm genv l a1 a2) && (← eqTm genv l b1 b2)
    | .sub a1 b1, .sub a2 b2 =>
        return (← eqTm genv l a1 a2) && (← eqTm genv l b1 b2)
    | .neutral n, t
    | t, .neutral n => do
        match ← forceNeutral genv n with
        | some v => eqTm genv l v t
        | none => return false
    | _, _ => return false

  partial def eqNeutral (genv : GlobalEnv) (l : Nat) : Neutral → Neutral → ElabM Bool
    | .mk h1 sp1, .mk h2 sp2 => do
        if (← eqHead h1 h2) && (← eqSpine genv l sp1 sp2) then
          return true
        else
          match (← forceNeutral genv (.mk h1 sp1), ← forceNeutral genv (.mk h2 sp2)) with
          | (some v1, some v2) => eqTm genv l v1 v2
          | (some v1, none) => eqTm genv l v1 (.neutral (.mk h2 sp2))
          | (none, some v2) => eqTm genv l (.neutral (.mk h1 sp1)) v2
          | (none, none) => return false

  partial def eqHead : Head → Head → ElabM Bool
    | .var x, .var y => return x == y
    | .const n1, .const n2 => return n1 == n2
    | .sorry id1 _, .sorry id2 _ => return id1 == id2
    | _, _ => return false

  partial def eqSpine (genv : GlobalEnv) (l : Nat) : List Frame → List Frame → ElabM Bool
    | [], [] => return true
    | f1 :: rest1, f2 :: rest2 =>
        return (← eqFrame genv l f1 f2) && (← eqSpine genv l rest1 rest2)
    | _, _ => return false

  partial def eqFrame (genv : GlobalEnv) (l : Nat) : Frame → Frame → ElabM Bool
    | .app a1, .app a2 => eqTm genv l a1 a2
    | .proj1, .proj1 => return true
    | .proj2, .proj2 => return true
    | .absurd c1, .absurd c2 => eqTy genv l c1 c2
    | _, _ => return false
end

def convTy (genv : GlobalEnv) (ctx : Context) (a b : VTy) : ElabM Unit := do
  let l := ctx.lvl
  if !(← eqTy genv l a b) then
    let a' ← quoteTy l a
    let b' ← quoteTy l b
    throw (.msg s!"Type mismatch: expected {repr a'}, got {repr b'}")

end Qdt
