import Qdt.Context

namespace Qdt

mutual
  partial def eqTy (l : Lvl) : VTy → VTy → ElabM Bool
    | .u, .u => return true
    | .pi _ a1 env1 b1, .pi _ a2 env2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) (← instClosTy env1 b1 var) (← instClosTy env2 b2 var)
    | .arrow a1 b1, .arrow a2 b2 => return (← eqTy l a1 a2) && (← eqTy l b1 b2)
    | .pi _ a1 env1 b1, .arrow a2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) (← instClosTy env1 b1 var) b2
    | .arrow a1 b1, .pi _ a2 env2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) b1 (← instClosTy env2 b2 var)
    | .sigma _ a1 env1 b1, .sigma _ a2 env2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) (← instClosTy env1 b1 var) (← instClosTy env2 b2 var)
    | .prod a1 b1, .prod a2 b2 => return (← eqTy l a1 a2) && (← eqTy l b1 b2)
    | .sigma _ a1 env1 b1, .prod a2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) (← instClosTy env1 b1 var) b2
    | .prod a1 b1, .sigma _ a2 env2 b2 => do
        if !(← eqTy l a1 a2) then return false
        let var := mkVar l
        eqTy (l + 1) b1 (← instClosTy env2 b2 var)
    | .unit, .unit => return true
    | .empty, .empty => return true
    | .int, .int => return true
    | .eq e1 e2 a, .eq e1' e2' a' =>
        return (← eqTm l e1 e1') && (← eqTm l e2 e2') && (← eqTy l a a')
    | .el n1, .el n2 => eqNeutral l n1 n2
    | _, _ => return false

  partial def eqTm (l : Lvl) : VTm → VTm → ElabM Bool
    | .neutral n1, .neutral n2 => eqNeutral l n1 n2
    | .lam _ _ env1 body1, .lam _ _ env2 body2 => do
        let var := mkVar l
        eqTm (l + 1) (← instClosTm env1 body1 var) (← instClosTm env2 body2 var)
    | .lam _ _ env body, t => do
        let var := mkVar l
        eqTm (l + 1) (← instClosTm env body var) (← doApp t var)
    | t, .lam _ _ env body => do
        let var := mkVar l
        eqTm (l + 1) (← doApp t var) (← instClosTm env body var)
    | .mkSigma _ _ _ _ t1 u1, .mkSigma _ _ _ _ t2 u2 =>
        return (← eqTm l t1 t2) && (← eqTm l u1 u2)
    | .mkSigma _ _ _ _ t u, p => do
        return (← eqTm l t (← doProj1 p)) && (← eqTm l u (← doProj2 p))
    | p, .mkSigma _ _ _ _ t u => do
        return (← eqTm l (← doProj1 p) t) && (← eqTm l (← doProj2 p) u)
    | .piHat _ a1 env1 b1, .piHat _ a2 env2 b2 => do
        if !(← eqTm l a1 a2) then return false
        let var := mkVar l
        eqTm (l + 1) (← instClosTm env1 b1 var) (← instClosTm env2 b2 var)
    | .arrowHat a1 b1, .arrowHat a2 b2 =>
        return (← eqTm l a1 a2) && (← eqTm l b1 b2)
    | .sigmaHat _ a1 env1 b1, .sigmaHat _ a2 env2 b2 => do
        if !(← eqTm l a1 a2) then return false
        let var := mkVar l
        eqTm (l + 1) (← instClosTm env1 b1 var) (← instClosTm env2 b2 var)
    | .prodHat a1 b1, .prodHat a2 b2 =>
        return (← eqTm l a1 a2) && (← eqTm l b1 b2)
    | .unit, .unit => return true
    | .intLit n1, .intLit n2 => return n1 == n2
    | .unitHat, .unitHat => return true
    | .emptyHat, .emptyHat => return true
    | .intHat, .intHat => return true
    | .absurd c1 e1, .absurd c2 e2 =>
        return (← eqTy l c1 c2) && (← eqTm l e1 e2)
    | .eqHat a1 t1 u1, .eqHat a2 t2 u2 =>
        return (← eqTm l a1 a2) && (← eqTm l t1 t2) && (← eqTm l u1 u2)
    | .refl a1 e1, .refl a2 e2 =>
        return (← eqTy l a1 a2) && (← eqTm l e1 e2)
    | .add a1 b1, .add a2 b2 =>
        return (← eqTm l a1 a2) && (← eqTm l b1 b2)
    | .sub a1 b1, .sub a2 b2 =>
        return (← eqTm l a1 a2) && (← eqTm l b1 b2)
    | .sorry ty1, .sorry ty2 => eqTy l ty1 ty2
    | _, _ => return false

  partial def eqNeutral (l : Lvl) (n1 n2 : Neutral) : ElabM Bool := do
    if !eqHead n1.head n2.head then return false
    eqSpine l n1.spine n2.spine

  partial def eqHead : Head → Head → Bool
    | .var x, .var y => x == y
    | .global n1, .global n2 => n1 == n2
    | _, _ => false

  partial def eqSpine (l : Lvl) : List Frame → List Frame → ElabM Bool
    | [], [] => return true
    | .app a1 :: rest1, .app a2 :: rest2 =>
        return (← eqTm l a1 a2) && (← eqSpine l rest1 rest2)
    | .proj1 :: rest1, .proj1 :: rest2 => eqSpine l rest1 rest2
    | .proj2 :: rest1, .proj2 :: rest2 => eqSpine l rest1 rest2
    | _, _ => return false
end

def convTy (ctx : Context) (a b : VTy) : ElabM Unit := do
  let l := ctx.lvl
  if !(← eqTy l a b) then
    let a' ← quoteTy l a
    let b' ← quoteTy l b
    throw (.msg s!"Type mismatch: expected {repr a'}, got {repr b'}")

end Qdt
