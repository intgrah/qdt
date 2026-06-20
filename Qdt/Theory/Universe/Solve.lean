module

public import Qdt.Control

@[expose] public section

namespace Qdt
namespace Universe

variable (q₀ : Key)

partial def instantiate (u : Universe) : ElabM q₀ Universe := do
  let σ := (← get).usubst
  let rec go (u : Universe) : Universe :=
    match u with
    | .mvar id =>
      match σ.lookup? id with
      | some u' => go u'
      | none => u
    | _ => u
  return go u

partial def instantiateAll (u : Universe) : ElabM q₀ Universe := do
  let σ := (← get).usubst
  let rec go : Universe → Universe
    | .mvar id =>
      match σ.lookup? id with
      | some u' => go u'
      | none => .mvar id
    | .succ u => .succ (go u)
    | .max u v => .max (go u) (go v)
    | u => u
  return go u

partial def occursAfter (m : UMVarId) (u : Universe) : ElabM q₀ Bool := do
  let u' ← instantiateAll q₀ u
  return u'.FVMVars.contains m

def freshUMVar : ElabM q₀ UMVarId := do
  let st ← get
  set { st with nextUMVar := st.nextUMVar + 1 }
  return st.nextUMVar

partial def zonk (u : Universe) : ElabM q₀ Universe := do
  let σ := (← get).usubst
  let rec go : Universe → Universe
    | .mvar id =>
      match σ.lookup? id with
      | some u' => go u'
      | none => .mvar id
    | .succ u => .succ (go u)
    | .max u v => (Universe.max (go u) (go v)).normalise
    | u => u
  return go u

def assignUMVar (m : UMVarId) (u : Universe) : ElabM q₀ Unit :=
  modify fun st => { st with usubst := st.usubst.insert m u }

def postponeUEq (u v : Universe) : ElabM q₀ Unit :=
  modify fun st => { st with postponedUEqs := st.postponedUEqs.push (u, v) }

def tryApproxSelfMax (u v : Universe) : ElabM q₀ Bool := do
  match v with
  | .max v' (.mvar m) => if u == v' then assignUMVar q₀ m u; return true else return false
  | .max (.mvar m) v' => if u == v' then assignUMVar q₀ m u; return true else return false
  | _ => return false

def tryAbsorbMax (u v : Universe) : ElabM q₀ Bool := do
  match v with
  | .max v' (.mvar m) => if v' ≤ u then assignUMVar q₀ m u; return true else return false
  | .max (.mvar m) v' => if v' ≤ u then assignUMVar q₀ m u; return true else return false
  | _ => return false

def decLevel? : Universe → Option Universe
  | .succ u => some u
  | .zero => none
  | .max u v =>
    match decLevel? u, decLevel? v with
    | some u', some v' => some (.max u' v')
    | _, _ => none
  | _ => none

def splitOffset : Universe → Universe × Nat
  | .succ u => let (b, k) := splitOffset u; (b, k + 1)
  | u => (u, 0)

partial def propagateLE (source target : Universe) : ElabM q₀ Unit := do
  let target ← instantiate q₀ target
  let (tBase, tOff) := splitOffset target
  match tBase with
  | .param _ | .mvar _ | .zero => goLE source 0 tBase tOff
  | _ => pure ()
where
  goLE (v : Universe) (vOff : Nat) (tBase : Universe) (tOff : Nat) : ElabM q₀ Unit := do
    let v ← instantiate q₀ v
    match v with
    | .zero | .param _ => pure ()
    | .succ v' => goLE v' (vOff + 1) tBase tOff
    | .max a b => goLE a vOff tBase tOff; goLE b vOff tBase tOff
    | .mvar id =>
      if (← get).usubst.assigned id || tBase == .mvar id then pure ()
      else if vOff == tOff then assignUMVar q₀ id tBase
      else pure ()

mutual

partial def solveUEq (u v : Universe) : ElabM q₀ Bool := do
  let u := (← instantiateAll q₀ u).normalise
  let v := (← instantiateAll q₀ v).normalise
  solveUEqWhnf u v

partial def solveUEqWhnf (u v : Universe) : ElabM q₀ Bool := do
  if u == v then return true
  match u, v with
  | .mvar m, t =>
    if ← occursAfter q₀ m t then
      postponeUEq q₀ u v; return true
    else
      assignUMVar q₀ m t; return true
  | t, .mvar m =>
    if ← occursAfter q₀ m t then
      postponeUEq q₀ u v; return true
    else
      assignUMVar q₀ m t; return true
  | .succ u', .succ v' => solveUEq u' v'
  | .zero, .max a b => return (← solveUEq .zero a) && (← solveUEq .zero b)
  | .max a b, .zero => return (← solveUEq a .zero) && (← solveUEq b .zero)
  | .succ _, .zero | .zero, .succ _ => return false
  | .succ _, .param _ | .param _, .succ _ => return false
  | .succ u', v =>
    match decLevel? v with
    | some v' => solveUEq u' v'
    | none =>
      if v.hasMVar then postponeUEq q₀ u v; return true
      else return false
  | u, .succ v' =>
    match decLevel? u with
    | some u' => solveUEq u' v'
    | none =>
      if u.hasMVar then postponeUEq q₀ u v; return true
      else return false
  | .zero, .zero => return true
  | .zero, .param _ | .param _, .zero => return false
  | .param i, .param j => return i == j
  | _, _ =>
    if ← tryApproxSelfMax q₀ u v then return true
    if ← tryApproxSelfMax q₀ v u then return true
    if u.hasMVar || v.hasMVar then
      postponeUEq q₀ u v; return true
    else return false

end

partial def solveUEqList : List Universe → List Universe → ElabM q₀ Bool
  | [], [] => return true
  | u :: us, v :: vs => return (← solveUEq q₀ u v) && (← solveUEqList us vs)
  | _, _ => return false

partial def retryPostponed : ElabM q₀ Bool := do
  let queue := (← get).postponedUEqs
  modify fun st => { st with postponedUEqs := #[] }
  let mut failed : Array (Universe × Universe) := #[]
  let mut progress := false
  for (u, v) in queue do
    let beforeQueueSize := (← get).postponedUEqs.size
    let ok ← solveUEq q₀ u v
    let afterQueueSize := (← get).postponedUEqs.size
    if afterQueueSize == beforeQueueSize then progress := true
    if !ok then failed := failed.push (u, v)
  let ok ←
    if progress && !(← get).postponedUEqs.isEmpty then
      retryPostponed
    else
      pure true
  modify fun st => { st with postponedUEqs := st.postponedUEqs ++ failed }
  return ok && failed.isEmpty && (← get).postponedUEqs.isEmpty

partial def absorbStuck : ElabM q₀ Unit := do
  let queue := (← get).postponedUEqs
  modify fun st => { st with postponedUEqs := #[] }
  let mut progress := false
  for (u, v) in queue do
    let u' := (← instantiateAll q₀ u).normalise
    let v' := (← instantiateAll q₀ v).normalise
    if (← tryAbsorbMax q₀ u' v') || (← tryAbsorbMax q₀ v' u') then
      progress := true
    else
      postponeUEq q₀ u v
  if progress then
    let _ ← retryPostponed q₀
    absorbStuck

def stuckConstraints : ElabM q₀ (Array (Universe × Universe)) := do
  let _ ← retryPostponed q₀
  absorbStuck q₀
  let leftover := (← get).postponedUEqs
  modify fun st => { st with postponedUEqs := #[] }
  leftover.mapM fun (u, v) => return (← zonk q₀ u, ← zonk q₀ v)

end Universe
end Qdt
