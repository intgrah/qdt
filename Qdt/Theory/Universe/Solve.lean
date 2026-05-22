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
  | .level _ | .mvar _ | .zero => goLE source 0 tBase tOff
  | _ => pure ()
where
  goLE (v : Universe) (vOff : Nat) (tBase : Universe) (tOff : Nat) : ElabM q₀ Unit := do
    let v ← instantiate q₀ v
    match v with
    | .zero | .level _ => pure ()
    | .succ v' => goLE v' (vOff + 1) tBase tOff
    | .max a b => goLE a vOff tBase tOff; goLE b vOff tBase tOff
    | .mvar id =>
      if (← get).usubst.assigned id then pure ()
      else if vOff == tOff then assignUMVar q₀ id tBase
      else pure ()

mutual

partial def solveUEq (u v : Universe) : ElabM q₀ Bool := do
  let u ← instantiate q₀ u
  let v ← instantiate q₀ v
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
  | .succ _, .level _ | .level _, .succ _ => return false
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
  | .zero, .level _ | .level _, .zero => return false
  | .level i, .level j => return i == j
  | _, _ =>
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
  let mut allOk := true
  let mut progress := false
  for (u, v) in queue do
    let beforeQueueSize := (← get).postponedUEqs.size
    let ok ← solveUEq q₀ u v
    let afterQueueSize := (← get).postponedUEqs.size
    if afterQueueSize == beforeQueueSize then progress := true
    if !ok then allOk := false
  if progress && !(← get).postponedUEqs.isEmpty then
    retryPostponed
  else
    return allOk && (← get).postponedUEqs.isEmpty

end Universe
end Qdt
