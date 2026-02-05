import Std.Data.DHashMap
import Std.Data.HashMap
import Std.Data.HashSet

import Qdt.Incremental.Basic
import Qdt.Incremental.Query

namespace Qdt.Incremental

open Std (DHashMap HashMap HashSet)

variable {ε : Type} {Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

def recompute
    (rules : ∀ q, TaskM ε R (R q))
    (store : ∀ q, R q)
    (q : Q) : R q :=
  sorry

def Consistent
    (rules : ∀ q, TaskM ε R (R q))
    (store : ∀ q, R q)
    (isInput : Q → Bool)
    (k : Q) : Prop :=
  if isInput k then True else store k = recompute rules store k

def InputsUnchanged
    (initialStore finalStore : ∀ q, R q)
    (isInput : Q → Bool) : Prop :=
  ∀ k, isInput k → finalStore k = initialStore k

theorem correctness {α : Type}
    (engine : Engine ε R)
    (rules : ∀ q, TaskM ε R (R q))
    (task : TaskM ε R α)
    (initialStore : ∀ q, R q) :
    ∀ (result : α) (engine' : Engine ε R) (finalStore : ∀ q, R q),
      runWithEngine engine rules task = .ok (result, engine') →
      InputsUnchanged initialStore finalStore engine.isInput ∧
      ∀ q, ¬engine.isInput q → Consistent rules finalStore engine.isInput q :=
  sorry

def Reachable
    (rules : ∀ q, TaskM ε R (R q))
    (root : Q)
    (k : Q) : Prop :=
  sorry

def Changed
    (fingerprint : ∀ q, R q → UInt64)
    (oldStore newStore : ∀ q, R q)
    (k : Q) : Prop :=
  fingerprint k (oldStore k) ≠ fingerprint k (newStore k)

def Rebuilt
    (engine : Engine ε R)
    (rules : ∀ q, TaskM ε R (R q))
    (target : Q)
    (k : Q) : Prop :=
  sorry

theorem minimality
    (engine : Engine ε R)
    (rules : ∀ q, TaskM ε R (R q))
    (target : Q)
    (oldStore newStore : ∀ q, R q)
    (changedInputs : HashSet Q)
    (h_changed : ∀ q, changedInputs.contains q ↔ Changed engine.fingerprint oldStore newStore q) :
    ∀ q,
      ¬Reachable rules target q ∨
      (∀ dep, Reachable rules q dep → engine.isInput dep → ¬changedInputs.contains dep) →
      ¬Rebuilt engine rules target q :=
  sorry

structure ValidCache (engine : Engine ε R) (store : ∀ q, R q) : Prop where
  fingerprints_match : ∀ q (memo : Memo R q), engine.cache.get? q = some memo →
    ∀ (dep : Q) (fp : UInt64), memo.deps.get? dep = some fp →
      engine.fingerprint dep (store dep) = fp
  reverseDeps_complete : ∀ q (memo : Memo R q), engine.cache.get? q = some memo →
    ∀ (dep : Q), memo.deps.contains dep →
      match engine.reverseDeps.get? dep with
      | some s => s.contains q
      | none => False

theorem invalidate_sound
    (engine : Engine ε R)
    (changedKeys : HashSet Q)
    (store : ∀ q, R q)
    (h_valid : ValidCache engine store) :
    let engine' := engine.invalidate changedKeys
    ∀ q (memo : Memo R q), engine'.cache.get? q = some memo →
      ∀ changed, changedKeys.contains changed →
        ¬Reachable (ε := ε) (fun _ => pure ()) q changed :=
  sorry

end Qdt.Incremental
