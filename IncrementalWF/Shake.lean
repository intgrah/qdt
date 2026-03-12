module

public import IncrementalWF.Basic

import Mathlib.Data.PFun

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
  (tasks : Tasks Monad ℭ)

structure Shake.Memo (q₀ : ℭ.Q) where
  value : ℭ.R q₀
  deps : HashMap ℭ.Q UInt64
  inputDeps : HashMap ℭ.I UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

structure Shake.Store where
  inputs : J
  memos : DHashMap ℭ.Q (Memo ℭ)

public def Shake : Build Monad ℭ J where
  σ := Shake.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 4096
  }
  inputs := fun store => Input.get store.inputs
  set i v := fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks store q := runST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let started ← ST.mkRef (σ := σ) (HashSet.emptyWithCapacity 4096)
    let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
      if (← started.get).contains q then
        if let some m := (← memos.get).get? q then
          return m.value
      let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
      let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 4)
      let input' (i : ℭ.I) : ST σ (ℭ.V i) := do
        let v := Input.get store.inputs i
        if !(← inputDeps.get).contains i then
          inputDeps.modify (·.insert i (hash v))
        pure v
      let fetch' (q : ℭ.Q) : ST σ (ℭ.R q) := do
        let v ← fetch q
        if !(← deps.get).contains q then
          let h := match (← memos.get).get? q with
            | some m => m.hash
            | none => hash v
          deps.modify (·.insert q h)
        pure v
      let verifyInputDeps (inputDeps : HashMap ℭ.I UInt64) : Bool :=
        inputDeps.all fun i oldHash => hash (Input.get (ℭ := ℭ) store.inputs i) == oldHash
      let verifyDeps (deps : HashMap ℭ.Q UInt64) : ST σ Bool := do
        for (depKey, oldHash) in deps do
          let _ ← fetch depKey
          let h := match (← memos.get).get? depKey with
            | some m => m.hash
            | none => 0
          if h != oldHash then return false
        return true
      let recompute : ST σ (ℭ.R q) := do
        let value ← tasks (Input.get store.inputs) q (ST σ) input' (fun q _ => fetch' q)
        let m : Shake.Memo ℭ q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
        started.modify (·.insert q)
        memos.modify (·.insert q m)
        return value
      let r ← match (← memos.get).get? q with
        | some m =>
          if verifyInputDeps m.inputDeps && (← verifyDeps m.deps) then
            started.modify (·.insert q)
            pure m.value
          else recompute
        | none => recompute
      return r
    termination_by q
    decreasing_by
      all_goals sorry
    return (⟨← fetch q, sorry⟩, ⟨store.inputs, ← memos.get⟩)

end Incremental
