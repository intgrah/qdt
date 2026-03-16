module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

public structure Shake.Memo (q : ℭ.Q) where
  value : ℭ.R q
  deps : HashMap ℭ.Q UInt64
  inputDeps : HashMap ℭ.I UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

public structure Shake.Store (J : Type) where
  inputs : J
  memos : DHashMap ℭ.Q (Memo ℭ)

public def Shake : Build Monad ℭ J where
  σ := Shake.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q := fun store =>
    let ι₀ := Input.get store.inputs
    runST fun σ => do
      let memos ← ST.mkRef (σ := σ) store.memos
      let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
      let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
        if let some m := (← started.get).get? q then
          return m.value
        let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
        let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
        let input' (i : ℭ.I) : ST σ (ℭ.V i) := do
          let v := ι₀ i
          if !(← inputDeps.get).contains i then
            inputDeps.modify (·.insert i (hash v))
          return v
        let fetch' (q : ℭ.Q) : ST σ (ℭ.R q) := do
          let r ← fetch q
          if !(← deps.get).contains q then
            let h := match (← started.get).get? q with
              | some m => m.hash
              | none => hash r
            deps.modify (·.insert q h)
          return r
        let verifyInputDeps (inputDeps : HashMap ℭ.I UInt64) : Bool :=
          inputDeps.all fun i oldHash => hash (ι₀ i) == oldHash
        let verifyDeps (deps : HashMap ℭ.Q UInt64) : ST σ Bool := do
          for (depKey, oldHash) in deps do
            let _ ← fetch depKey
            let h := match (← started.get).get? depKey with
              | some m => m.hash
              | none => 0
            if h != oldHash then return false
          return true
        let recompute : ST σ (ℭ.R q) := do
          let value ← tasks ι₀ q (ST σ) input' (fun q' _hq => fetch' q')
          let m : Shake.Memo ℭ q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
          started.modify (·.insert q m)
          memos.modify (·.insert q m)
          return value
        let r ← match (← memos.get).get? q with
          | some m =>
            if verifyInputDeps m.inputDeps && (← verifyDeps m.deps) then
              started.modify (·.insert q m)
              pure m.value
            else recompute
          | none => recompute
        return r
      termination_by (ℭ.wf ι₀).wrap q
      decreasing_by all_goals sorry
      return (← fetch q, ⟨store.inputs, ← memos.get⟩)

end Incremental
