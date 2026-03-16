module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

public structure Salsa.Memo (q : ℭ.Q) where
  value : ℭ.R q
  changedAt : Nat
  verifiedAt : Nat
  deps : Array ℭ.Q
  inputDeps : Array ℭ.I
  hash : UInt64 := Hashable.hash value
  hash_value : Hashable.hash value = hash := by rfl

public structure Salsa.Store (J : Type) where
  inputs : J
  revision : Nat
  memos : DHashMap ℭ.Q (Salsa.Memo ℭ)
  inputRevisions : HashMap ℭ.I Nat

public def Salsa : Build Monad ℭ J where
  σ := Salsa.Store ℭ J
  init store := {
    inputs := store
    revision := 0
    memos := DHashMap.emptyWithCapacity 4096
    inputRevisions := HashMap.emptyWithCapacity 1024
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    let revision := store.revision + 1
    let inputs := Input.set store.inputs i v
    let inputRevisions := store.inputRevisions.insert i revision
    { store with inputs, revision, inputRevisions }
  build tasks q := fun store =>
    let ι₀ := Input.get store.inputs
    runST fun σ => do
      let memos ← ST.mkRef (σ := σ) store.memos
      let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
        let memo? := (← memos.get).get? q
        if let some memo := memo? then
          if memo.verifiedAt == store.revision then
            return memo.value
        if let some memo := memo? then do
          let mut clean :=
            memo.inputDeps.all fun i =>
              store.inputRevisions.getD i 0 ≤ memo.verifiedAt
          if clean then
            for dep in memo.deps do
              let _ ← fetch dep
              match (← memos.get).get? dep with
              | some depMemo =>
                if depMemo.changedAt > memo.verifiedAt then
                  clean := false
                  break
              | none =>
                clean := false
                break
          if clean then
            memos.modify (·.insert q { memo with verifiedAt := store.revision })
            return memo.value
        let depsRef ← ST.mkRef (σ := σ) (#[] : Array ℭ.Q)
        let inputDepsRef ← ST.mkRef (σ := σ) (#[] : Array ℭ.I)
        let input' (i : ℭ.I) : ST σ (ℭ.V i) := do
          inputDepsRef.modify (·.push i)
          return ι₀ i
        let fetch' (q : ℭ.Q) : ST σ (ℭ.R q) := do
          let v ← fetch q
          depsRef.modify (·.push q)
          return v
        let value ← tasks ι₀ q (ST σ) input' (fun q' _hq => fetch' q')
        let h := Hashable.hash value
        let changedAt := match memo? with
          | some memo => if h == memo.hash then memo.changedAt else store.revision
          | none => store.revision
        let newMemo : Salsa.Memo ℭ q := {
          value
          hash := h
          changedAt
          verifiedAt := store.revision,
          deps := ← depsRef.get
          inputDeps := ← inputDepsRef.get
        }
        memos.modify (·.insert q newMemo)
        return value
      termination_by (ℭ.wf ι₀).wrap q
      decreasing_by all_goals sorry
      return (← fetch q, { store with memos := ← memos.get })

end Incremental
