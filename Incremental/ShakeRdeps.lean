module

public import Incremental.ShakeStore

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

structure ShakeRdeps.Store (J : Type) where
  inputs : J
  memos : DHashMap ℭ.Q (ShakeRT.Memo ℭ)
  rdeps : HashMap ℭ.Q (HashSet ℭ.Q)

partial def ShakeRdeps.getTransitiveDependents
    (rdeps : HashMap ℭ.Q (HashSet ℭ.Q)) (keys : HashSet ℭ.Q) : HashSet ℭ.Q :=
  let rec go (worklist : List ℭ.Q) (visited : HashSet ℭ.Q) : HashSet ℭ.Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then go rest visited
        else
          let visited := visited.insert k
          let newWork := (rdeps.getD k ∅).toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go keys.toList (HashSet.emptyWithCapacity keys.size)

def ShakeRdeps.invalidate
    (store : ShakeRdeps.Store ℭ J) (changedKeys : HashSet ℭ.Q) : ShakeRdeps.Store ℭ J :=
  let toInvalidate := getTransitiveDependents ℭ store.rdeps changedKeys
  { store with memos := toInvalidate.fold .erase store.memos }

public def ShakeRdeps (tasks : Tasks Monad ℭ) : Build Monad ℭ J tasks where
  cId := Id.instMonad
  σ := ShakeRdeps.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
    rdeps := HashMap.emptyWithCapacity 1024
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build q store :=
    let ι₀ := Input.get store.inputs
    runST fun σ => do
      let memos ← ST.mkRef (σ := σ) store.memos
      let rdeps ← ST.mkRef (σ := σ) store.rdeps
      let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
      let stack ← ST.mkRef (σ := σ) #[]
      let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
        if let some dependent := (← stack.get).back? then
          rdeps.modify fun rd =>
            rd.alter q (·.getD ∅ |>.insert dependent)
        if let some m := (← started.get).get? q then
          return m.value
        let stk ← stack.get
        stack.set (stk.push q)
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
          let value ← tasks q (ST σ) input' (fun q₁ _hq => fetch' q₁)
          let m : ShakeRT.Memo ℭ q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
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
        stack.modify Array.pop
        return r
      termination_by ℭ.wf.wrap q
      decreasing_by all_goals sorry
      (⟨← fetch q, sorry⟩, ⟨store.inputs, ← memos.get, ← rdeps.get⟩)

end Incremental
