module

public import Incremental.Shake

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

structure ShakeEState.State where
  memos : DHashMap ℭ.Q (Shake.Memo ℭ)
  started : DHashMap ℭ.Q (Shake.Memo ℭ)
  stack : Array ℭ.Q
  deps : HashMap ℭ.Q UInt64
  inputDeps : HashMap ℭ.I UInt64

public def ShakeEState : Build Monad ℭ J where
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
    let rec fetch (q : ℭ.Q) : StateM (ShakeEState.State ℭ) (ℭ.R q) := do
      if let some m := (← get).started.get? q then
        return m.value
      modify fun s => { s with stack := s.stack.push q }
      let savedDeps := (← get).deps
      let savedInputDeps := (← get).inputDeps
      modify fun s => { s with
        deps := HashMap.emptyWithCapacity 16
        inputDeps := HashMap.emptyWithCapacity 16
      }
      let input' (i : ℭ.I) : StateM (ShakeEState.State ℭ) (ℭ.V i) := do
        let v := ι₀ i
        if !(← get).inputDeps.contains i then
          modify fun s => { s with inputDeps := s.inputDeps.insert i (hash v) }
        pure v
      let fetch' (q : ℭ.Q) : StateM (ShakeEState.State ℭ) (ℭ.R q) := do
        let r ← fetch q
        if !(← get).deps.contains q then
          let h := match (← get).started.get? q with
            | some m => m.hash
            | none => hash r
          modify fun s => { s with deps := s.deps.insert q h }
        pure r
      let verifyInputDeps (inputDeps : HashMap ℭ.I UInt64) : Bool :=
        inputDeps.all fun i oldHash => hash (ι₀ i) == oldHash
      let verifyDeps (deps : HashMap ℭ.Q UInt64) : StateM (ShakeEState.State ℭ) Bool := do
        for (depKey, oldHash) in deps do
          let _ ← fetch depKey
          let h := match (← get).started.get? depKey with
            | some m => m.hash
            | none => 0
          if h != oldHash then return false
        return true
      let recompute : StateM (ShakeEState.State ℭ) (ℭ.R q) := do
        let value ← tasks ι₀ q (StateM (ShakeEState.State ℭ)) input' (fun q₁ _hq => fetch' q₁)
        let m : Shake.Memo ℭ q := { value, deps := (← get).deps, inputDeps := (← get).inputDeps }
        modify fun s => { s with
          started := s.started.insert q m
          memos := s.memos.insert q m
        }
        return value
      let r ← match (← get).memos.get? q with
        | some m =>
          if verifyInputDeps m.inputDeps && (← verifyDeps m.deps) then
            modify fun s => { s with started := s.started.insert q m }
            pure m.value
          else recompute
        | none => recompute
      modify fun s => {
        s with
        deps := savedDeps
        inputDeps := savedInputDeps
        stack := s.stack.pop
      }
      return r
    termination_by (ℭ.wf ι₀).wrap q
    decreasing_by all_goals sorry
    let initState : ShakeEState.State ℭ := {
      memos := store.memos
      started := .emptyWithCapacity 1024
      stack := #[]
      deps := HashMap.emptyWithCapacity 16
      inputDeps := HashMap.emptyWithCapacity 16
    }
    let (r, s) := (fetch q).run initState
    (r, { store with memos := s.memos })

end Incremental
