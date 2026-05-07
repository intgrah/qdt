module

public import Incremental.ShakeStore
public import Mathlib.Control.Monad.Cont

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]

@[expose] public def ShakeCPS : Build Monad ℭ J where
  cId := inferInstance
  σ := ShakeRT.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q₀ store :=
    let ι₀ := Input.get store.inputs
    runST fun σ => do
      let memos ← ST.mkRef (σ := σ) store.memos
      let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
      let rec fetch (q : ℭ.Q) : ContT (ℭ.R q₀) (ST σ) (ℭ.R q) := fun k => do
        if let some m := (← started.get).get? q then
          k m.value
        else
          let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
          let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
          let input' (i : ℭ.I) : ContT (ℭ.R q₀) (ST σ) (ℭ.V i) := fun ki => do
            let v := ι₀ i
            if !(← inputDeps.get).contains i then
              inputDeps.modify (·.insert i (hash v))
            ki v
          let fetch' (q : ℭ.Q) : ContT (ℭ.R q₀) (ST σ) (ℭ.R q) := fun ki =>
            (fetch q).run fun v => do
              if !(← deps.get).contains q then
                let h := match (← started.get).get? q with
                  | some m => m.hash
                  | none => hash v
                deps.modify (·.insert q h)
              ki v
          let recompute : ST σ (ℭ.R q₀) :=
            (tasks q (ContT (ℭ.R q₀) (ST σ)) input' (fun q₁ _hq => fetch' q₁)).run fun value => do
              let m : ShakeRT.Memo ℭ q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
              started.modify (·.insert q m)
              memos.modify (·.insert q m)
              k value
          let verifyInputDeps (inputDeps : HashMap ℭ.I UInt64) : Bool :=
            inputDeps.all fun i oldHash => hash (ι₀ i) == oldHash
          match (← memos.get).get? q with
          | some m =>
            if !verifyInputDeps m.inputDeps then recompute
            else
              m.deps.toList.foldr (init := do
                started.modify (·.insert q m)
                k m.value
              ) fun (depKey, oldHash) cont =>
                (fetch depKey).run fun _ => do
                  let h := match (← started.get).get? depKey with
                    | some m => m.hash
                    | none => 0
                  if h != oldHash then recompute
                  else cont
          | none => recompute
      termination_by ℭ.wf.wrap q
      decreasing_by all_goals sorry
      return (⟨← (fetch q₀).run pure, sorry⟩, ⟨store.inputs, ← memos.get⟩)

end Incremental
