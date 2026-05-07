module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IntrinsicHash
public import Incremental.ShakeStore

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap)

namespace Shake

variable
  {ℭ : BuildConfig}
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  {H : Type}
  [DecidableEq H]
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks Monad ℭ)

structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : List (ℭ.I × H)
  deps : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q), H)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.1 (ι p.1) = p.2) →
      (∀ p ∈ deps, hR p.1 (compute (inferInstance : Monad Id) tasks ι p.1) = p.2.2) →
      value = compute (inferInstance : Monad Id) tasks ι q

abbrev Cache := DHashMap ℭ.Q (Memo (H := H) hI hR tasks)

abbrev Value (ι : ∀ i, ℭ.V i) (q : ℭ.Q) :=
  { r : ℭ.R q // r = compute (inferInstanceAs (Monad Id)) tasks ι q }

def verifyInputs (ι : ∀ i, ℭ.V i) :
    List (ℭ.I × H) → Bool
  | [] => true
  | ⟨i, h⟩ :: rest =>
    hI i (ι i) = h ∧ verifyInputs ι rest

theorem verifyInputs_iff (ι : ∀ i, ℭ.V i) (l : List (ℭ.I × H)) :
    verifyInputs (H := H) hI ι l = true ↔
      ∀ p ∈ l, hI p.1 (ι p.1) = p.2 := by
  induction l with
  | nil => simp [verifyInputs]
  | cons p rest ih => simp [verifyInputs, ih]

variable {tasks}

def verifyDeps {ι : ∀ i, ℭ.V i} {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Cache (H := H) hI hR tasks) (Value tasks ι q')) :
    (l : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q₀), H)) →
      StateM (Cache (H := H) hI hR tasks)
        (Option (PLift
          (∀ p ∈ l, hR p.1 (compute (inferInstance : Monad Id) tasks ι p.1) = p.2.2)))
  | [] => pure (some ⟨by intro _ h; cases h⟩)
  | ⟨q', hq, h⟩ :: rest => do
      let ⟨v, hv⟩ ← fetch q' hq
      if hh : hR q' v = h then
        match ← verifyDeps fetch rest with
        | none => pure none
        | some ⟨hrest⟩ =>
            pure (some ⟨by
              intro p hp
              cases hp with
              | head =>
                  show hR q' (compute (inferInstance : Monad Id) tasks ι q') = h
                  rw [← hv]; exact hh
              | tail _ ht => exact hrest _ ht⟩)
      else pure none

end Shake

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [∀ i, Hashable (ℭ.V i)]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q] [∀ q, Hashable (ℭ.R q)]
  {H : Type} [DecidableEq H]

public def Shake (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) :
    Build Monad ℭ J where
  cId := inferInstance
  σ := ShakeRT.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q store :=
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
          let value ← tasks q (ST σ) input' (fun q' _hq => fetch' q')
          let m : ShakeRT.Memo ℭ q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
          started.modify (·.insert q m)
          memos.modify (·.insert q m)
          return value
        match (← memos.get).get? q with
        | some m =>
          if verifyInputDeps m.inputDeps && (← verifyDeps m.deps) then
            started.modify (·.insert q m)
            pure m.value
          else recompute
        | none => recompute
      termination_by ℭ.wf.wrap q
      decreasing_by all_goals sorry
      return (⟨← fetch q, sorry⟩, ⟨store.inputs, ← memos.get⟩)

end Incremental
