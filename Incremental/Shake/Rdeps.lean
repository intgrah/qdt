module

public import Incremental.Shake.Store

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
  inputRdeps : HashMap ℭ.I (HashSet ℭ.Q)
  dirty : HashSet ℭ.Q

partial def ShakeRdeps.getTransitiveDependents
    (rdeps : HashMap ℭ.Q (HashSet ℭ.Q)) (seed : HashSet ℭ.Q) : HashSet ℭ.Q :=
  let rec go (worklist : List ℭ.Q) (visited : HashSet ℭ.Q) : HashSet ℭ.Q :=
    match worklist with
    | [] => visited
    | k :: rest =>
        if visited.contains k then go rest visited
        else
          let visited := visited.insert k
          let newWork := (rdeps.getD k ∅).toList.filter (!visited.contains ·)
          go (newWork ++ rest) visited
  go seed.toList (HashSet.emptyWithCapacity seed.size)

def ShakeRdeps.invalidate
    (store : ShakeRdeps.Store ℭ J) (i : ℭ.I) : ShakeRdeps.Store ℭ J :=
  let seed := store.inputRdeps.getD i ∅
  let trans := getTransitiveDependents ℭ store.rdeps seed
  { store with dirty := trans.fold (·.insert ·) store.dirty }

public def ShakeRdeps (tasks : Tasks ℭ) : Build ℭ J tasks Id Id where
  σ := ShakeRdeps.Store ℭ J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
    rdeps := HashMap.emptyWithCapacity 1024
    inputRdeps := HashMap.emptyWithCapacity 64
    dirty := HashSet.emptyWithCapacity 0
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    ShakeRdeps.invalidate ℭ J
      { store with inputs := Input.set store.inputs i v } i
  build q store :=
    let ι₀ := Input.get store.inputs
    runST fun σ => do
      let memos ← ST.mkRef (σ := σ) store.memos
      let rdeps ← ST.mkRef (σ := σ) store.rdeps
      let inputRdeps ← ST.mkRef (σ := σ) store.inputRdeps
      let dirty ← ST.mkRef (σ := σ) store.dirty
      let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
      let stack ← ST.mkRef (σ := σ) #[]
      let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
        if let some parent := (← stack.get).back? then
          rdeps.modify fun rd =>
            rd.alter q (·.getD ∅ |>.insert parent)
        if let some m := (← started.get).get? q then
          return m.value
        if !(← dirty.get).contains q then
          if let some m := (← memos.get).get? q then
            started.modify (·.insert q m)
            return m.value
        let stk ← stack.get
        stack.set (stk.push q)
        let queryDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
        let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 16)
        let input' (i : ℭ.I) : ST σ (ℭ.V i) := do
          let v := ι₀ i
          if !(← inputDeps.get).contains i then
            inputDeps.modify (·.insert i (hash v))
          inputRdeps.modify fun r =>
            r.alter i (·.getD ∅ |>.insert q)
          return v
        let fetch' (q' : ℭ.Q) (hq : ℭ.rel q' q) : ST σ (ℭ.R q') := do
          let r ← fetch q'
          if !(← queryDeps.get).contains q' then
            let h := match (← started.get).get? q' with
              | some m => m.hash
              | none => hash r
            queryDeps.modify (·.insert q' h)
          return r
        let value ← tasks q (ST σ) input' fetch'
        let m : ShakeRT.Memo ℭ q := { value, queryDeps := ← queryDeps.get, inputDeps := ← inputDeps.get }
        started.modify (·.insert q m)
        memos.modify (·.insert q m)
        dirty.modify (·.erase q)
        stack.modify Array.pop
        return value
      termination_by ℭ.wf.wrap q
      let value ← fetch q
      return (⟨value, sorry⟩,
        { inputs := store.inputs,
          memos := ← memos.get,
          rdeps := ← rdeps.get,
          inputRdeps := ← inputRdeps.get,
          dirty := ← dirty.get })

end Incremental
