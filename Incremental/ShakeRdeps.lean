module

public import Incremental.Shake

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure ShakeRdeps.Store (ι : Type) where
  inputs : ι
  memos : DHashMap Q (Shake.Memo I Q R)
  rdeps : HashMap Q (HashSet Q)

partial def ShakeRdeps.getTransitiveDependents {Q : Type} [BEq Q] [Hashable Q]
    (rdeps : HashMap Q (HashSet Q)) (keys : HashSet Q) : HashSet Q :=
  let rec go (worklist : List Q) (visited : HashSet Q) : HashSet Q :=
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
    {I Q R ι} [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
    [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]
    (store : ShakeRdeps.Store I Q R ι) (changedKeys : HashSet Q) : ShakeRdeps.Store I Q R ι :=
  let toInvalidate := getTransitiveDependents store.rdeps changedKeys
  { store with memos := toInvalidate.fold .erase store.memos }

partial def ShakeRdeps : Build Monad I V Q R ι where
  σ := ShakeRdeps.Store I Q R ι
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
    rdeps := HashMap.emptyWithCapacity 1024
  }
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q := fun store => runEST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let rdeps ← ST.mkRef (σ := σ) store.rdeps
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some dependent := (← stack.get).back? then
        rdeps.modify fun rd =>
          rd.alter q (·.getD ∅ |>.insert dependent)
      if let some m := (← started.get).get? q then
        return m.value
      let stk ← stack.get
      if stk.contains q then throw .cycle
      stack.set (stk.push q)
      let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
      let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 4)
      let input' (i : I) : EST BuildError σ (V i) := do
        let v := Input.get store.inputs i
        let ds ← inputDeps.get
        if !ds.contains i then
          inputDeps.modify (·.insert i (hash v))
        pure v
      let fetch' (q : Q) : EST BuildError σ (R q) := do
        let v ← fetch q
        let ds ← deps.get
        if !ds.contains q then
          let h := match (← started.get).get? q with
            | some m => m.hash
            | none => hash v
          deps.modify (·.insert q h)
        pure v
      let verifyInputDeps (inputDeps : HashMap I UInt64) : Bool :=
        inputDeps.all fun i oldHash => hash (Input.get (V := V) store.inputs i) == oldHash
      let verifyDeps (deps : HashMap Q UInt64) : EST BuildError σ Bool := do
        for (depKey, oldHash) in deps do
          let _ ← fetch depKey
          let h := match (← started.get).get? depKey with
            | some m => m.hash
            | none => 0
          if h != oldHash then return false
        return true
      let recompute : EST BuildError σ (R q) := do
        let value ← tasks q (EST BuildError σ) input' fetch'
        let m : Shake.Memo I Q R q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
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
    return (← fetch q, ⟨store.inputs, ← memos.get, ← rdeps.get⟩)

end Incremental
