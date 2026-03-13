module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (J : Type) [Input I V J]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

public structure Shake.Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  inputDeps : HashMap I UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

public structure Shake.Store (J : Type) where
  inputs : J
  memos : DHashMap Q (Memo I Q R)

public partial def Shake : Build Monad I V Q R J where
  σ := Shake.Store I Q R J
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q := fun store => runEST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some m := (← started.get).get? q then
        return m.value
      let stk ← stack.get
      if stk.contains q then throw .cycle
      stack.set (stk.push q)
      let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
      let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 4)
      let input' (i : I) : EST BuildError σ (V i) := do
        let v := Input.get store.inputs i
        if !(← inputDeps.get).contains i then
          inputDeps.modify (·.insert i (hash v))
        pure v
      let fetch' (q : Q) : EST BuildError σ (R q) := do
        let v ← fetch q
        if !(← deps.get).contains q then
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
    return (← fetch q, ⟨store.inputs, ← memos.get⟩)

end Incremental
