module

public import Incremental.Basic

public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure Salsa.Memo (q : Q) where
  value : R q
  changedAt : Nat
  verifiedAt : Nat
  deps : Array Q
  inputDeps : Array I
  hash : UInt64 := Hashable.hash value
  hash_value : Hashable.hash value = hash := by rfl

structure Salsa.Store (ι : Type) where
  inputs : ι
  revision : Nat
  memos : DHashMap Q (Salsa.Memo I Q R)
  inputRevisions : HashMap I Nat

partial def Salsa : Build Monad I V Q R ι where
  σ := Salsa.Store I Q R ι
  init store := {
    inputs := store
    revision := 0
    memos := DHashMap.emptyWithCapacity 4096
    inputRevisions := HashMap.emptyWithCapacity 1024
  }
  set i v := modify fun store =>
    let revision := store.revision + 1
    let inputs := Input.set store.inputs i v
    let inputRevisions := store.inputRevisions.insert i revision
    { store with inputs, revision, inputRevisions }
  build tasks q := fun store => runEST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let stack ← ST.mkRef (σ := σ) (HashSet.emptyWithCapacity 64 : HashSet Q)
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      let memo? := (← memos.get).get? q
      if let some memo := memo? then
        if memo.verifiedAt == store.revision then
          return memo.value
      let stk ← stack.get
      if stk.contains q then throw .cycle
      stack.set (stk.insert q)
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
      let depsRef ← ST.mkRef (σ := σ) (#[] : Array Q)
      let inputDepsRef ← ST.mkRef (σ := σ) (#[] : Array I)
      let input' (i : I) : EST BuildError σ (V i) := do
        inputDepsRef.modify (·.push i)
        pure (Input.get store.inputs i)
      let fetch' (q : Q) : EST BuildError σ (R q) := do
        let v ← fetch q
        depsRef.modify (·.push q)
        pure v
      let value ← tasks q (EST BuildError σ) input' fetch'
      let h := Hashable.hash value
      let changedAt := match memo? with
        | some memo => if h == memo.hash then memo.changedAt else store.revision
        | none => store.revision
      let newMemo : Salsa.Memo I Q R q := {
        value
        hash := h
        changedAt
        verifiedAt := store.revision,
        deps := ← depsRef.get
        inputDeps := ← inputDepsRef.get
      }
      memos.modify (·.insert q newMemo)
      return value
    return (← fetch q, { store with memos := ← memos.get })

end Incremental
