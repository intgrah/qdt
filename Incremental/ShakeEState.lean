module

public import Incremental.Shake

public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure ShakeEState.State where
  memos : DHashMap Q (Shake.Memo I Q R)
  started : DHashMap Q (Shake.Memo I Q R)
  stack : Array Q
  deps : HashMap Q UInt64
  inputDeps : HashMap I UInt64

partial def ShakeEState : Build Monad I V Q R ι where
  σ := Shake.Store I Q R ι
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q := fun store =>
    let rec fetch (q : Q) : EStateM BuildError (ShakeEState.State I Q R) (R q) := do
      if let some m := (← get).started.get? q then
        return m.value
      if (← get).stack.contains q then throw .cycle
      modify fun s => { s with stack := s.stack.push q }
      let savedDeps := (← get).deps
      let savedInputDeps := (← get).inputDeps
      modify fun s => { s with
        deps := HashMap.emptyWithCapacity 64
        inputDeps := HashMap.emptyWithCapacity 4
      }
      let input' (i : I) : EStateM BuildError (ShakeEState.State I Q R) (V i) := do
        let v := Input.get store.inputs i
        if !(← get).inputDeps.contains i then
          modify fun s => { s with inputDeps := s.inputDeps.insert i (hash v) }
        pure v
      let fetch' (q : Q) : EStateM BuildError (ShakeEState.State I Q R) (R q) := do
        let v ← fetch q
        if !(← get).deps.contains q then
          let h := match (← get).started.get? q with
            | some m => m.hash
            | none => hash v
          modify fun s => { s with deps := s.deps.insert q h }
        pure v
      let verifyInputDeps (inputDeps : HashMap I UInt64) : Bool :=
        inputDeps.all fun i oldHash => hash (Input.get (V := V) store.inputs i) == oldHash
      let verifyDeps (deps : HashMap Q UInt64) : EStateM BuildError (ShakeEState.State I Q R) Bool := do
        for (depKey, oldHash) in deps do
          let _ ← fetch depKey
          let h := match (← get).started.get? depKey with
            | some m => m.hash
            | none => 0
          if h != oldHash then return false
        return true
      let recompute : EStateM BuildError (ShakeEState.State I Q R) (R q) := do
        let value ← tasks q (EStateM BuildError (ShakeEState.State I Q R)) input' fetch'
        let m : Shake.Memo I Q R q := { value, deps := (← get).deps, inputDeps := (← get).inputDeps }
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
    let initState : ShakeEState.State I Q R := {
      memos := store.memos
      started := .emptyWithCapacity 1024
      stack := #[]
      deps := .emptyWithCapacity 64
      inputDeps := .emptyWithCapacity 4
    }
    match (fetch q).run initState with
    | .ok r s => .ok (r, { store with memos := s.memos })
    | .error e _ => .error e

end Incremental
