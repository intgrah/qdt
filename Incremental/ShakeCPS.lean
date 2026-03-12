module

public import Incremental.Shake
public import Mathlib.Control.Monad.Cont

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq I] [LawfulBEq I] [Hashable I] [∀ i, Hashable (V i)]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

public partial def ShakeCPS : Build Monad I V Q R ι where
  σ := Shake.Store I Q R ι
  init inputs := {
    inputs
    memos := DHashMap.emptyWithCapacity 1024
  }
  set i v := modify fun store =>
    { store with inputs := Input.set store.inputs i v }
  build tasks q₀ := fun store => runEST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : ContT (R q₀) (EST BuildError σ) (R q) := fun k => do
      if let some m := (← started.get).get? q then
        k m.value
      else
        let stk ← stack.get
        if stk.contains q then throw .cycle
        stack.set (stk.push q)
        let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
        let inputDeps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 4)
        let input' (i : I) : ContT (R q₀) (EST BuildError σ) (V i) := fun ki => do
          let v := Input.get store.inputs i
          if !(← inputDeps.get).contains i then
            inputDeps.modify (·.insert i (hash v))
          ki v
        let fetch' (q' : Q) : ContT (R q₀) (EST BuildError σ) (R q') := fun ki =>
          (fetch q').run fun v => do
            if !(← deps.get).contains q' then
              let h := match (← started.get).get? q' with
                | some m => m.hash
                | none => hash v
              deps.modify (·.insert q' h)
            ki v
        let recompute : EST BuildError σ (R q₀) :=
          (tasks q (ContT (R q₀) (EST BuildError σ)) input' fetch').run fun value => do
            let m : Shake.Memo I Q R q := { value, deps := ← deps.get, inputDeps := ← inputDeps.get }
            started.modify (·.insert q m)
            memos.modify (·.insert q m)
            stack.modify Array.pop
            k value
        let verifyInputDeps (inputDeps : HashMap I UInt64) : Bool :=
          inputDeps.all fun i oldHash => hash (Input.get (V := V) store.inputs i) == oldHash
        match (← memos.get).get? q with
        | some m =>
          if !verifyInputDeps m.inputDeps then recompute
          else
            m.deps.toList.foldr (init := do
              started.modify (·.insert q m)
              stack.modify Array.pop
              k m.value
            ) fun (depKey, oldHash) cont =>
              (fetch depKey).run fun _ => do
                let h := match (← started.get).get? depKey with
                  | some m => m.hash
                  | none => 0
                if h != oldHash then recompute
                else cont
        | none => recompute
    return (← (fetch q₀).run pure, ⟨store.inputs, ← memos.get⟩)

end Incremental
