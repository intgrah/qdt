module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (J : Type) [Input I V J]
  [BEq I] [LawfulBEq I] [Hashable I]
  [BEq Q] [LawfulBEq Q] [Hashable Q]

structure Make.Memo (q : Q) where
  value : R q
  modTime : Nat

structure Make.Store (J : Type) where
  inputs : J
  time : Nat
  memos : DHashMap Q (Make.Memo Q R)
  inputModTimes : HashMap I Nat

public partial def Make (tasks : Tasks Applicative I V Q R) : Build Applicative I V Q R J tasks where
  σ := Make.Store I Q R J
  init inputs := {
    inputs
    time := 0
    memos := DHashMap.emptyWithCapacity 1024
    inputModTimes := HashMap.emptyWithCapacity 64
  }
  set i v := modify fun store =>
    let inputs := Input.set store.inputs i v
    let time := store.time + 1
    let inputModTimes := store.inputModTimes.insert i time
    { store with inputs, time, inputModTimes }
  build q := fun store => runEST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let time ← ST.mkRef (σ := σ) store.time
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) (#[] : Array Q)
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some m := (← started.get).get? q then return m.value
      let stk ← stack.get
      if stk.contains q then throw .cycle
      stack.set (stk.push q)
      let task := tasks q
      let qDeps := task.queryDeps
      let iDeps := task.inputDeps
      for dep in qDeps do
        let _ ← fetch dep
      let ms ← memos.get
      let myModTime := match ms.get? q with | some m => m.modTime | none => 0
      let dirty := !ms.contains q
        || iDeps.any fun i => store.inputModTimes.getD i 0 > myModTime
        || qDeps.any fun d => match ms.get? d with | some m => m.modTime > myModTime | none => true
      let r ←
        if dirty then do
          time.modify (· + 1)
          let now ← time.get
          let v ← task (EST BuildError σ) (fun i => pure (Input.get store.inputs i)) fetch
          let m : Make.Memo Q R q := { value := v, modTime := now }
          started.modify (·.insert q m)
          memos.modify (·.insert q m)
          pure v
        else
          match ms.get? q with
          | some m =>
            started.modify (·.insert q m)
            pure m.value
          | none => throw .cycle
      stack.modify Array.pop
      pure r
    let result ← fetch q
    return (result, { store with time := ← time.get, memos := ← memos.get })

end Incremental
