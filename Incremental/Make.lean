module

public import Incremental.Basic

namespace Incremental

open Std (DHashMap HashMap)

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

public structure Make.Memo (q : ℭ.Q) where
  value : ℭ.R q
  modTime : Nat

public structure Make.Store (J : Type) where
  inputs : J
  time : Nat
  memos : DHashMap ℭ.Q (Make.Memo ℭ)
  inputModTimes : HashMap ℭ.I Nat

def Make.queryDeps {q : ℭ.Q} (task : Task Applicative ℭ q (ℭ.R q)) : List ℭ.Q :=
  task (Const (List ℭ.Q)) (fun _ => []) (fun q' _ => [q'])

def Make.inputDeps {q : ℭ.Q} (task : Task Applicative ℭ q (ℭ.R q)) : List ℭ.I :=
  task (Const (List ℭ.I)) (fun i => [i]) (fun _ _ => [])

public def Make (tasks : Tasks Applicative ℭ) : Build Applicative ℭ J tasks Id where
  cId := inferInstance
  σ := Make.Store ℭ J
  init inputs := {
    inputs
    time := 0
    memos := DHashMap.emptyWithCapacity 1024
    inputModTimes := HashMap.emptyWithCapacity 64
  }
  inputs store := Input.get store.inputs
  set i v := modify fun store =>
    let inputs := Input.set store.inputs i v
    let time := store.time + 1
    let inputModTimes := store.inputModTimes.insert i time
    { store with inputs, time, inputModTimes }
  build q store := runST fun σ => do
    let memos ← ST.mkRef (σ := σ) store.memos
    let time ← ST.mkRef (σ := σ) store.time
    let rec fetch (q : ℭ.Q) : ST σ (ℭ.R q) := do
      let task := tasks q
      let qDeps := Make.queryDeps ℭ task
      let iDeps := Make.inputDeps ℭ task
      for dep in qDeps do
        let _ ← fetch dep
      let ms ← memos.get
      let myModTime := match ms.get? q with | some m => m.modTime | none => 0
      let dirty := !ms.contains q
        || iDeps.any fun i => store.inputModTimes.getD i 0 > myModTime
        || qDeps.any fun d => match ms.get? d with | some m => m.modTime > myModTime | none => true
      if dirty then do
        time.modify (· + 1)
        let now ← time.get
        let v ← task (ST σ) (fun i => pure (Input.get store.inputs i)) (fun q' _ => fetch q')
        let m : Make.Memo ℭ q := { value := v, modTime := now }
        memos.modify (·.insert q m)
        pure v
      else
        match ms.get? q with
        | some m => pure m.value
        | none => fetch q
    termination_by ℭ.wf.wrap q
    decreasing_by all_goals sorry
    return (⟨← fetch q, sorry⟩, { store with time := ← time.get, memos := ← memos.get })

end Incremental
