module

public import Incremental.Basic

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

variable
  (I : Type) (V : I → Type)
  (Q : Type) (R : Q → Type)
  (ι : Type) [Input I V ι]
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure Shake.Memo (q : Q) where
  value : R q
  deps : HashMap Q UInt64
  hash : UInt64 := hash value
  hash_value : Hashable.hash value = hash := by rfl

structure Shake.Store (ι : Type) where
  inputs : ι
  cache : DHashMap Q (Memo Q R)

partial def Shake : Build Monad I V Q R ι where
  σ := Shake.Store Q R ι
  init store := { inputs := store, cache := DHashMap.emptyWithCapacity 1024 }
  set s i v := { s with inputs := Input.set s.inputs i v }
  build tasks q s := runEST fun σ => do
    let memo ← ST.mkRef (σ := σ) s.cache
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      match (← started.get).get? q with
      | some m => pure m.value
      | none =>
        let stk ← stack.get
        if stk.contains q then throw .cycle
        stack.set (stk.push q)
        let compute : EST BuildError σ (R q × HashMap Q UInt64) := do
          let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
          let fetch' (q : Q) : EST BuildError σ (R q) := do
            let v ← fetch q
            let ds ← deps.get
            if !ds.contains q then
              let h := match (← started.get).get? q with
                | some m => m.hash
                | none => hash v
              deps.modify (·.insert q h)
            pure v
          let a ← tasks q (EST BuildError σ) (Input.get s.inputs) fetch'
          return (a, ← deps.get)
        let verifyDeps (deps : HashMap Q UInt64) : EST BuildError σ Bool := do
          for (depKey, oldHash) in deps do
            let _ ← fetch depKey
            let h := match (← started.get).get? depKey with
              | some m => m.hash
              | none => 0
            if h != oldHash then return false
          return true
        let recompute : EST BuildError σ (R q) := do
          let (value, deps) ← compute
          let m : Shake.Memo Q R q := { value, deps }
          started.modify (·.insert q m)
          memo.modify (·.insert q m)
          pure value
        let r ← match (← memo.get).get? q with
          | some m =>
            if ← verifyDeps m.deps then
              started.modify (·.insert q m)
              pure m.value
            else recompute
          | none => recompute
        stack.modify Array.pop
        return r
    return (← fetch q, ⟨s.inputs, ← memo.get⟩)

@[extern "lean_shake_build"]
opaque ShakeNative.build' {I : Type} {V : I → Type} {Q : Type} {R : Q → Type}
    [BEq Q] [Hashable Q] [∀ q, Hashable (R q)] :
    (∀ i, V i) → Tasks Monad I V Q R →
    ∀ q, DHashMap Q (Shake.Memo Q R) →
    Except BuildError (R q × DHashMap Q (Shake.Memo Q R))

def ShakeNative : Build Monad I V Q R ι where
  σ := Shake.Store Q R ι
  init store := { inputs := store, cache := DHashMap.emptyWithCapacity 1024 }
  set s i v := { s with inputs := Input.set s.inputs i v }
  build tasks q s :=
    match ShakeNative.build' (Input.get s.inputs) tasks q s.cache with
    | .ok (r, cache) => Except.ok (r, { inputs := s.inputs, cache })
    | .error e => .error e

structure ShakeRdeps.Store (ι : Type) where
  inputs : ι
  cache : DHashMap Q (Shake.Memo Q R)
  rdeps : HashMap Q (HashSet Q) := HashMap.emptyWithCapacity 1024

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

def ShakeRdeps.invalidate {Q R ι} [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]
    (store : ShakeRdeps.Store Q R ι) (changedKeys : HashSet Q) : ShakeRdeps.Store Q R ι :=
  let toInvalidate := getTransitiveDependents store.rdeps changedKeys
  { store with cache := toInvalidate.fold (init := store.cache) DHashMap.erase }

partial def ShakeRdeps : Build Monad I V Q R ι where
  σ := ShakeRdeps.Store Q R ι
  init store := { inputs := store, cache := DHashMap.emptyWithCapacity 1024 }
  set s i v := { s with inputs := Input.set s.inputs i v }
  build tasks q s := runEST fun σ => do
    let cache ← ST.mkRef (σ := σ) s.cache
    let rdeps ← ST.mkRef (σ := σ) s.rdeps
    let started ← ST.mkRef (σ := σ) (DHashMap.emptyWithCapacity 1024)
    let stack ← ST.mkRef (σ := σ) #[]
    let rec fetch (q : Q) : EST BuildError σ (R q) := do
      if let some dependent := (← stack.get).back? then
        rdeps.modify fun rd =>
          rd.alter q (·.getD ∅ |>.insert dependent)
      match (← started.get).get? q with
      | some m => pure m.value
      | none =>
        let stk ← stack.get
        if stk.contains q then throw .cycle
        stack.set (stk.push q)
        let compute : EST BuildError σ (R q × HashMap Q UInt64) := do
          let deps ← ST.mkRef (σ := σ) (HashMap.emptyWithCapacity 64)
          let fetch' (q : Q) : EST BuildError σ (R q) := do
            let v ← fetch q
            let ds ← deps.get
            if !ds.contains q then
              let h := match (← started.get).get? q with
                | some m => m.hash
                | none => hash v
              deps.modify (·.insert q h)
            pure v
          let a ← tasks q (EST BuildError σ) (Input.get s.inputs) fetch'
          return (a, ← deps.get)
        let verifyDeps (deps : HashMap Q UInt64) : EST BuildError σ Bool := do
          for (depKey, oldHash) in deps do
            let _ ← fetch depKey
            let h := match (← started.get).get? depKey with
              | some m => m.hash
              | none => 0
            if h != oldHash then return false
          return true
        let recompute : EST BuildError σ (R q) := do
          let (value, deps) ← compute
          let m : Shake.Memo Q R q := { value, deps }
          started.modify (·.insert q m)
          cache.modify (·.insert q m)
          pure value
        let r ← match (← cache.get).get? q with
          | some m =>
            if ← verifyDeps m.deps then
              started.modify (·.insert q m)
              pure m.value
            else recompute
          | none => recompute
        stack.modify Array.pop
        return r
    return (← fetch q, ⟨s.inputs, ← cache.get, ← rdeps.get⟩)

end Incremental
