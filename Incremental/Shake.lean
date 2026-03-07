module

public import Incremental.Basic

@[expose] public section

namespace Incremental

namespace Shake

open Std (DHashMap HashMap)

variable {Q : Type} {R : Q → Type}
  [BEq Q] [LawfulBEq Q] [Hashable Q] [∀ q, Hashable (R q)]

structure State where
  store : Store Q R
  started : DHashMap Q (Memo Q R)
  stack : List Q
  currentDeps : HashMap Q UInt64

partial def build : Build Monad Q R :=
  fun tasks target store => runEST fun σ => do
    let stRef ← ST.mkRef (σ := σ) ({
      store
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      currentDeps := HashMap.emptyWithCapacity 64
    } : State (Q := Q) (R := R))

    let rec buildRule (q : Q) : EST Cycle σ (R q) := do
      let st ← stRef.get

      match st.started.get? q with
      | some memo =>
          match st.stack.head? with
          | some dependent =>
              stRef.modify fun st =>
                let store := st.store.addReverseDep Q R q dependent
                { st with store }
          | none => pure ()
          pure memo.value
      | none =>
          match st.stack.head? with
          | some dependent =>
              stRef.modify fun st =>
                let store := st.store.addReverseDep Q R q dependent
                { st with store }
          | none => pure ()
          if st.stack.contains q then
            throw Cycle.mk
          stRef.modify fun st => { st with stack := q :: st.stack }
          try
            let st ← stRef.get

            match tasks q with
            | none =>
                match st.store.cache.get? q with
                | some memo =>
                    stRef.modify fun st => { st with started := st.started.insert q memo }
                    pure memo.value
                | none =>
                    throw Cycle.mk
            | some task =>
                let compute : EST Cycle σ (R q × HashMap Q UInt64) := do
                  let oldDeps := (← stRef.get).currentDeps
                  stRef.modify fun st => { st with currentDeps := HashMap.emptyWithCapacity 64 }
                  let fetch' : ∀ q, EST Cycle σ (R q) := fun q => do
                    let v ← buildRule q
                    let ds := (← stRef.get).currentDeps
                    if !ds.contains q then
                      let h := match (← stRef.get).started.get? q with
                        | some memo => memo.hash
                        | none => hash v
                      stRef.modify fun st => { st with currentDeps := st.currentDeps.insert q h }
                    pure v
                  let a ← task _ fetch'
                  let deps := (← stRef.get).currentDeps
                  stRef.modify fun st => { st with currentDeps := oldDeps }
                  pure (a, deps)

                let verifyDeps (deps : HashMap Q UInt64) : EST Cycle σ PUnit := do
                  for (depKey, oldHash) in deps.toList do
                    try
                      let _ ← buildRule depKey
                      let h := match (← stRef.get).started.get? depKey with
                        | some memo => memo.hash
                        | none => hash 0
                      if h != oldHash then throw Cycle.mk
                    catch _ => throw Cycle.mk

                let recompute : EST Cycle σ (R q) := do
                  let (value, deps) ← compute
                  let memo : Memo Q R q := { value, deps }
                  stRef.modify fun st =>
                    { st with
                      started := st.started.insert q memo
                      store := { st.store with cache := st.store.cache.insert q memo } }
                  pure value

                match st.store.cache.get? q with
                | some memo =>
                    try
                      verifyDeps memo.deps
                      stRef.modify fun st => { st with started := st.started.insert q memo }
                      pure memo.value
                    catch _ => recompute
                | none =>
                    recompute
          finally
            stRef.modify fun st =>
              match st.stack with
              | [] => st
              | _ :: rest => { st with stack := rest }

    let _ ← buildRule target
    return (← stRef.get).store

end Shake
