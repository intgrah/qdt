import Qdt.Incremental.Trace

namespace Qdt.Incremental

open Std (DHashMap HashMap)

variable {ε α Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

def runWithEngine
    (engine : Engine ε R)
    (rules : ∀ q, TaskM ε R (R q))
    (task : TaskM ε R α) :
    EIO ε (α × Engine ε R) := do
  let init : RunState ε R :=
    {
      engine
      started := DHashMap.emptyWithCapacity 1024
      stack := []
      deps := HashMap.emptyWithCapacity 64
    }
  let action : BaseM ε R (α × Engine ε R) := do
    let fetchRef : ST.Ref IO.RealWorld (∀ q, BaseM ε R (R q)) ←
      ST.mkRef (fun q => throw (engine.mkCycleError q))

    let fetchIO (q : Q) : BaseM ε R (R q) := do
      (← fetchRef.get) q

    let rulesIO (q : Q) : BaseM ε R (R q) := do
      let st ← get
      match st.started.get? q with
      | some memo => pure memo.value
      | none =>
          if st.stack.contains q then
            throw (st.engine.mkCycleError q)
          modify fun st => { st with stack := q :: st.stack }
          try
            let st ← get
            let engine := st.engine

            let recompute (store : Bool) : BaseM ε R (R q) := do
              let (value, deps) ← (trackDeps engine.fingerprint (rules q)).run { fetch := fetchIO }
              let memo : Memo R q := { value, deps }
              modify fun st => { st with started := st.started.insert q memo }
              if store then
                modify fun st =>
                  { st with engine := { st.engine with cache := st.engine.cache.insert q memo } }
              pure value

            if engine.isInput q then
              recompute (store := false)
            else
              match engine.cache.get? q with
              | some memo =>
                  if (← (verifyDeps engine.fingerprint memo.deps).run { fetch := fetchIO }) then
                    modify fun st => { st with started := st.started.insert q memo }
                    pure memo.value
                  else
                    recompute (store := true)
              | none =>
                  recompute (store := true)
          finally
            modify fun st =>
              match st.stack with
              | [] => st
              | _ :: rest => { st with stack := rest }

    fetchRef.set rulesIO

    let a ← task.run ⟨fetchIO⟩
    let st ← get
    pure (a, st.engine)

  action.run' init

end Qdt.Incremental
