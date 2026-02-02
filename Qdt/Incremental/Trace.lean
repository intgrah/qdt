import Qdt.Incremental.Basic

namespace Qdt.Incremental

open Std (HashMap)

variable {ε α Q : Type} {R : Q → Type} [BEq Q] [LawfulBEq Q] [Hashable Q]

def trackDeps
    (fingerprint : ∀ q, R q → UInt64)
    (task : TaskM ε R α) :
    TaskM ε R (α × HashMap Q UInt64) := do
  let oldDeps := (← get).deps
  modify fun st => { st with deps := HashMap.emptyWithCapacity 64 }
  let base ← read
  let fetch' : ∀ q, BaseM ε R (R q) := fun q => do
    let v ← base q
    let ds := (← get).deps
    if !ds.contains q then
      modify fun st => { st with deps := st.deps.insert q (fingerprint q v) }
    pure v
  let a ← task.run fetch'
  let deps := (← get).deps
  modify fun st => { st with deps := oldDeps }
  return (a, deps)

def verifyDeps
    (fingerprint : ∀ q, R q → UInt64)
    (deps : HashMap Q UInt64) :
    TaskM ε R Bool := do
  deps.toList.allM fun (q, old) => do
    let v ← TaskM.fetch q
    return fingerprint q v == old

end Qdt.Incremental
