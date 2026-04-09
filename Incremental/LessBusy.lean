module

public import Incremental.FreeTheorem

namespace Incremental

open Std (DHashMap)

namespace LessBusy

variable
  {ℭ : BuildConfig}
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  (tasks : Tasks Monad ℭ) (ι₀ : ∀ i, ℭ.V i)

abbrev Value (q : ℭ.Q) := { r : ℭ.R q // r = compute (inferInstance : Monad Id) tasks ι₀ q }
abbrev VCache := DHashMap ℭ.Q (Value tasks ι₀)

def action : MonadAction (StateM (VCache tasks ι₀)) Id where
  rel P m b := ∀ s, P (m s).1 b
  rel_pure := fun hab _ => hab
  rel_bind := fun hma hk s => hk _ _ (hma s) _

def run (q₀ : ℭ.Q)
    (fetch : ∀ q, ℭ.rel q q₀ →
      StateM (VCache tasks ι₀) (Value tasks ι₀ q)) :
    StateM (VCache tasks ι₀) (Value tasks ι₀ q₀) := do
  let ⟨r, hr⟩ ← MonadAttach.attach (tasks q₀ (StateM (VCache tasks ι₀))
    (fun i => StateT.pure (ι₀ i))
    (fun q hq => Subtype.val <$> fetch q hq))
  have : r = compute (inferInstance : Monad Id) tasks ι₀ q₀ := by
    obtain ⟨s, s', heq⟩ := hr
    have hft := Tasks.freeTheorem tasks q₀ (action tasks ι₀)
      ι₀
      (fun i => StateT.pure (ι₀ i))
      (fun q hq => Subtype.val <$> fetch q hq)
      (fun i s => rfl)
      (fun q hq s => fetch q hq |>.run' s |>.property) s
    exact (congrArg Prod.fst heq).symm.trans hft
  return ⟨r, this⟩

set_option linter.unusedVariables false in
def fetch (q₀ : ℭ.Q) :
    StateM (VCache tasks ι₀) (Value tasks ι₀ q₀) := do
  if let some v := (← get).get? q₀ then return v
  let v ← run tasks ι₀ q₀ (fun q hq => fetch q)
  modify (·.insert q₀ v)
  return v
termination_by ℭ.wf.wrap q₀
decreasing_by exact hq

end LessBusy

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

public def LessBusy : Build Monad ℭ J where
  cId := inferInstance
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q store :=
    let ι₀ := Input.get store
    let cache₀ : LessBusy.VCache tasks ι₀ := DHashMap.emptyWithCapacity 1024
    let (v, _) := LessBusy.fetch tasks ι₀ q cache₀
    (v, store)

end Incremental
