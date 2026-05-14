module

public import Incremental.Parametric

namespace Incremental

open Std (DHashMap)

namespace LessBusy

variable
  {ℭ : BuildConfig}
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  (tasks : MTasks ℭ) (ι₀ : ∀ i, ℭ.V i)

abbrev VCache := DHashMap ℭ.Q (Value Id.instMonad tasks ι₀)

def action : Task.Monad.Action (StateM (VCache tasks ι₀)) Id where
  rel P m b := ∀ s, P (m.run' s) b
  rel_pure hab _ := hab
  rel_bind hma hk s := hk _ _ (hma s) _

def run (q₀ : ℭ.Q)
    (fetch : ∀ q, ℭ.rel q q₀ →
      StateM (VCache tasks ι₀) (Value Id.instMonad tasks ι₀ q)) :
    StateM (VCache tasks ι₀) (Value Id.instMonad tasks ι₀ q₀) := do
  let ⟨r, hr⟩ ← MonadAttach.attach ((tasks q₀).fn (StateM (VCache tasks ι₀))
    (fun i => StateT.pure (ι₀ i))
    (fun q hq => Value.val <$> fetch q hq))
  have : r = computeM tasks ι₀ q₀ := by
    have ⟨s, s', heq⟩ := hr
    have hft := MTasks.freeTheorem tasks q₀ (action tasks ι₀)
      ι₀
      (fun i => StateT.pure (ι₀ i))
      (fun q hq => Value.val <$> fetch q hq)
      (fun i s => rfl)
      (fun q hq s => fetch q hq |>.run' s |>.spec) s
    exact (congrArg Prod.fst heq).symm.trans hft
  return ⟨r, this⟩

def fetch (q₀ : ℭ.Q) :
    StateM (VCache tasks ι₀) (Value Id.instMonad tasks ι₀ q₀) := do
  if let some v := (← get).get? q₀ then return v
  let v ← run tasks ι₀ q₀ (fun q _ => fetch q)
  modify (·.insert q₀ v)
  return v
termination_by ℭ.wf.wrap q₀

end LessBusy

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

public def LessBusy (tasks : MTasks ℭ) : Build Monad ℭ J tasks Id Id where
  cId := Id.instMonad
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build q store :=
    let ι₀ := Input.get store
    let cache₀ : LessBusy.VCache tasks ι₀ := DHashMap.emptyWithCapacity 1024
    let (v, _) := LessBusy.fetch tasks ι₀ q cache₀
    (v, store)

end Incremental
