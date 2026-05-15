module

public import Incremental.Shake.Basic

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

namespace Shake

variable
  {ℭ : BuildConfig}
  {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)

section main
variable [BEq ℭ.Q] [Hashable ℭ.Q]
  {m : Type → Type} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m]
  [DecidableEq H] [LawfulBEq ℭ.Q]

@[specialize bracket]
def fetch
    (bracket : ∀ {α}, ℭ.Q → m α → m α)
    (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
  let (vcache, cache) ← get
  if let some ⟨(v, _), _⟩ := vcache.get? q₀ then return v
  let fetchWithHash (q' : ℭ.Q) (_ : ℭ.rel q' q₀) :
      StateT (Store hI hR tasks ι₀) m
        { vh : Value tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val } := do
    let v ← fetch bracket ι₀ q'
    let (vc, _) ← get
    match vc.get? q' with
    | some e => pure ⟨(v, e.val.snd), by
        rw [e.property]
        exact congrArg (hR q') (e.val.fst.spec.trans v.spec.symm)⟩
    | none => pure ⟨(v, hR q' v.val), rfl⟩
  let doRun : StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
    let ⟨(memo, value), _⟩ ← run hI hR tasks ι₀ q₀ bracket fetchWithHash
    modify fun (vc, c) =>
      (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c.insert q₀ memo)
    pure value
  match cache.get? q₀ with
  | some mm =>
    if hvin : verifyInputs hI ι₀ mm.inputDeps then do
      match ← verifyDeps hI hR tasks ι₀
          (fun q' _hq => fetch bracket ι₀ q') mm.queryDeps with
      | some ⟨hdep⟩ =>
        let value : Value tasks ι₀ q₀ := ⟨mm.value, mm.invariant ι₀
          ((verifyInputs_spec hI ι₀ mm.inputDeps).mp hvin) hdep⟩
        modify fun (vc, c) =>
          (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c)
        pure value
      | none => doRun
    else doRun
  | none => doRun
termination_by ℭ.wf.wrap q₀

end main

end Shake

public def Shake
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    (bracket : ∀ {α}, ℭ.Q → m α → m α := fun _ x => x) :
    Build ℭ J tasks m Id where
  σ := J × Shake.Cache hI hR tasks
  init j := (j, DHashMap.emptyWithCapacity 1024)
  inputs s := Input.get s.fst
  set i v := modify fun (j, c) => (Input.set j i v, c)
  build q store := do
    let (j, oldCache) := store
    let ι₀ := Input.get j
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024, oldCache)
    let (v, (_, newCache)) ←
      bracket q (Shake.fetch (m := m) hI hR tasks bracket ι₀ q initStore)
    pure (v, (j, newCache))

end Incremental
