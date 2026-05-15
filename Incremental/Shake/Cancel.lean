module

public import Incremental.Shake.Basic
public import Incremental.MonadCancel
public import Incremental.LawfulEST

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
  [MonadCancel m] [MonadLiftT BaseIO m]
  [DecidableEq H] [LawfulBEq ℭ.Q]

def fetchCancel
    (persist : ∀ q', Memo hI hR tasks q' → m PUnit)
    (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
  monadLift (MonadCancel.checkpoint : m PUnit)
  let (vcache, cache) ← get
  if let some ⟨(v, _), _⟩ := vcache.get? q₀ then return v
  let fetchWithHash (q' : ℭ.Q) (_ : ℭ.rel q' q₀) :
      StateT (Store hI hR tasks ι₀) m
        { vh : Value tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val } := do
    let v ← fetchCancel persist ι₀ q'
    let (vc, _) ← get
    match vc.get? q' with
    | some e => pure ⟨(v, e.val.snd), by
        rw [e.property]
        exact congrArg (hR q') (e.val.fst.spec.trans v.spec.symm)⟩
    | none => pure ⟨(v, hR q' v.val), rfl⟩
  let doRun : StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
    let ⟨(memo, value), _⟩ ←
      run hI hR tasks ι₀ q₀ (bracket := fun _ x => x) fetchWithHash
    modify fun (vc, c) =>
      (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c.insert q₀ memo)
    monadLift (m := m) (n := StateT _ m) (persist q₀ memo)
    pure value
  match cache.get? q₀ with
  | some mm =>
    if hvin : verifyInputs hI ι₀ mm.inputDeps then do
      match ← verifyDeps hI hR tasks ι₀ (fun q' _hq => fetchCancel persist ι₀ q') mm.queryDeps with
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

structure Cancelled

abbrev CancelM (Cache : Type) :=
  ReaderT (IO.Ref Bool) (ExceptT Cancelled (StateT Cache BaseIO))

instance {Cache} : MonadCancel (CancelM Cache) where
  CanCancel _ := True
  checkpoint := do
    let ref ← read
    let flag ← (ref.get : BaseIO Bool)
    if flag then throw ⟨⟩ else pure ⟨⟩

public def ShakeCancel
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ)
    (cancelRef : IO.Ref Bool)
    (onPersist : ℭ.Q → BaseIO Unit := fun _ => pure ()) :
    Build ℭ J tasks BaseIO (Except Cancelled) where
  σ := J × Shake.Cache hI hR tasks
  init j := (j, DHashMap.emptyWithCapacity 1024)
  inputs s := Input.get s.fst
  set i v := modify fun (j, c) => (Input.set j i v, c)
  build q store := do
    let (j, oldCache) := store
    let ι₀ := Input.get j
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024, oldCache)
    let persist : ∀ q', Shake.Memo hI hR tasks q' →
        CancelM (Shake.Cache hI hR tasks) PUnit :=
      fun q' memo =>
        fun _ref => ExceptT.lift do
          onPersist q'
          modifyThe (Shake.Cache hI hR tasks) (·.insert q' memo)
    let action := Shake.fetchCancel (m := CancelM (Shake.Cache hI hR tasks))
      hI hR tasks persist ι₀ q initStore
    let (excValueStore, finalCache) ← action cancelRef oldCache
    match excValueStore with
    | .ok (v, _) => return (.ok v, (j, finalCache))
    | .error e => return (.error e, (j, finalCache))

end Incremental
