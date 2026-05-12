module

public import Incremental.Shake

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap HashSet)

namespace Shake

variable
  {ℭ : BuildConfig}
  {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks Monad ℭ)

section main
variable [DecidableEq H] [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  {m : Type → Type} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m]
  (enter : ℭ.Q → m Unit) (exit : ℭ.Q → m Unit)

@[specialize enter exit]
def runMTraced (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m
        { vh : Value tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val }) :
    StateT (Store hI hR tasks ι₀) m
      { mv : Memo hI hR tasks q₀ × Value tasks ι₀ q₀ //
        mv.fst.value = mv.snd.val } := fun store => do
  let input' (i : ℭ.I) : StateT (RunState hI hR tasks ι₀ q₀) m (ℭ.V i) :=
    fun s => pure (ι₀ i, { s with ins := ⟨i, hI i (ι₀ i)⟩ :: s.ins })
  let fetch' (q : ℭ.Q) (hq : ℭ.rel q q₀) :
      StateT (RunState hI hR tasks ι₀ q₀) m (ℭ.R q) :=
    fun s => do
      liftM (enter q)
      let (⟨(v, h), _⟩, st') ← fetch q hq s.store
      liftM (exit q)
      pure (v.val, { s with store := st', deps := dedupPush ⟨q, hq, h⟩ s.deps })
  let mTree := tasks q₀ (StateT (RunState hI hR tasks ι₀ q₀) m) input' fetch'
  let initState : RunState hI hR tasks ι₀ q₀ := ⟨store, [], #[]⟩
  let hRel :=
    Task.Monad.freeTheorem (tasks q₀) (traceAction hI hR tasks ι₀ q₀ (m := m))
      input' FM.pureInput fetch' FM.pureFetch
      (fun i s a s' hcan => by
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hcan)
        refine ⟨rfl, ?_, rfl⟩
        simp [FM.pureInput, FM.evalTrace_inputs])
      (fun q hq s _ _ hcan => by
        obtain ⟨_, _, hrest₁⟩ := LawfulMonadAttach.canReturn_bind_imp' hcan
        obtain ⟨⟨r, _⟩, _, hrest₂⟩ :=
          LawfulMonadAttach.canReturn_bind_imp' (x := fetch q hq s.store) hrest₁
        obtain ⟨_, _, hpure_can⟩ := LawfulMonadAttach.canReturn_bind_imp' hrest₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hpure_can)
        refine ⟨r.val.fst.property, rfl, ?_⟩
        show dedupPush ⟨q, hq, r.val.snd⟩ s.deps =
             dedupPush ⟨q, hq, hR q (eval tasks ι₀ q)⟩ s.deps
        rw [r.property, r.val.fst.property])
  MonadAttach.pbind (mTree initState) fun result hcan => do
    have ⟨hval_tree, hin_trace, hdep_trace⟩ := hRel initState result.fst result.snd hcan
    have hval : result.fst = eval tasks ι₀ q₀ :=
      hval_tree.trans (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀)
    have hin_trace' : result.snd.ins =
        (FM.evalTrace_inputs ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀)).reverse.map
          fun p => ⟨p.i, hI p.i p.v⟩ := by
      simpa only [initState, List.append_nil] using hin_trace
    have hdep_trace' : result.snd.deps =
        pushAll hR (FM.evalTrace_deps ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀))
          (#[] : Array (DepEntry (H := H) q₀)) := by
      simpa only [initState] using hdep_trace
    let memo : Memo hI hR tasks q₀ :=
      { value := result.fst
        inputDeps := result.snd.ins
        deps := result.snd.deps
        invariant ι hin hdep := by
          have hin' : ∀ p ∈ FM.evalTrace_inputs ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀),
              ι p.i = p.v := fun p hp => (hI p.i).injective <|
            hin ⟨p.i, hI p.i p.v⟩ <| hin_trace' ▸
              List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
          have hdep' : ∀ p ∈ FM.evalTrace_deps ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀),
              eval tasks ι p.q = p.r := fun p hp => by
            have hpr := FM.evalTrace_deps_value _ _ _ _ hp
            have h_uniform : ∀ p' ∈ FM.evalTrace_deps ι₀ (eval tasks ι₀)
                (tasksTree ℭ tasks q₀),
                hR p'.q p'.r = hR p'.q (eval tasks ι₀ p'.q) :=
              fun _ hp' => congrArg _ (FM.evalTrace_deps_value _ _ _ _ hp')
            have ⟨y, hy_in, hy_q, hy_hash⟩ := hdep_trace' ▸ pushAll_complete (hR := hR)
              (target := fun q => hR q (eval tasks ι₀ q)) h_uniform p hp
            apply (hR p.q).injective
            rw [hpr, ← hy_q, hdep y hy_in, hy_hash, hy_q]
          calc result.fst
              = eval tasks ι₀ q₀ := hval
            _ = FM.evalTree ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀) :=
              (tasksTree_eval_compute ℭ tasks q₀ ι₀).symm
            _ = FM.evalTree ι (eval tasks ι) (tasksTree ℭ tasks q₀) :=
              FM.evalTree_cross ι₀ ι _ _ _ hin' hdep'
            _ = eval tasks ι q₀ := tasksTree_eval_compute ℭ tasks q₀ ι }
    pure (⟨(memo, ⟨result.fst, hval⟩), rfl⟩, result.snd.store)

@[specialize enter exit]
def fetchMTraced (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
  let (vcache, cache, inFlight) ← get
  if let some ⟨(v, _), _⟩ := vcache.get? q₀ then return v
  let fetchWithHash (q' : ℭ.Q) (_ : ℭ.rel q' q₀) :
      StateT (Store hI hR tasks ι₀) m
        { vh : Value tasks ι₀ q' × H // vh.2 = (hR q') vh.1.val } := do
    let v ← fetchMTraced ι₀ q'
    let (vc, _, _) ← get
    match vc.get? q' with
    | some e => pure ⟨(v, e.val.snd), by
        rw [e.property]
        exact congrArg (hR q') (e.val.fst.property.trans v.property.symm)⟩
    | none => pure ⟨(v, hR q' v.val), rfl⟩
  let doRun : StateT (Store hI hR tasks ι₀) m (Value tasks ι₀ q₀) := do
    let ⟨(memo, value), _⟩ ← runMTraced hI hR tasks enter exit ι₀ q₀ fetchWithHash
    modify fun (vc, c, ifl) =>
      (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c.insert q₀ memo, ifl)
    pure value
  if inFlight.contains q₀ then doRun
  else do
    modify fun (vc, c, ifl) => (vc, c, ifl.insert q₀)
    let result ←
      match cache.get? q₀ with
      | some mm =>
        if hvin : verifyInputs hI ι₀ mm.inputDeps then do
          match ← verifyDeps hI hR tasks ι₀ (fun q' _hq => fetchMTraced ι₀ q') mm.deps with
          | some ⟨hdep⟩ =>
            let value : Value tasks ι₀ q₀ := ⟨mm.value, mm.invariant ι₀
              ((verifyInputs_spec hI ι₀ mm.inputDeps).mp hvin) hdep⟩
            modify fun (vc, c, ifl) =>
              (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c, ifl)
            pure value
          | none => doRun
        else doRun
      | none => doRun
    modify fun (vc, c, ifl) => (vc, c, ifl.erase q₀)
    pure result
termination_by ℭ.wf.wrap q₀

end main

end Shake

public def ShakeTraced
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks Monad ℭ)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
    (enter : ℭ.Q → m Unit) (exit : ℭ.Q → m Unit) :
    Build Monad ℭ J tasks m where
  cId := Id.instMonad
  σ := J × Shake.Cache hI hR tasks
  init j := (j, DHashMap.emptyWithCapacity 1024)
  inputs s := Input.get s.fst
  set i v := modify fun (j, c) => (Input.set j i v, c)
  build q store := do
    let (j, oldCache) := store
    let ι₀ := Input.get j
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024, oldCache, ∅)
    liftM (enter q)
    let (v, (_, newCache, _)) ← Shake.fetchMTraced hI hR tasks enter exit ι₀ q initStore
    liftM (exit q)
    pure (v, (j, newCache))

end Incremental
