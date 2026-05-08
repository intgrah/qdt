module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IdealHash
public import Incremental.ShakeStore

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap)

namespace Shake

variable
  {ℭ : BuildConfig}
  {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks Monad ℭ)

abbrev eval : (∀ i, ℭ.V i) → ∀ q : ℭ.Q, ℭ.R q :=
  compute Id.instMonad tasks

structure DepEntry (q₀ : ℭ.Q) where
  q : ℭ.Q
  hq : ℭ.rel q q₀
  h : H

structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : List (ℭ.I × H)
  deps : List (DepEntry (H := H) q)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.1 (ι p.1) = p.2) →
      (∀ p ∈ deps, hR p.q (eval tasks ι p.q) = p.h) →
      value = eval tasks ι q

abbrev Value (ι : ∀ i, ℭ.V i) (q : ℭ.Q) :=
  { r : ℭ.R q // r = eval tasks ι q }

private theorem inputDeps_invariant (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (inputDeps : List (ℭ.I × H))
    (hin_trace : inputDeps =
      (FM.evalTrace_inputs ι₀ (eval tasks ι₀)
        (tasksTree ℭ tasks q₀)).reverse.map (fun p => (⟨p.1, hI p.1 p.2⟩ : ℭ.I × H)))
    (ι : ∀ i, ℭ.V i)
    (hin : ∀ p ∈ inputDeps, hI p.1 (ι p.1) = p.2) :
    ∀ p ∈ FM.evalTrace_inputs ι₀ (eval tasks ι₀)
        (tasksTree ℭ tasks q₀),
      ι p.1 = p.2 := fun p hp => by
  have : (⟨p.1, hI p.1 p.2⟩ : ℭ.I × H) ∈ inputDeps :=
    hin_trace ▸ List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
  simpa using hin _ this

private theorem depEntries_invariant (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (deps : List (DepEntry (H := H) q₀))
    (hdep_trace : deps =
      (FM.evalTrace_deps ι₀ (eval tasks ι₀)
        (tasksTree ℭ tasks q₀)).reverse.map
          (fun p => (⟨p.q, p.hq, hR p.q p.r⟩ : DepEntry q₀)))
    (ι : ∀ i, ℭ.V i)
    (hdep : ∀ p ∈ deps, hR p.q (eval tasks ι p.q) = p.h) :
    ∀ p ∈ FM.evalTrace_deps ι₀ (eval tasks ι₀)
        (tasksTree ℭ tasks q₀),
      eval tasks ι p.q = p.r := fun p hp => by
  have : (⟨p.q, p.hq, hR p.q p.r⟩ : DepEntry q₀) ∈ deps :=
    hdep_trace ▸ List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
  simpa using hdep _ this

variable [DecidableEq H]

abbrev verifyInputs (ι : ∀ i, ℭ.V i) (l : List (ℭ.I × H)) : Bool :=
  l.all fun ⟨i, h⟩ => hI i (ι i) = h

theorem verifyInputs_spec (ι : ∀ i, ℭ.V i) (l : List (ℭ.I × H)) :
    verifyInputs hI ι l = true ↔ ∀ p ∈ l, hI p.1 (ι p.1) = p.2 := by
  simp

variable [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

abbrev Cache := DHashMap ℭ.Q (Memo hI hR tasks)

abbrev VCache (ι : ∀ i, ℭ.V i) :=
  DHashMap ℭ.Q (fun q => { p : Value tasks ι q × H // p.2 = hR q p.1.val })

abbrev Store (ι : ∀ i, ℭ.V i) := VCache hR tasks ι × Cache hI hR tasks

structure RunState (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) where
  store : Store hI hR tasks ι₀
  ins : List (ℭ.I × H)
  deps : List (DepEntry (H := H) q₀)

def verifyDeps (ι₀ : ∀ i, ℭ.V i) {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q')) :
    (l : List (DepEntry (H := H) q₀)) →
    StateM (Store hI hR tasks ι₀)
      (Option (PLift (∀ p ∈ l, hR p.q (eval tasks ι₀ p.q) = p.h)))
  | [] => pure (some ⟨nofun⟩)
  | ⟨q', hq, h⟩ :: rest => do
      let v ← fetch q' hq
      let (vc, _) ← get
      let cachedHash := match vc.get? q' with
        | some e => e.val.2
        | none => hR q' v.val
      if heq : cachedHash = h then do
        have hcache : cachedHash = hR q' v.val := by
          dsimp only [cachedHash]
          split
          · next e _ =>
            rw [e.property]
            exact congrArg (hR q') (e.val.1.property.trans v.property.symm)
          · rfl
        match ← verifyDeps ι₀ fetch rest with
        | some ⟨hrest⟩ =>
          pure (some ⟨fun p hp => by
            cases hp with
            | head =>
              show hR q' (eval tasks ι₀ q') = h
              rw [← v.property, ← hcache]
              exact heq
            | tail _ ht => exact hrest p ht⟩)
        | none => pure none
      else
        pure none

def traceAction (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    Task.Monad.Action (StateM (RunState hI hR tasks ι₀ q₀)) (FM ℭ q₀) where
  rel {α β} P m t :=
    ∀ s,
      P (m.run s).1 (FM.evalTree ι₀ (eval tasks ι₀) t) ∧
      (m.run s).2.ins =
        (FM.evalTrace_inputs ι₀ (eval tasks ι₀) t).reverse.map
          (fun ⟨i, v⟩ => ⟨i, hI i v⟩) ++ s.ins ∧
      (m.run s).2.deps =
        (FM.evalTrace_deps ι₀ (eval tasks ι₀) t).reverse.map
          (fun ⟨q, hq, r⟩ => ⟨q, hq, hR q r⟩) ++ s.deps
  rel_pure hab s := ⟨hab, rfl, rfl⟩
  rel_bind {α₁ α₂ β₁ β₂ R S ma mt ka kt} hma hk s := by
    have ⟨hv, hin, hdep⟩ := hma s
    have ⟨hv', hin', hdep'⟩ := hk _ _ hv (StateT.run ma s).2
    have hbind : StateT.run (ma >>= ka) s =
        StateT.run (ka (StateT.run ma s).1) (StateT.run ma s).2 := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [show FM.evalTree _ _ (mt >>= kt) = _ from FM.evalTree_bind ..]
      exact hv'
    · rw [
        congrArg (·.2.ins) hbind,
        hin', hin,
        show (mt >>= kt) = FM.bind mt kt from rfl,
        FM.evalTrace_inputs_bind,
      ]
      simp
    · rw [
        congrArg (·.2.deps) hbind,
        hdep', hdep,
        show (mt >>= kt) = FM.bind mt kt from rfl,
        FM.evalTrace_deps_bind
      ]
      simp

def run (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀)
        { vh : Value tasks ι₀ q' × H // vh.2 = (hR q') vh.1.val }) :
    StateM (Store hI hR tasks ι₀)
      { mv : Memo hI hR tasks q₀ × Value tasks ι₀ q₀ //
        mv.1.value = mv.2.val } :=
  fun store =>
    let input' (i : ℭ.I) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.V i) :=
      fun s => (ι₀ i, { s with ins := ⟨i, hI i (ι₀ i)⟩ :: s.ins })
    let fetch' (q : ℭ.Q) (hq : ℭ.rel q q₀) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.R q) :=
      fun s =>
        let (⟨(v, h), _⟩, st') := fetch q hq s.store
        (v.val, { s with store := st', deps := ⟨q, hq, h⟩ :: s.deps })
    let m := tasks q₀ (StateM (RunState hI hR tasks ι₀ q₀)) input' fetch'
    let initState : RunState hI hR tasks ι₀ q₀ := ⟨store, [], []⟩
    let result := m initState
    have ⟨hval_tree, hin_trace, hdep_trace⟩ :=
      Task.Monad.freeTheorem (tasks q₀) (traceAction hI hR tasks ι₀ q₀)
        input' FM.pureInput fetch' FM.pureFetch
        (fun _ _ => ⟨rfl, rfl, rfl⟩)
        (fun q hq s => ⟨(fetch q hq s.store).1.val.1.property, rfl, by
          show (⟨q, hq, (fetch q hq s.store).1.val.2⟩ : DepEntry q₀) :: s.deps =
               (⟨q, hq, hR q (eval tasks ι₀ q)⟩ : DepEntry q₀) :: s.deps
          rw [(fetch q hq s.store).1.property, (fetch q hq s.store).1.val.1.property]⟩)
        initState
    have hval : result.1 = eval tasks ι₀ q₀ :=
      hval_tree.trans (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀)
    have hin_trace' : result.2.ins =
        (FM.evalTrace_inputs ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀)).reverse.map
          fun ⟨i, v⟩ => ⟨i, hI i v⟩ := by
      simpa [initState] using hin_trace
    have hdep_trace' : result.2.deps =
        (FM.evalTrace_deps ι₀ (eval tasks ι₀) (tasksTree ℭ tasks q₀)).reverse.map
          fun ⟨q, hq, r⟩ => ⟨q, hq, hR q r⟩ := by
      simpa [initState] using hdep_trace
    let memo : Memo hI hR tasks q₀ :=
      { value := result.1
        inputDeps := result.2.ins
        deps := result.2.deps
        invariant ι hin hdep := by
          rw [hval]
          dsimp only [eval]
          rw [
            ← tasksTree_eval_compute ℭ tasks q₀ ι₀,
            ← tasksTree_eval_compute ℭ tasks q₀ ι
          ]
          exact FM.evalTree_cross ι₀ ι (eval tasks ι₀) (eval tasks ι)
            (tasksTree ℭ tasks q₀)
            (inputDeps_invariant hI tasks ι₀ q₀ result.2.ins hin_trace' ι hin)
            (depEntries_invariant hR tasks ι₀ q₀ result.2.deps hdep_trace' ι hdep) }
    (⟨(memo, ⟨result.1, hval⟩), rfl⟩, result.2.store)

def fetch (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
  let (vcache, cache) ← get
  if let some ⟨(v, _), _⟩ := vcache.get? q₀ then return v
  let fetchWithHash (q' : ℭ.Q) (_ : ℭ.rel q' q₀) :
      StateM (Store hI hR tasks ι₀)
        { vh : Value tasks ι₀ q' × H // vh.2 = (hR q') vh.1.val } := do
    let v ← fetch ι₀ q'
    let (vc, _) ← get
    match vc.get? q' with
    | some e => pure ⟨(v, e.val.2), by rw [e.property]; exact congrArg (hR q') (e.val.1.property.trans v.property.symm)⟩
    | none => pure ⟨(v, hR q' v.val), rfl⟩
  let doRun : StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
    let ⟨(memo, value), _⟩ ← run hI hR tasks ι₀ q₀ fetchWithHash
    modify fun (vc, c) => (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c.insert q₀ memo)
    pure value
  match cache.get? q₀ with
  | some m =>
    if hvin : verifyInputs hI ι₀ m.inputDeps then do
      match ← verifyDeps hI hR tasks ι₀ (fun q' hq => fetch ι₀ q') m.deps with
      | some ⟨hdep⟩ =>
        let value : Value tasks ι₀ q₀ := ⟨m.value, m.invariant ι₀
          ((verifyInputs_spec hI ι₀ m.inputDeps).mp hvin) hdep⟩
        modify fun (vc, c) => (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c)
        pure value
      | none => doRun
    else doRun
  | none => doRun
termination_by ℭ.wf.wrap q₀

end Shake

public def Shake
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks Monad ℭ) :
    Build Monad ℭ J tasks where
  cId := Id.instMonad
  σ := J × Shake.Cache hI hR tasks
  init j := (j, DHashMap.emptyWithCapacity 1024)
  inputs s := Input.get s.1
  set i v := modify fun (j, c) => (Input.set j i v, c)
  build q store :=
    let (j, oldCache) := store
    let ι₀ := Input.get j
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024, oldCache)
    let (v, (_, newCache)) := Shake.fetch hI hR tasks ι₀ q initStore
    (v, (j, newCache))

end Incremental
