module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IntrinsicHash

@[expose] public section

namespace Incremental

open Std (DHashMap)

/-! ## Shake — fingerprint-based incremental build

Each `Memo` for query `q` carries a *universally quantified* invariant:
for every input function `ι` whose recorded fingerprints match, the
cached value equals `compute (inferInstance : Monad Id) tasks ι q`.

The two ingredients:

* `Function.Embedding.injective` (Mathlib) — applied to `hI i` /
  `hR q`, the per-position embeddings into the hash type `H`.
* `Tasks.freeTheorem` — parametricity for `Task`.

The first lets us read off pointwise equality of inputs (and dep
results) from hash equality.  The second lets us promote the recompute
in `StateM` to an equality of values in `Id`.
-/

namespace Shake

variable
  {ℭ : BuildConfig}
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  {H : Type}
  [DecidableEq H]
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks Monad ℭ)

/
quantifies over `ι`.  The `deps` list carries an `ℭ.rel q' q`
witness alongside each query so the recursive `fetch` decreases. -/
structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : List ((i : ℭ.I) × H)
  deps : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q), H)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.1 (ι p.1) = p.2) →
      (∀ p ∈ deps, hR p.1 (compute (inferInstance : Monad Id) tasks ι p.1) = p.2.2) →
      value = compute (inferInstance : Monad Id) tasks ι q

abbrev Cache := DHashMap ℭ.Q (Memo (H := H) hI hR tasks)

abbrev Value (ι : ∀ i, ℭ.V i) (q : ℭ.Q) :=
  { r : ℭ.R q // r = compute (inferInstance : Monad Id) tasks ι q }

/
input fingerprints. -/
def verifyInputs (ι : ∀ i, ℭ.V i) :
    List ((i : ℭ.I) × H) → Bool
  | [] => true
  | ⟨i, h⟩ :: rest =>
    decide (hI i (ι i) = h) && verifyInputs ι rest

theorem verifyInputs_iff (ι : ∀ i, ℭ.V i) (l : List ((i : ℭ.I) × H)) :
    verifyInputs (H := H) hI ι l = true ↔
      ∀ p ∈ l, hI p.1 (ι p.1) = p.2 := by
  induction l with
  | nil => simp [verifyInputs]
  | cons p rest ih =>
    obtain ⟨i, h⟩ := p
    simp [verifyInputs, ih, List.mem_cons]

variable {tasks}

/
`fetch`) and comparing its hash to the recorded fingerprint.  On
success returns a proof that every recorded fingerprint really is
`hashFn (compute (inferInstance : Monad Id) tasks ι q')`.  Each dep entry carries an
`ℭ.rel ι q' q₀` witness, threaded into the recursive `fetch`. -/
def verifyDeps {ι : ∀ i, ℭ.V i} {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Cache (H := H) hI hR tasks) (Value tasks ι q')) :
    (l : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q₀), H)) →
      StateM (Cache (H := H) hI hR tasks)
        (Option (PLift
          (∀ p ∈ l, hR p.1 (compute (inferInstance : Monad Id) tasks ι p.1) = p.2.2)))
  | [] => pure (some ⟨by intro _ h; cases h⟩)
  | ⟨q', hq, h⟩ :: rest => do
      let ⟨v, hv⟩ ← fetch q' hq
      if hh : hR q' v = h then
        match ← verifyDeps fetch rest with
        | none => pure none
        | some ⟨hrest⟩ =>
            pure (some ⟨by
              intro p hp
              cases hp with
              | head =>
                  show hR q' (compute (inferInstance : Monad Id) tasks ι q') = h
                  rw [← hv]; exact hh
              | tail _ ht => exact hrest _ ht⟩)
      else pure none

/-! ### Recompute

`runRecompute` lifts `tasks q₀` to its FM tree (via
`Task.freeTheorem` at `f := FM ℭ q₀` versus `Id`), warms the cache
by walking the FM dep-trace, and reads the value off `evalTree`. -/

/
its cache-update side effect.  The fetched value is discarded;
the recompute reads its result from `evalTree`. -/
def cacheUpdates {ι₀ : ∀ i, ℭ.V i} {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Cache (H := H) hI hR tasks) (Value tasks ι₀ q')) :
    List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q₀), ℭ.R q') →
      StateM (Cache (H := H) hI hR tasks) Unit
  | [] => pure ()
  | ⟨q', hq, _⟩ :: rest => do
      let _ ← fetch q' hq
      cacheUpdates fetch rest

/
FM tree, then returns the value paired with its proof of equality
to `compute (inferInstance : Monad Id) tasks ι₀ q₀`. -/
def runRecompute (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Cache (H := H) hI hR tasks) (Value tasks ι₀ q')) :
    StateM (Cache (H := H) hI hR tasks) (Value tasks ι₀ q₀) := do
  let tree := Incremental.tasksTree ℭ tasks q₀
  let rec_now : ∀ q, ℭ.rel q q₀ → ℭ.R q := fun q _ => compute (inferInstance : Monad Id) tasks ι₀ q
  cacheUpdates (hI := hI) (hR := hR) (tasks := tasks) fetch
    (FM.evalTrace_deps ι₀ rec_now tree)
  let value := FM.evalTree ι₀ rec_now tree
  let h : value = compute (inferInstance : Monad Id) tasks ι₀ q₀ :=
    Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀
  pure ⟨value, h⟩

/
and `deps` are the hashed FM trace at `(ι_now, compute (inferInstance : Monad Id) tasks ι_now)`.
The invariant proof goes by `FM.evalTree_cross`, using injectivity
of `hI`, `hR` to lift hash agreement at each recorded position into
value agreement. -/
def buildMemoFM (ι_now : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (v : Value tasks ι_now q₀) :
    Memo (H := H) hI hR tasks q₀ :=
  let tree := Incremental.tasksTree ℭ tasks q₀
  let rec_now : ∀ q, ℭ.rel q q₀ → ℭ.R q := fun q _ => compute (inferInstance : Monad Id) tasks ι_now q
  let trace_in := FM.evalTrace_inputs ι_now rec_now tree
  let trace_dep := FM.evalTrace_deps ι_now rec_now tree
  { value := v.val
    inputDeps := trace_in.reverse.map (fun p => ⟨p.1, hI p.1 p.2⟩)
    deps := trace_dep.reverse.map
      (fun p => ⟨p.1, p.2.1, hR p.1 p.2.2⟩)
    invariant := by
      intro ι hin hdep
      have hv : v.val = compute (inferInstance : Monad Id) tasks ι_now q₀ := v.property
      rw [hv]
      rw [← Incremental.tasksTree_eval_compute ℭ tasks q₀ ι_now,
          ← Incremental.tasksTree_eval_compute ℭ tasks q₀ ι]
      apply FM.evalTree_cross ι_now ι rec_now (fun q _ => compute (inferInstance : Monad Id) tasks ι q) tree
      ·
        intro p hp
        have hmem :
            (⟨p.1, hI p.1 p.2⟩ : (i : ℭ.I) × H) ∈
              trace_in.reverse.map (fun p => ⟨p.1, hI p.1 p.2⟩) := by
          apply List.mem_map.mpr
          exact ⟨p, List.mem_reverse.mpr hp, rfl⟩
        have hash_eq := hin _ hmem
        exact (hI p.1).injective hash_eq
      ·
        intro p hp
        have hmem :
            (⟨p.1, p.2.1, hR p.1 p.2.2⟩ :
              Σ' (q : ℭ.Q) (_ : ℭ.rel q q₀), H) ∈
              trace_dep.reverse.map
                (fun p => ⟨p.1, p.2.1, hR p.1 p.2.2⟩) := by
          apply List.mem_map.mpr
          exact ⟨p, List.mem_reverse.mpr hp, rfl⟩
        have hash_eq := hdep _ hmem
        exact (hR p.1).injective hash_eq }

/-! ### The recursive fetch

Look up the cache at `q`.  On hit, verify both input fingerprints
and dep fingerprints (the latter recursively); if both check out,
the memo's invariant gives the cached value its correctness proof.
On miss or verification failure, recompute. -/

variable (tasks)

set_option linter.unusedVariables false in
def fetch (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateM (Cache (H := H) hI hR tasks) (Value tasks ι₀ q₀) := do
  let cache ← get
  match h : cache.get? q₀ with
  | some m =>
    if hin : verifyInputs hI ι₀ m.inputDeps = true then
      let hin' : ∀ p ∈ m.inputDeps, hI p.1 (ι₀ p.1) = p.2 :=
        (verifyInputs_iff (H := H) hI ι₀ m.inputDeps).mp hin
      match ← verifyDeps hI hR (fun q' _hq => fetch ι₀ q') m.deps with
      | some ⟨hdep⟩ =>
          pure ⟨m.value, m.invariant ι₀ hin' hdep⟩
      | none =>
          let v ← runRecompute hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
          modify (·.insert q₀ (buildMemoFM hI hR ι₀ q₀ v))
          pure v
    else
      let v ← runRecompute hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
      modify (·.insert q₀ (buildMemoFM hI hR ι₀ q₀ v))
      pure v
  | none =>
    let v ← runRecompute hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
    modify (·.insert q₀ (buildMemoFM hI hR ι₀ q₀ v))
    pure v
termination_by ℭ.wf.wrap q₀
decreasing_by all_goals exact _hq

end Shake

variable
  (ℭ : BuildConfig)
  (J : Type) [Input ℭ J]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  {H : Type} [DecidableEq H]

/
per-position embeddings into the hash type.  Pass
`Hashable.toEmbedding` for the `UInt64`-hash instantiation.

Each `build` call starts with an empty cache: the cache type
depends on `tasks`, supplied per-build. -/
public def Shake (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) :
    Build Monad ℭ J where
  cId := inferInstance
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q store :=
    let ι₀ := Input.get store
    let cache₀ : Shake.Cache (H := H) hI hR tasks := DHashMap.emptyWithCapacity 1024
    let (v, _) := Shake.fetch hI hR tasks ι₀ q cache₀
    (v, store)

end Incremental
