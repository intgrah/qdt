module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IntrinsicHash
public import Incremental.ShakeStore

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap)

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

structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : List (ℭ.I × H)
  deps : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q), H)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.1 (ι p.1) = p.2) →
      (∀ p ∈ deps, hR p.1 (compute (inferInstance : Monad Id) tasks ι p.1) = p.2.2) →
      value = compute (inferInstance : Monad Id) tasks ι q

abbrev Cache := DHashMap ℭ.Q (Memo (H := H) hI hR tasks)

abbrev Value (ι : ∀ i, ℭ.V i) (q : ℭ.Q) :=
  { r : ℭ.R q // r = compute (inferInstanceAs (Monad Id)) tasks ι q }

abbrev VCache (ι : ∀ i, ℭ.V i) := DHashMap ℭ.Q (Value tasks ι)

def CacheCorrect (ι₀ : ∀ i, ℭ.V i) (cache : Cache (H := H) hI hR tasks) : Prop :=
  ∀ q (m : Memo (H := H) hI hR tasks q), cache.get? q = some m →
    m.value = compute (inferInstanceAs (Monad Id)) tasks ι₀ q

abbrev GoodCache (ι₀ : ∀ i, ℭ.V i) :=
  { c : Cache (H := H) hI hR tasks // CacheCorrect hI hR tasks ι₀ c }

abbrev Store (ι₀ : ∀ i, ℭ.V i) := VCache tasks ι₀ × GoodCache hI hR tasks ι₀

def verifyInputs (ι : ∀ i, ℭ.V i) :
    List (ℭ.I × H) → Bool
  | [] => true
  | ⟨i, h⟩ :: rest =>
    hI i (ι i) = h ∧ verifyInputs ι rest

theorem verifyInputs_iff (ι : ∀ i, ℭ.V i) (l : List (ℭ.I × H)) :
    verifyInputs (H := H) hI ι l = true ↔
      ∀ p ∈ l, hI p.1 (ι p.1) = p.2 := by
  induction l with
  | nil => simp [verifyInputs]
  | cons p rest ih => simp [verifyInputs, ih]

variable {tasks}

def verifyDeps {ι : ∀ i, ℭ.V i} {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι) (Value tasks ι q')) :
    (l : List (Σ' (q' : ℭ.Q) (_ : ℭ.rel q' q₀), H)) → StateM (Store hI hR tasks ι) Bool
  | [] => pure true
  | ⟨q', hq, _⟩ :: rest => do
      let _ ← fetch q' hq
      verifyDeps fetch rest

def action (ι₀ : ∀ i, ℭ.V i) :
    MonadAction (StateM (Store hI hR tasks ι₀)) Id where
  rel P m b := ∀ s, P (m s).1 b
  rel_pure := fun hab _ => hab
  rel_bind := fun hma hk s => hk _ _ (hma s) _

def run (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q')) :
    StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
  let ⟨r, hr⟩ ← MonadAttach.attach (tasks q₀ (StateM (Store hI hR tasks ι₀))
    (fun i => StateT.pure (ι₀ i))
    (fun q hq => Subtype.val <$> fetch q hq))
  have : r = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀ := by
    obtain ⟨s, s', heq⟩ := hr
    have hft := Tasks.freeTheorem tasks q₀ (action hI hR ι₀)
      ι₀
      (fun i => StateT.pure (ι₀ i))
      (fun q hq => Subtype.val <$> fetch q hq)
      (fun i s => rfl)
      (fun q hq s => fetch q hq |>.run' s |>.property) s
    exact (congrArg Prod.fst heq).symm.trans hft
  return ⟨r, this⟩

def buildMemo (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (v : Value tasks ι₀ q₀)
    (vcache : VCache tasks ι₀) :
    Memo (H := H) hI hR tasks q₀ :=
  let tree := Incremental.tasksTree ℭ tasks q₀
  let rec_now : ∀ q, ℭ.rel q q₀ → ℭ.R q := fun q _hq =>
    match vcache.get? q with
    | some v => v.val
    | none => compute (inferInstanceAs (Monad Id)) tasks ι₀ q
  let trace_in := FM.evalTrace_inputs ι₀ rec_now tree
  let trace_dep := FM.evalTrace_deps ι₀ rec_now tree
  { value := v.val
    inputDeps := trace_in.reverse.map (fun p => ⟨p.1, hI p.1 p.2⟩)
    deps := trace_dep.reverse.map (fun p => ⟨p.1, p.2.1, hR p.1 p.2.2⟩)
    invariant := by
      intro ι hin hdep
      have rec_eq : ∀ q (hq : ℭ.rel q q₀), rec_now q hq = compute (inferInstanceAs (Monad Id)) tasks ι₀ q := by
        intro q hq; simp only [rec_now]; split
        · next v hget => exact v.property
        · rfl
      have step1 : FM.evalTree ι₀ rec_now tree =
          FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) tree := by
        apply FM.evalTree_cross
        · intro p hp; exact (FM.evalTrace_inputs_value ι₀ rec_now tree p hp).symm
        · intro p hp; rw [FM.evalTrace_deps_value ι₀ rec_now tree p hp]; exact (rec_eq p.1 p.2.1).symm
      have step2 : FM.evalTree ι₀ rec_now tree =
          FM.evalTree ι (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι q) tree := by
        apply FM.evalTree_cross
        · intro p hp
          exact (hI p.1).injective (hin ⟨p.1, hI p.1 p.2⟩
            (List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩))
        · intro p hp
          exact (hR p.1).injective (hdep ⟨p.1, p.2.1, hR p.1 p.2.2⟩
            (List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩))
      calc v.val
          = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀ := v.property
        _ = FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) tree :=
            (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀).symm
        _ = FM.evalTree ι₀ rec_now tree := step1.symm
        _ = FM.evalTree ι (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι q) tree := step2
        _ = compute (inferInstanceAs (Monad Id)) tasks ι q₀ :=
            Incremental.tasksTree_eval_compute ℭ tasks q₀ ι }

def insertPreserves {ι₀ : ∀ i, ℭ.V i} {cache : Cache (H := H) hI hR tasks}
    (hcache : CacheCorrect hI hR tasks ι₀ cache) (q₀ : ℭ.Q)
    (memo : Memo (H := H) hI hR tasks q₀)
    (hval : memo.value = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀) :
    CacheCorrect hI hR tasks ι₀ (cache.insert q₀ memo) := by
  intro q m hget
  by_cases heq : q₀ == q
  · have := LawfulBEq.eq_of_beq heq; subst this
    rw [DHashMap.get?_insert_self] at hget
    obtain rfl := Option.some.inj hget
    exact hval
  · simp [DHashMap.get?_insert, heq] at hget
    exact hcache q m hget

variable (tasks)

set_option linter.unusedVariables false in
def fetch (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
  let (vcache, ⟨cache, hcache⟩) ← get
  if let some v := vcache.get? q₀ then return v
  match h : cache.get? q₀ with
  | some m =>
    if verifyInputs hI ι₀ m.inputDeps then
      if ← verifyDeps hI hR (fun q' _hq => fetch ι₀ q') m.deps then
        let v : Value tasks ι₀ q₀ := ⟨m.value, hcache q₀ m h⟩
        modify fun (vc, gc) => (vc.insert q₀ v, gc)
        pure v
      else do
        let v ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
        modify fun (vc, gc) => (vc.insert q₀ v, gc)
        pure v
    else do
      let v ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
      modify fun (vc, gc) => (vc.insert q₀ v, gc)
      pure v
  | none => do
    let v ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
    modify fun (vc, gc) => (vc.insert q₀ v, gc)
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

public def Shake (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) :
    Build Monad ℭ J where
  cId := inferInstance
  σ := J
  init := id
  inputs := Input.get
  set i v := modify fun store => Input.set store i v
  build tasks q store :=
    let ι₀ := Input.get store
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024,
       ⟨DHashMap.emptyWithCapacity 1024, fun q m h => by simp_all [DHashMap.get?_emptyWithCapacity]⟩)
    let (v, _) := Shake.fetch hI hR tasks ι₀ q initStore
    (v, store)

end Incremental
