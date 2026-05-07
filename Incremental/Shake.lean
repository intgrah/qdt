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
      (∀ p ∈ deps, hR p.q (compute (inferInstance : Monad Id) tasks ι p.q) = p.h) →
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

abbrev RunState (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :=
  Store hI hR tasks ι₀ × List (ℭ.I × H) × List (DepEntry (H := H) q₀)

variable {tasks}

def verifyDeps {ι : ∀ i, ℭ.V i} {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι) (Value tasks ι q')) :
    (l : List (DepEntry (H := H) q₀)) → StateM (Store hI hR tasks ι) Bool
  | [] => pure true
  | ⟨q', hq, h⟩ :: rest => do
      let v ← fetch q' hq
      if hR q' v.val = h then verifyDeps fetch rest else pure false

def traceAction (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    MonadAction (StateM (RunState hI hR tasks ι₀ q₀)) (FM ℭ q₀) where
  rel {α β} P m t :=
    ∀ s,
      P (m.run s).1 (FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) t) ∧
      (m.run s).2.2.1 =
        (FM.evalTrace_inputs ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) t).reverse.map
          (fun p => (⟨p.1, hI p.1 p.2⟩ : ℭ.I × H)) ++ s.2.1 ∧
      (m.run s).2.2.2 =
        (FM.evalTrace_deps ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) t).reverse.map
          (fun p => (⟨p.1, p.2.1, hR p.1 p.2.2⟩ : DepEntry q₀)) ++ s.2.2
  rel_pure := fun hab s => ⟨hab, rfl, rfl⟩
  rel_bind := fun {α₁ α₂ β₁ β₂ R S ma mt ka kt} hma hk s => by
    obtain ⟨hv, hin, hdep⟩ := hma s
    obtain ⟨hv', hin', hdep'⟩ := hk _ _ hv (ma s).2
    refine ⟨?_, ?_, ?_⟩
    · show S (ka (ma s).1 (ma s).2).1 _
      rw [show FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) (mt >>= kt) =
        FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q)
          (kt (FM.evalTree ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q) mt)) from
        FM.evalTree_bind ..]
      exact hv'
    · show (ka (ma s).1 (ma s).2).2.2.1 = _
      rw [show (ka (ma s).1 (ma s).2) = (StateT.run (ka (StateT.run ma s).1) (ma s).2) from rfl]
      rw [hin', show (ma s).2.2.1 = (StateT.run ma s).2.2.1 from rfl, hin]
      show _ = List.map _ (FM.evalTrace_inputs _ _ (FM.bind mt kt)).reverse ++ _
      rw [FM.evalTrace_inputs_bind]
      simp [List.reverse_append, List.map_append, List.append_assoc]
    · show (ka (ma s).1 (ma s).2).2.2.2 = _
      rw [show (ka (ma s).1 (ma s).2) = (StateT.run (ka (StateT.run ma s).1) (ma s).2) from rfl]
      rw [hdep', show (ma s).2.2.2 = (StateT.run ma s).2.2.2 from rfl, hdep]
      show _ = List.map _ (FM.evalTrace_deps _ _ (FM.bind mt kt)).reverse ++ _
      rw [FM.evalTrace_deps_bind]
      simp [List.reverse_append, List.map_append, List.append_assoc]

def run (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q')) :
    StateM (Store hI hR tasks ι₀)
      { m : Memo (H := H) hI hR tasks q₀ //
        m.value = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀ } :=
  fun store =>
    let input' (i : ℭ.I) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.V i) :=
      fun (st, ins, deps) => (ι₀ i, (st, ⟨i, hI i (ι₀ i)⟩ :: ins, deps))
    let fetch' (q : ℭ.Q) (hq : ℭ.rel q q₀) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.R q) :=
      fun (st, ins, deps) =>
        let (v, st') := (fetch q hq) st
        (v.val, (st', ins, (⟨q, hq, hR q v.val⟩ : DepEntry q₀) :: deps))
    let m := tasks q₀ (StateM (RunState hI hR tasks ι₀ q₀)) input' fetch'
    let result := m (store, [], [])
    have hc := (Task.freeTheorem (tasks q₀) (traceAction hI hR ι₀ q₀)
      input' FM.pureInput fetch' FM.pureFetch
      (fun i s => ⟨rfl, rfl, rfl⟩)
      (fun q hq s => ⟨((fetch q hq) s.1).1.property, rfl, by
        show (⟨q, hq, hR q ((fetch q hq) s.1).1.val⟩ : DepEntry q₀) :: s.2.2 =
             (⟨q, hq, hR q (compute (inferInstanceAs (Monad Id)) tasks ι₀ q)⟩ : DepEntry q₀) :: s.2.2
        rw [((fetch q hq) s.1).1.property]⟩))
      (store, ([] : List (ℭ.I × H)), ([] : List (DepEntry (H := H) q₀)))
    have ⟨hval_tree, hinc, hdepc⟩ := hc
    let hval : result.1 = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀ :=
      hval_tree.trans (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀)
    (⟨⟨result.1, result.2.2.1, result.2.2.2, by
      intro ι hin hdep
      have hinc_s : result.2.2.1 =
          (FM.evalTrace_inputs ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q)
            (Incremental.tasksTree ℭ tasks q₀)).reverse.map
            (fun p => (⟨p.1, hI p.1 p.2⟩ : ℭ.I × H)) := by simpa using hinc
      have hdepc_s : result.2.2.2 =
          (FM.evalTrace_deps ι₀ (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q)
            (Incremental.tasksTree ℭ tasks q₀)).reverse.map
            (fun p => (⟨p.1, p.2.1, hR p.1 p.2.2⟩ : DepEntry q₀)) := by
        simpa using hdepc
      have step : FM.evalTree ι₀
            (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q)
            (Incremental.tasksTree ℭ tasks q₀) =
          FM.evalTree ι
            (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι q)
            (Incremental.tasksTree ℭ tasks q₀) := by
        apply FM.evalTree_cross
        · intro p hp
          have : (⟨p.1, hI p.1 p.2⟩ : ℭ.I × H) ∈ result.2.2.1 := by
            rw [hinc_s]; exact List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
          exact (hI p.1).injective (hin _ this)
        · intro p hp
          have : (⟨p.1, p.2.1, hR p.1 p.2.2⟩ : DepEntry q₀) ∈ result.2.2.2 := by
            rw [hdepc_s]; exact List.mem_map.mpr ⟨p, List.mem_reverse.mpr hp, rfl⟩
          exact (hR p.1).injective (hdep _ this)
      calc result.1
          = compute (inferInstanceAs (Monad Id)) tasks ι₀ q₀ := hval
        _ = FM.evalTree ι₀
              (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι₀ q)
              (Incremental.tasksTree ℭ tasks q₀) :=
            (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀).symm
        _ = FM.evalTree ι
              (fun q _ => compute (inferInstanceAs (Monad Id)) tasks ι q)
              (Incremental.tasksTree ℭ tasks q₀) := step
        _ = compute (inferInstanceAs (Monad Id)) tasks ι q₀ :=
            Incremental.tasksTree_eval_compute ℭ tasks q₀ ι⟩,
      hval⟩, result.2.1)

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
        let ⟨memo, hmemo⟩ ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
        let v : Value tasks ι₀ q₀ := ⟨memo.value, hmemo⟩
        let (vcache', ⟨cache', hcache'⟩) ← get
        let gc' : GoodCache hI hR tasks ι₀ :=
          ⟨cache'.insert q₀ memo, insertPreserves hI hR hcache' q₀ memo hmemo⟩
        set (vcache'.insert q₀ v, gc')
        pure v
    else do
      let ⟨memo, hmemo⟩ ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
      let v : Value tasks ι₀ q₀ := ⟨memo.value, hmemo⟩
      let (vcache', ⟨cache', hcache'⟩) ← get
      let gc' : GoodCache hI hR tasks ι₀ :=
        ⟨cache'.insert q₀ memo, insertPreserves hI hR hcache' q₀ memo hmemo⟩
      set (vcache'.insert q₀ v, gc')
      pure v
  | none => do
    let ⟨memo, hmemo⟩ ← run hI hR ι₀ q₀ (fun q' _hq => fetch ι₀ q')
    let v : Value tasks ι₀ q₀ := ⟨memo.value, hmemo⟩
    let (vcache', ⟨cache', hcache'⟩) ← get
    let gc' : GoodCache hI hR tasks ι₀ :=
      ⟨cache'.insert q₀ memo, insertPreserves hI hR hcache' q₀ memo hmemo⟩
    set (vcache'.insert q₀ v, gc')
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
