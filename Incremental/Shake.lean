module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IdealHash
public import Incremental.ShakeStore

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

abbrev eval : (∀ i, ℭ.V i) → ∀ q : ℭ.Q, ℭ.R q :=
  compute Id.instMonad tasks

structure InputDep (I H : Type) where
  key : I
  hash : H

structure DepEntry (q₀ : ℭ.Q) where
  q : ℭ.Q
  rel : ℭ.rel q q₀
  hash : H

abbrev Value (ι : ∀ i, ℭ.V i) (q : ℭ.Q) :=
  { r : ℭ.R q // r = eval tasks ι q }

section verifyInputs
variable [DecidableEq H]

abbrev verifyInputs (ι : ∀ i, ℭ.V i) (l : List (InputDep ℭ.I H)) : Bool :=
  l.all fun ⟨i, h⟩ => hI i (ι i) = h

theorem verifyInputs_spec (ι : ∀ i, ℭ.V i) (l : List (InputDep ℭ.I H)) :
    verifyInputs hI ι l = true ↔ ∀ p ∈ l, hI p.key (ι p.key) = p.hash := by
  simp only [verifyInputs, List.all_eq_true, decide_eq_true_iff]

end verifyInputs

section dedupPush
variable [BEq ℭ.Q]

/-- Append `e` to `acc` unless some entry with the same `q` already exists. -/
def dedupPush {q₀ : ℭ.Q} (e : DepEntry (H := H) q₀)
    (acc : Array (DepEntry (H := H) q₀)) :
    Array (DepEntry (H := H) q₀) :=
  if acc.any (·.q == e.q) then acc else acc.push e

/-- `dedupPush` preserves the invariant that every entry's key is represented by some
    entry with hash matching `target`. -/
private theorem dedupPush_preserves_target {q₀ : ℭ.Q} {target : ℭ.Q → H}
    (e : DepEntry (H := H) q₀)
    {acc : Array (DepEntry (H := H) q₀)}
    (hacc : ∀ x ∈ acc, ∃ y ∈ acc, y.q = x.q ∧ y.hash = target x.q)
    (he_target : e.hash = target e.q) :
    ∀ x ∈ dedupPush e acc, ∃ y ∈ dedupPush e acc, y.q = x.q ∧ y.hash = target x.q := by
  unfold dedupPush
  split_ifs with h
  · exact hacc
  · intro x hx
    simp only [Array.mem_push] at hx
    rcases hx with hx | rfl
    · have ⟨y, hy_mem, hy_q, hy_hash⟩ := hacc x hx
      exact ⟨y, Array.mem_push_of_mem _ hy_mem, hy_q, hy_hash⟩
    · exact ⟨x, Array.mem_push_self, rfl, he_target⟩

/-- After `dedupPush`, the new entry's key has at least one representative. -/
private theorem dedupPush_has_self {q₀ : ℭ.Q} [LawfulBEq ℭ.Q]
    (e : DepEntry (H := H) q₀)
    (acc : Array (DepEntry (H := H) q₀)) :
    ∃ y ∈ dedupPush e acc, y.q = e.q := by
  unfold dedupPush
  split_ifs with h
  · have ⟨y, hy_mem, hyq⟩ := Array.any_eq_true'.mp h
    exact ⟨y, hy_mem, LawfulBEq.eq_of_beq hyq⟩
  · exact ⟨e, Array.mem_push_self, rfl⟩

/-- Every existing key remains represented after `dedupPush`. -/
private theorem dedupPush_preserves_keys {q₀ : ℭ.Q}
    (e : DepEntry (H := H) q₀) (acc : Array (DepEntry (H := H) q₀)) :
    ∀ x ∈ acc, ∃ y ∈ dedupPush e acc, y.q = x.q := by
  intro x hx
  unfold dedupPush
  split_ifs
  · exact ⟨x, hx, rfl⟩
  · exact ⟨x, Array.mem_push_of_mem _ hx, rfl⟩

/-- Iterated `dedupPush` over a list of `DepEntry`s. -/
abbrev pushAll {q₀ : ℭ.Q} (l : List (Incremental.DepEntry ℭ q₀))
    (acc : Array (DepEntry (H := H) q₀)) :
    Array (DepEntry (H := H) q₀) :=
  l.foldl (fun acc p => dedupPush ⟨p.q, p.hq, hR p.q p.r⟩ acc) acc

/-- `pushAll` preserves the target-invariant if `target` agrees with each entry's hash. -/
private theorem pushAll_preserves_target {q₀ : ℭ.Q} {target : ℭ.Q → H}
    {l : List (Incremental.DepEntry ℭ q₀)}
    (h_uniform : ∀ p ∈ l, hR p.q p.r = target p.q)
    {acc : Array (DepEntry (H := H) q₀)}
    (hacc : ∀ x ∈ acc, ∃ y ∈ acc, y.q = x.q ∧ y.hash = target x.q) :
    ∀ x ∈ pushAll hR l acc, ∃ y ∈ pushAll hR l acc, y.q = x.q ∧ y.hash = target x.q := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd rest ih =>
    apply ih (fun p hp => h_uniform p (List.mem_cons_of_mem _ hp))
    exact dedupPush_preserves_target ⟨hd.q, hd.hq, hR hd.q hd.r⟩ hacc
      (h_uniform hd List.mem_cons_self)

/-- `pushAll` preserves all existing keys. -/
private theorem pushAll_preserves_keys {q₀ : ℭ.Q}
    {l : List (Incremental.DepEntry ℭ q₀)}
    {acc : Array (DepEntry (H := H) q₀)} :
    ∀ x ∈ acc, ∃ y ∈ pushAll hR l acc, y.q = x.q := by
  induction l generalizing acc with
  | nil => exact fun x hx => ⟨x, hx, rfl⟩
  | cons hd rest ih =>
    intro x hx
    have ⟨y, hy_in, hy_q⟩ := dedupPush_preserves_keys
      ⟨hd.q, hd.hq, hR hd.q hd.r⟩ acc x hx
    have ⟨z, hz_in, hz_q⟩ := ih y hy_in
    exact ⟨z, hz_in, hz_q.trans hy_q⟩

/-- After `pushAll`, every key in the input list is represented. -/
private theorem pushAll_has_keys {q₀ : ℭ.Q} [LawfulBEq ℭ.Q]
    {l : List (Incremental.DepEntry ℭ q₀)}
    {acc : Array (DepEntry (H := H) q₀)} :
    ∀ p ∈ l, ∃ y ∈ pushAll hR l acc, y.q = p.q := by
  induction l generalizing acc with
  | nil => nofun
  | cons hd rest ih => exact fun
    | _, .head _ =>
      have ⟨y, hy_in, hy_q⟩ := dedupPush_has_self ⟨hd.q, hd.hq, hR hd.q hd.r⟩ acc
      have ⟨z, hz_in, hz_q⟩ := pushAll_preserves_keys hR (l := rest) y hy_in
      ⟨z, hz_in, hz_q.trans hy_q⟩
    | p, .tail _ hp_rest => ih p hp_rest

/-- The completeness lemma: after `pushAll`, every input key has an entry with
    matching hash. -/
private theorem pushAll_complete {q₀ : ℭ.Q} {target : ℭ.Q → H} [LawfulBEq ℭ.Q]
    {l : List (Incremental.DepEntry ℭ q₀)}
    (h_uniform : ∀ p ∈ l, hR p.q p.r = target p.q) :
    ∀ p ∈ l, ∃ y ∈ pushAll hR l (#[] : Array (DepEntry (H := H) q₀)),
      y.q = p.q ∧ y.hash = target p.q := by
  intro p hp
  have ⟨y, hy_in, hy_q⟩ := pushAll_has_keys hR (acc := #[]) p hp
  have ⟨z, hz_in, hz_q, hz_hash⟩ := pushAll_preserves_target hR (target := target)
    (acc := #[]) h_uniform nofun y hy_in
  exact ⟨z, hz_in, hz_q.trans hy_q, hy_q ▸ hz_q ▸ hz_hash⟩

end dedupPush

section main
variable [DecidableEq H] [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : List (InputDep ℭ.I H)
  deps : Array (DepEntry (H := H) q)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.key (ι p.key) = p.hash) →
      (∀ p ∈ deps, hR p.q (eval tasks ι p.q) = p.hash) →
      value = eval tasks ι q

abbrev Cache := DHashMap ℭ.Q (Memo hI hR tasks)

abbrev VCache (ι : ∀ i, ℭ.V i) :=
  DHashMap ℭ.Q (fun q => { p : Value tasks ι q × H // p.snd = hR q p.fst.val })

abbrev Store (ι : ∀ i, ℭ.V i) :=
  VCache hR tasks ι × Cache hI hR tasks × HashSet ℭ.Q

structure RunState (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) where
  store : Store hI hR tasks ι₀
  ins : List (InputDep ℭ.I H)
  deps : Array (DepEntry (H := H) q₀)

def verifyDepsList (ι₀ : ∀ i, ℭ.V i) {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q')) :
    (l : List (DepEntry (H := H) q₀)) →
    StateM (Store hI hR tasks ι₀)
      (Option (PLift (∀ p ∈ l, hR p.q (eval tasks ι₀ p.q) = p.hash)))
  | [] => pure (some ⟨nofun⟩)
  | e :: rest => do
      let v ← fetch e.q e.rel
      let (vc, _, _) ← get
      let cachedHash := match vc.get? e.q with
        | some ce => ce.val.snd
        | none => hR e.q v.val
      if heq : cachedHash = e.hash then do
        have hcache : cachedHash = hR e.q v.val := by
          dsimp only [cachedHash]
          split
          · next ce _ =>
            rw [ce.property]
            exact congrArg (hR e.q) (ce.val.fst.property.trans v.property.symm)
          · rfl
        match ← verifyDepsList ι₀ fetch rest with
        | some ⟨hrest⟩ => pure (some ⟨fun
            | _, .head _ => by rw [← v.property, ← hcache]; exact heq
            | p, .tail _ ht => hrest p ht⟩)
        | none => pure none
      else
        pure none

def verifyDeps (ι₀ : ∀ i, ℭ.V i) {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q'))
    (arr : Array (DepEntry (H := H) q₀)) :
    StateM (Store hI hR tasks ι₀)
      (Option (PLift (∀ p ∈ arr, hR p.q (eval tasks ι₀ p.q) = p.hash))) := do
  match ← verifyDepsList hI hR tasks ι₀ fetch arr.toList with
  | some ⟨hList⟩ => pure (some ⟨fun p hp => hList p hp.val⟩)
  | none => pure none

def traceAction (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    Task.Monad.Action (StateM (RunState hI hR tasks ι₀ q₀)) (FM ℭ q₀) where
  rel {α β} P m t :=
    ∀ s,
      P (m.run s).fst (FM.evalTree ι₀ (eval tasks ι₀) t) ∧
      (m.run s).snd.ins =
        (FM.evalTrace_inputs ι₀ (eval tasks ι₀) t).reverse.map
          (fun p => InputDep.mk p.i (hI p.i p.v)) ++ s.ins ∧
      (m.run s).snd.deps = pushAll hR (FM.evalTrace_deps ι₀ (eval tasks ι₀) t) s.deps
  rel_pure hab s := ⟨hab, rfl, rfl⟩
  rel_bind {α₁ α₂ β₁ β₂ R S ma mt ka kt} hma hk s := by
    have ⟨hv, hin, hdep⟩ := hma s
    have ⟨hv', hin', hdep'⟩ := hk _ _ hv (StateT.run ma s).snd
    have hbind : StateT.run (ma >>= ka) s =
        StateT.run (ka (StateT.run ma s).fst) (StateT.run ma s).snd := rfl
    refine ⟨?_, ?_, ?_⟩
    · change S _ (FM.evalTree _ _ (FM.bind mt kt))
      rw [FM.evalTree_bind]
      exact hv'
    · change _ = (FM.evalTrace_inputs _ _ (FM.bind mt kt)).reverse.map _ ++ _
      rw [congrArg (·.snd.ins) hbind, hin', hin, FM.evalTrace_inputs_bind]
      simp only [List.reverse_append, List.map_append, List.append_assoc]
    · change _ = pushAll _ (FM.evalTrace_deps _ _ (FM.bind mt kt)) _
      rw [congrArg (·.snd.deps) hbind, hdep', hdep, FM.evalTrace_deps_bind]
      simp only [pushAll, List.foldl_append]

def run (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateM (Store hI hR tasks ι₀)
        { vh : Value tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val }) :
    StateM (Store hI hR tasks ι₀)
      { mv : Memo hI hR tasks q₀ × Value tasks ι₀ q₀ //
        mv.fst.value = mv.snd.val } :=
  fun store =>
    let input' (i : ℭ.I) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.V i) :=
      fun s => (ι₀ i, { s with ins := ⟨i, hI i (ι₀ i)⟩ :: s.ins })
    let fetch' (q : ℭ.Q) (hq : ℭ.rel q q₀) : StateM (RunState hI hR tasks ι₀ q₀) (ℭ.R q) :=
      fun s =>
        let (⟨(v, h), _⟩, st') := fetch q hq s.store
        (v.val, { s with store := st', deps := dedupPush ⟨q, hq, h⟩ s.deps })
    let m := tasks q₀ (StateM (RunState hI hR tasks ι₀ q₀)) input' fetch'
    let initState : RunState hI hR tasks ι₀ q₀ := ⟨store, [], #[]⟩
    let result := m initState
    have ⟨hval_tree, hin_trace, hdep_trace⟩ :=
      Task.Monad.freeTheorem (tasks q₀) (traceAction hI hR tasks ι₀ q₀)
        input' FM.pureInput fetch' FM.pureFetch
        (fun _ _ => ⟨rfl, rfl, rfl⟩)
        (fun q hq s =>
          let r := (fetch q hq s.store).fst
          ⟨r.val.fst.property, rfl, by
            show dedupPush ⟨q, hq, r.val.snd⟩ s.deps =
                 dedupPush ⟨q, hq, hR q (eval tasks ι₀ q)⟩ s.deps
            rw [r.property, r.val.fst.property]⟩)
        initState
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
    (⟨(memo, ⟨result.fst, hval⟩), rfl⟩, result.snd.store)

def fetch (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
  let (vcache, cache, inFlight) ← get
  if let some ⟨(v, _), _⟩ := vcache.get? q₀ then return v
  let fetchWithHash (q' : ℭ.Q) (_ : ℭ.rel q' q₀) :
      StateM (Store hI hR tasks ι₀)
        { vh : Value tasks ι₀ q' × H // vh.2 = (hR q') vh.1.val } := do
    let v ← fetch ι₀ q'
    let (vc, _, _) ← get
    match vc.get? q' with
    | some e => pure ⟨(v, e.val.snd), by
        rw [e.property]
        exact congrArg (hR q') (e.val.fst.property.trans v.property.symm)⟩
    | none => pure ⟨(v, hR q' v.val), rfl⟩
  let doRun : StateM (Store hI hR tasks ι₀) (Value tasks ι₀ q₀) := do
    let ⟨(memo, value), _⟩ ← run hI hR tasks ι₀ q₀ fetchWithHash
    modify fun (vc, c, ifl) =>
      (vc.insert q₀ ⟨(value, hR q₀ value.val), rfl⟩, c.insert q₀ memo, ifl)
    pure value
  if inFlight.contains q₀ then doRun
  else do
    modify fun (vc, c, ifl) => (vc, c, ifl.insert q₀)
    let result ←
      match cache.get? q₀ with
      | some m =>
        if hvin : verifyInputs hI ι₀ m.inputDeps then do
          match ← verifyDeps hI hR tasks ι₀ (fun q' hq => fetch ι₀ q') m.deps with
          | some ⟨hdep⟩ =>
            let value : Value tasks ι₀ q₀ := ⟨m.value, m.invariant ι₀
              ((verifyInputs_spec hI ι₀ m.inputDeps).mp hvin) hdep⟩
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
  inputs s := Input.get s.fst
  set i v := modify fun (j, c) => (Input.set j i v, c)
  build q store :=
    let (j, oldCache) := store
    let ι₀ := Input.get j
    let initStore : Shake.Store hI hR tasks ι₀ :=
      (DHashMap.emptyWithCapacity 1024, oldCache, ∅)
    let (v, (_, newCache, _)) := Shake.fetch hI hR tasks ι₀ q initStore
    (v, (j, newCache))

end Incremental
