module

public import Incremental.Basic
public import Incremental.FreeTheorem
public import Incremental.FreeMonad
public import Incremental.IdealHash
public import Incremental.Shake.Store

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

structure InputDep (I H : Type) where
  key : I
  hash : H

structure QueryDep (ℭ : BuildConfig) (q₀ : ℭ.Q) (H : Type) where
  q : ℭ.Q
  rel : ℭ.rel q q₀
  hash : H

section verifyInputs
variable [DecidableEq H]

abbrev verifyInputs (ι : ∀ i, ℭ.V i) (l : Array (InputDep ℭ.I H)) : Bool :=
  l.all fun ⟨i, h⟩ => hI i (ι i) = h

theorem verifyInputs_spec (ι : ∀ i, ℭ.V i) (l : Array (InputDep ℭ.I H)) :
    verifyInputs hI ι l = true ↔ ∀ p ∈ l, hI p.key (ι p.key) = p.hash := by
  simp only [verifyInputs, Array.all_eq_true_iff_forall_mem, decide_eq_true_iff]

end verifyInputs

section dedupPush
variable [BEq ℭ.Q]

def dedupPush {q₀ : ℭ.Q} (e : QueryDep ℭ q₀ H)
    (acc : Array (QueryDep ℭ q₀ H)) :
    Array (QueryDep ℭ q₀ H) :=
  if acc.any (·.q == e.q) then acc else acc.push e

private theorem dedupPush_preserves_target {q₀ : ℭ.Q} {target : ℭ.Q → H}
    (e : QueryDep ℭ q₀ H)
    {acc : Array (QueryDep ℭ q₀ H)}
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

private theorem dedupPush_has_self {q₀ : ℭ.Q} [LawfulBEq ℭ.Q]
    (e : QueryDep ℭ q₀ H)
    (acc : Array (QueryDep ℭ q₀ H)) :
    ∃ y ∈ dedupPush e acc, y.q = e.q := by
  unfold dedupPush
  split_ifs with h
  · have ⟨y, hy_mem, hyq⟩ := Array.any_eq_true'.mp h
    exact ⟨y, hy_mem, LawfulBEq.eq_of_beq hyq⟩
  · exact ⟨e, Array.mem_push_self, rfl⟩

private theorem dedupPush_preserves_keys {q₀ : ℭ.Q}
    (e : QueryDep ℭ q₀ H) (acc : Array (QueryDep ℭ q₀ H)) :
    ∀ x ∈ acc, ∃ y ∈ dedupPush e acc, y.q = x.q := by
  intro x hx
  unfold dedupPush
  split_ifs
  · exact ⟨x, hx, rfl⟩
  · exact ⟨x, Array.mem_push_of_mem _ hx, rfl⟩

abbrev pushAll {q₀ : ℭ.Q} (l : List (Incremental.DepEntry ℭ q₀))
    (acc : Array (QueryDep ℭ q₀ H)) :
    Array (QueryDep ℭ q₀ H) :=
  l.foldl (fun acc p => dedupPush ⟨p.q, p.hq, hR p.q p.r⟩ acc) acc

private theorem pushAll_preserves_target {q₀ : ℭ.Q} {target : ℭ.Q → H}
    {l : List (Incremental.DepEntry ℭ q₀)}
    (h_uniform : ∀ p ∈ l, hR p.q p.r = target p.q)
    {acc : Array (QueryDep ℭ q₀ H)}
    (hacc : ∀ x ∈ acc, ∃ y ∈ acc, y.q = x.q ∧ y.hash = target x.q) :
    ∀ x ∈ pushAll hR l acc, ∃ y ∈ pushAll hR l acc, y.q = x.q ∧ y.hash = target x.q := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons hd rest ih =>
    apply ih (fun p hp => h_uniform p (List.mem_cons_of_mem _ hp))
    exact dedupPush_preserves_target ⟨hd.q, hd.hq, hR hd.q hd.r⟩ hacc
      (h_uniform hd List.mem_cons_self)

private theorem pushAll_preserves_keys {q₀ : ℭ.Q}
    {l : List (Incremental.DepEntry ℭ q₀)}
    {acc : Array (QueryDep ℭ q₀ H)} :
    ∀ x ∈ acc, ∃ y ∈ pushAll hR l acc, y.q = x.q := by
  induction l generalizing acc with
  | nil => intro x hx; exact ⟨x, hx, rfl⟩
  | cons hd rest ih =>
    intro x hx
    have ⟨y, hy_in, hy_q⟩ := dedupPush_preserves_keys
      ⟨hd.q, hd.hq, hR hd.q hd.r⟩ acc x hx
    have ⟨z, hz_in, hz_q⟩ := ih y hy_in
    exact ⟨z, hz_in, hz_q.trans hy_q⟩

private theorem pushAll_has_keys {q₀ : ℭ.Q} [LawfulBEq ℭ.Q]
    {l : List (Incremental.DepEntry ℭ q₀)}
    {acc : Array (QueryDep ℭ q₀ H)} :
    ∀ p ∈ l, ∃ y ∈ pushAll hR l acc, y.q = p.q := by
  induction l generalizing acc with
  | nil => nofun
  | cons hd rest ih =>
    rintro p (_ | ⟨_, hp_rest⟩)
    · have ⟨y, hy_in, hy_q⟩ := dedupPush_has_self ⟨hd.q, hd.hq, hR hd.q hd.r⟩ acc
      have ⟨z, hz_in, hz_q⟩ := pushAll_preserves_keys hR (l := rest) y hy_in
      exact ⟨z, hz_in, hz_q.trans hy_q⟩
    · exact ih p hp_rest

theorem pushAll_append {q₀ : ℭ.Q}
    (xs ys : List (Incremental.DepEntry ℭ q₀))
    (acc : Array (QueryDep ℭ q₀ H)) :
    pushAll hR (xs ++ ys) acc = pushAll hR ys (pushAll hR xs acc) :=
  List.foldl_append

theorem pushAll_complete {q₀ : ℭ.Q} {target : ℭ.Q → H} [LawfulBEq ℭ.Q]
    {l : List (Incremental.DepEntry ℭ q₀)}
    (h_uniform : ∀ p ∈ l, hR p.q p.r = target p.q) :
    ∀ p ∈ l, ∃ y ∈ pushAll hR l (#[] : Array (QueryDep ℭ q₀ H)),
      y.q = p.q ∧ y.hash = target p.q := by
  intro p hp
  have ⟨y, hy_in, hy_q⟩ := pushAll_has_keys hR (acc := #[]) p hp
  have ⟨z, hz_in, hz_q, hz_hash⟩ := pushAll_preserves_target hR (target := target)
    (acc := #[]) h_uniform nofun y hy_in
  exact ⟨z, hz_in, hz_q.trans hy_q, hy_q ▸ hz_q ▸ hz_hash⟩

end dedupPush

section main
variable [BEq ℭ.Q] [Hashable ℭ.Q]
  {m : Type → Type} [Monad m] [LawfulMonad m]
  [MonadAttach m] [LawfulMonadAttach m]

structure Memo (q : ℭ.Q) where
  value : ℭ.R q
  inputDeps : Array (InputDep ℭ.I H)
  deps : Array (QueryDep ℭ q H)
  invariant :
    ∀ (ι : ∀ i, ℭ.V i),
      (∀ p ∈ inputDeps, hI p.key (ι p.key) = p.hash) →
      (∀ p ∈ deps, hR p.q (computeM tasks ι p.q) = p.hash) →
      value = computeM tasks ι q

abbrev Cache := DHashMap ℭ.Q (Memo hI hR tasks)

abbrev VCache (ι : ∀ i, ℭ.V i) :=
  DHashMap ℭ.Q (fun q => { p : Value Id.instMonad tasks ι q × H // p.snd = hR q p.fst.val })

abbrev Store (ι : ∀ i, ℭ.V i) :=
  VCache hR tasks ι × Cache hI hR tasks

structure RunState (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) where
  store : Store hI hR tasks ι₀
  ins : Array (InputDep ℭ.I H)
  deps : Array (QueryDep ℭ q₀ H)

def traceAction (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    Task.Monad.Action (StateT (RunState hI hR tasks ι₀ q₀) m) (FM ℭ q₀) where
  rel {α β} P ma t :=
    ∀ s a s', MonadAttach.CanReturn (ma.run s) (a, s') →
      P a (FM.evalTree ι₀ (computeM tasks ι₀) t) ∧
      s'.ins = s.ins ++ ((FM.evalTrace_inputs ι₀ (computeM tasks ι₀) t).map
          (fun p => InputDep.mk p.i (hI p.i p.v))).toArray ∧
      s'.deps = pushAll hR (FM.evalTrace_deps ι₀ (computeM tasks ι₀) t) s.deps
  rel_pure {_ _ _ a _} hab s a' s' hcan := by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure
      (a := (a, s)) (b := (a', s')) hcan)
    refine ⟨hab, ?_, rfl⟩
    simp only [FM.evalTrace_inputs, List.map_nil, Array.append_empty]
  rel_bind {_ _ _ _ _ _ ma mt ka kt} hma hk s b s' hcan := by
    have ⟨⟨a, s''⟩, hma_can, hk_can⟩ :=
      LawfulMonadAttach.canReturn_bind_imp' (x := ma.run s) hcan
    have ⟨hv_a, hin_a, hdep_a⟩ := hma s a s'' hma_can
    have ⟨hv_b, hin_b, hdep_b⟩ := hk a _ hv_a s'' b s' hk_can
    refine ⟨FM.evalTree_bind .. ▸ hv_b, ?_, ?_⟩
    · change _ = _ ++ ((FM.evalTrace_inputs _ _ (FM.bind mt kt)).map _).toArray
      rw [FM.evalTrace_inputs_bind, hin_b, hin_a]
      simp only [Array.append_assoc, List.append_toArray, List.map_append]
    · change _ = pushAll _ (FM.evalTrace_deps _ _ (FM.bind mt kt)) _
      rw [FM.evalTrace_deps_bind, hdep_b, hdep_a, pushAll_append]

def runInput' (m : Type → Type) [Monad m] (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) (i : ℭ.I) :
    StateT (RunState hI hR tasks ι₀ q₀) m (ℭ.V i) :=
  fun s => pure (ι₀ i, { s with ins := s.ins.push ⟨i, hI i (ι₀ i)⟩ })

@[specialize bracket]
def runFetch' (m : Type → Type) [Monad m] (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (bracket : ∀ {α}, ℭ.Q → m α → m α)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m
        { vh : Value Id.instMonad tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val })
    (q : ℭ.Q) (hq : ℭ.rel q q₀) :
    StateT (RunState hI hR tasks ι₀ q₀) m (ℭ.R q) :=
  fun s => do
    let (⟨(v, h), _⟩, st') ← bracket q (fetch q hq s.store)
    pure (v.val, { s with store := st', deps := dedupPush ⟨q, hq, h⟩ s.deps })

theorem runInput'_rel (m : Type → Type) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    ∀ i, (traceAction hI hR tasks ι₀ q₀ (m := m)).rel Eq
      (runInput' hI hR tasks m ι₀ q₀ i) (FM.pureInput i) := by
  intro i s a s' hcan
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hcan)
  refine ⟨rfl, ?_, rfl⟩
  simp only [FM.pureInput, FM.evalTrace_inputs, List.map_cons, List.map_nil,
    Array.append_singleton]

theorem runFetch'_rel (m : Type → Type) [Monad m] [LawfulMonad m]
    [MonadAttach m] [LawfulMonadAttach m]
    (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (bracket : ∀ {α}, ℭ.Q → m α → m α)
    (bracket_canReturn : ∀ {α} (q : ℭ.Q) (x : m α) (a : α),
      MonadAttach.CanReturn (bracket q x) a → MonadAttach.CanReturn x a)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m
        { vh : Value Id.instMonad tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val }) :
    ∀ q hq, (traceAction hI hR tasks ι₀ q₀ (m := m)).rel Eq
      (runFetch' hI hR tasks m ι₀ q₀ bracket fetch q hq) (FM.pureFetch q hq) := by
  intro q hq s _ _ hcan
  have ⟨⟨r, _⟩, hbr_can, hrest⟩ := LawfulMonadAttach.canReturn_bind_imp' hcan
  have hfetch_can := bracket_canReturn q (fetch q hq s.store) _ hbr_can
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (LawfulMonadAttach.eq_of_canReturn_pure hrest)
  refine ⟨r.val.fst.spec, ?_, ?_⟩
  · simp only [FM.pureFetch, FM.evalTrace_inputs, List.map_nil, Array.append_empty]
  · show dedupPush ⟨q, hq, r.val.snd⟩ s.deps =
        dedupPush ⟨q, hq, hR q (computeM tasks ι₀ q)⟩ s.deps
    rw [r.property, r.val.fst.spec]

variable [DecidableEq H] [LawfulBEq ℭ.Q]

def verifyDepsList (ι₀ : ∀ i, ℭ.V i) {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m (Value Id.instMonad tasks ι₀ q')) :
    (l : List (QueryDep ℭ q₀ H)) →
    StateT (Store hI hR tasks ι₀) m
      (Option (PLift (∀ p ∈ l, hR p.q (computeM tasks ι₀ p.q) = p.hash)))
  | [] => pure (some ⟨nofun⟩)
  | e :: rest => do
      let v ← fetch e.q e.rel
      let (vc, _) ← get
      let cachedHash := match vc.get? e.q with
        | some ce => ce.val.snd
        | none => hR e.q v.val
      if heq : cachedHash = e.hash then do
        have hcache : cachedHash = hR e.q v.val := by
          dsimp only [cachedHash]
          split
          · next ce _ =>
            rw [ce.property]
            exact congrArg (hR e.q) (ce.val.fst.spec.trans v.spec.symm)
          · rfl
        match ← verifyDepsList ι₀ fetch rest with
        | some ⟨hrest⟩ => pure (some ⟨fun
            | _, .head _ => by
                show hR e.q (compute Id.instMonad tasks ι₀ e.q) = e.hash
                rw [← v.spec, ← hcache]; exact heq
            | p, .tail _ ht => hrest p ht⟩)
        | none => pure none
      else
        pure none

def verifyDeps (ι₀ : ∀ i, ℭ.V i) {q₀ : ℭ.Q}
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m (Value Id.instMonad tasks ι₀ q'))
    (arr : Array (QueryDep ℭ q₀ H)) :
    StateT (Store hI hR tasks ι₀) m
      (Option (PLift (∀ p ∈ arr, hR p.q (computeM tasks ι₀ p.q) = p.hash))) := do
  match ← verifyDepsList hI hR tasks ι₀ fetch arr.toList with
  | some ⟨hList⟩ => pure (some ⟨fun p hp => hList p hp.val⟩)
  | none => pure none

@[specialize bracket]
def run (ι₀ : ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (bracket : ∀ {α}, ℭ.Q → m α → m α)
    (bracket_canReturn : ∀ {α} (q : ℭ.Q) (x : m α) (a : α),
      MonadAttach.CanReturn (bracket q x) a → MonadAttach.CanReturn x a)
    (fetch : ∀ q' (_ : ℭ.rel q' q₀),
      StateT (Store hI hR tasks ι₀) m
        { vh : Value Id.instMonad tasks ι₀ q' × H // vh.snd = (hR q') vh.fst.val }) :
    StateT (Store hI hR tasks ι₀) m
      { mv : Memo hI hR tasks q₀ × Value Id.instMonad tasks ι₀ q₀ //
        mv.fst.value = mv.snd.val } := fun store => do
  let input' := runInput' hI hR tasks m ι₀ q₀
  let fetch' := runFetch' hI hR tasks m ι₀ q₀ bracket fetch
  let mTree := tasks q₀ (StateT (RunState hI hR tasks ι₀ q₀) m) input' fetch'
  let initState : RunState hI hR tasks ι₀ q₀ := ⟨store, #[], #[]⟩
  let hRel :=
    Task.Monad.freeTheorem (tasks q₀) (traceAction hI hR tasks ι₀ q₀)
      input' FM.pureInput fetch' FM.pureFetch
      (runInput'_rel hI hR tasks m ι₀ q₀)
      (runFetch'_rel hI hR tasks m ι₀ q₀ bracket bracket_canReturn fetch)
  MonadAttach.pbind (mTree initState) fun result hcan => do
    have ⟨hval_tree, hin_trace, hdep_trace⟩ := hRel initState result.fst result.snd hcan
    have hval : result.fst = computeM tasks ι₀ q₀ :=
      hval_tree.trans (Incremental.tasksTree_eval_compute ℭ tasks q₀ ι₀)
    have hin_trace' : result.snd.ins =
        ((FM.evalTrace_inputs ι₀ (computeM tasks ι₀) (tasksTree ℭ tasks q₀)).map
          fun p => ⟨p.i, hI p.i p.v⟩).toArray := by
      simpa only [initState, Array.empty_append] using hin_trace
    have hdep_trace' : result.snd.deps =
        pushAll hR (FM.evalTrace_deps ι₀ (computeM tasks ι₀) (tasksTree ℭ tasks q₀))
          (#[] : Array (QueryDep ℭ q₀ H)) := by
      simpa only [initState] using hdep_trace
    have hinvariant :
        ∀ (ι : ∀ i, ℭ.V i),
          (∀ p ∈ result.snd.ins, hI p.key (ι p.key) = p.hash) →
          (∀ p ∈ result.snd.deps, hR p.q (computeM tasks ι p.q) = p.hash) →
          result.fst = computeM tasks ι q₀ := by
      intro ι hin hdep
      have hin' : ∀ p ∈ FM.evalTrace_inputs ι₀ (computeM tasks ι₀) (tasksTree ℭ tasks q₀),
          ι p.i = p.v := fun p hp => (hI p.i).injective <|
        hin ⟨p.i, hI p.i p.v⟩ <| hin_trace' ▸ List.mem_toArray.mpr (List.mem_map_of_mem hp)
      have hdep' : ∀ p ∈ FM.evalTrace_deps ι₀ (computeM tasks ι₀) (tasksTree ℭ tasks q₀),
          computeM tasks ι p.q = p.r := by
        intro p hp
        have hpr := FM.evalTrace_deps_value _ _ _ _ hp
        have ⟨y, hy_in, hy_q, hy_hash⟩ := hdep_trace' ▸ pushAll_complete (hR := hR)
          (target := fun q => hR q (computeM tasks ι₀ q))
          (fun _ hp' => congrArg _ (FM.evalTrace_deps_value _ _ _ _ hp')) p hp
        apply (hR p.q).injective
        rw [hpr, ← hy_q, hdep y hy_in, hy_hash, hy_q]
      exact hval.trans (compute_cross ℭ tasks q₀ ι₀ ι hin' hdep')
    let memo : Memo hI hR tasks q₀ :=
      { value := result.fst
        inputDeps := result.snd.ins
        deps := result.snd.deps
        invariant := hinvariant }
    pure (⟨(memo, ⟨result.fst, hval⟩), rfl⟩, result.snd.store)

end main

end Shake

end Incremental
