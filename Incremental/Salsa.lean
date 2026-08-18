module

public import Incremental.Basic
public import Incremental.FreeMonad
public import Incremental.IdealHash
public import Mathlib.Data.Erased

@[expose] public section

namespace Incremental

open Std (DHashMap HashMap)

namespace Salsa

variable {ℭ : BuildConfig}

section

variable
  {H : Type}
  [BEq ℭ.I] [Hashable ℭ.I] [BEq ℭ.Q] [Hashable ℭ.Q]

structure Memo (ℭ : BuildConfig) (H : Type) (q : ℭ.Q) where
  value : ℭ.R q
  hash : H
  changedAt : Nat
  verifiedAt : Nat
  inputDeps : Array (InputDep ℭ.I)
  queryDeps : Array (QueryDep ℭ q)

abbrev Memos (ℭ : BuildConfig) [BEq ℭ.Q] [Hashable ℭ.Q] (H : Type) :=
  DHashMap ℭ.Q (Memo ℭ H)

structure RunState (ℭ : BuildConfig) [BEq ℭ.Q] [Hashable ℭ.Q] (H : Type) (q₀ : ℭ.Q) where
  ins : Array (InputDep ℭ.I)
  deps : Array (QueryDep ℭ q₀)
  memos : Memos ℭ H

structure Ctx (ℭ : BuildConfig) [BEq ℭ.I] [Hashable ℭ.I] (H : Type) where
  hR : ∀ q, ℭ.R q ↪ H
  tasks : Tasks ℭ
  ι₀ : ∀ i, ℭ.V i
  revision : Nat
  inputRevisions : HashMap ℭ.I Nat

structure Store (ℭ : BuildConfig) [BEq ℭ.I] [Hashable ℭ.I] [BEq ℭ.Q] [Hashable ℭ.Q]
    (H : Type) (J : Type) where
  inputs : J
  revision : Nat
  memos : Memos ℭ H
  inputRevisions : HashMap ℭ.I Nat
  history : Erased (Nat → ∀ i, ℭ.V i)

variable [LawfulBEq ℭ.Q] [DecidableEq H]

def runInput (c : Ctx ℭ H) (q₀ : ℭ.Q) (i : ℭ.I) :
    StateT (RunState ℭ H q₀) Id (ℭ.V i) :=
  fun s => (c.ι₀ i, { s with ins := s.ins.push ⟨i⟩ })

def runFetch (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (q' : ℭ.Q) (hq' : ℭ.rel q' q₀) : StateT (RunState ℭ H q₀) Id (ℭ.R q') :=
  fun s =>
    let (v, ms') := fetchRec q' hq' s.memos
    (v, { s with deps := s.deps.push ⟨q', hq'⟩, memos := ms' })

def reExec (c : Ctx ℭ H)
    (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q')) :
    StateM (Memos ℭ H)
      (ℭ.R q₀ × Array (InputDep ℭ.I) × Array (QueryDep ℭ q₀)) :=
  fun ms =>
    let (v, s) := (c.tasks q₀).fn _ (runInput c q₀) (runFetch q₀ fetchRec) ⟨#[], #[], ms⟩
    ((v, s.ins, s.deps), s.memos)

def insertReExec (c : Ctx ℭ H) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q')) :
    StateM (Memos ℭ H) (ℭ.R q₀) := do
  let (v, ins, deps) ← reExec c q₀ fetchRec
  let h := c.hR q₀ v
  let changedAt :=
    match (← get).get? q₀ with
    | some m => if h == m.hash then m.changedAt else c.revision
    | none => c.revision
  modify (·.insert q₀
    { value := v, hash := h, changedAt, verifiedAt := c.revision,
      inputDeps := ins, queryDeps := deps })
  return v

def verifyDeps (c : Ctx ℭ H) (q₀ : ℭ.Q) (V : Nat)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q')) :
    List (QueryDep ℭ q₀) → StateM (Memos ℭ H) Bool
  | [] => fun memos => (true, memos)
  | ⟨q', hq'⟩ :: rest => fun memos =>
    let s₁ := (fetchRec q' hq' memos).2
    match s₁.get? q' with
    | some m' =>
      if m'.verifiedAt == c.revision ∧ m'.changedAt ≤ V then
        verifyDeps c q₀ V fetchRec rest s₁
      else (false, s₁)
    | none => (false, s₁)

def inputsClean (c : Ctx ℭ H) (V : Nat) (inputDeps : Array (InputDep ℭ.I)) : Bool :=
  inputDeps.all fun ⟨i⟩ => c.inputRevisions.getD i 0 ≤ V

def fetch (c : Ctx ℭ H) (q₀ : ℭ.Q) : StateM (Memos ℭ H) (ℭ.R q₀) := fun memos =>
  let fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q') :=
    fun q' _hq => fetch c q'
  match memos.get? q₀ with
  | some m =>
    if m.verifiedAt == c.revision then (m.value, memos)
    else if inputsClean c m.verifiedAt m.inputDeps then
      if (verifyDeps c q₀ m.verifiedAt fetchRec m.queryDeps.toList memos).1 then
        (m.value, (verifyDeps c q₀ m.verifiedAt fetchRec m.queryDeps.toList memos).2.insert q₀
          { m with verifiedAt := c.revision })
      else insertReExec c q₀ fetchRec
        (verifyDeps c q₀ m.verifiedAt fetchRec m.queryDeps.toList memos).2
    else insertReExec c q₀ fetchRec memos
  | none => insertReExec c q₀ fetchRec memos
termination_by ℭ.wf.wrap q₀

end

theorem rel_irrefl : ∀ q : ℭ.Q, ¬ ℭ.rel q q := by
  intro q
  induction q using ℭ.wf.induction with
  | _ x ih => exact fun h => ih x h h

theorem rel_ne {q q₀ : ℭ.Q} (h : ℭ.rel q q₀) : q ≠ q₀ :=
  fun heq => rel_irrefl q₀ (heq ▸ h)

theorem transGen_acc {q : ℭ.Q} (hacc : Acc ℭ.rel q) :
    ¬ Relation.TransGen ℭ.rel q q := by
  induction hacc with
  | intro x _ ih =>
    intro ht
    cases ht with
    | single hr => exact rel_irrefl x hr
    | tail hp hl => exact ih _ hl (Relation.TransGen.head hl hp)

theorem transGen_irrefl (q : ℭ.Q) : ¬ Relation.TransGen ℭ.rel q q :=
  transGen_acc (ℭ.wf.apply q)

theorem evalTrace_inputs_cross {q₀ : ℭ.Q} {α : Type} (ι ι' : ∀ i, ℭ.V i)
    (rec rec' : ∀ q, ℭ.R q) (t : FM ℭ q₀ α)
    (hin : ∀ p ∈ FM.evalTrace_inputs ι rec t, ι' p.i = p.v)
    (hdep : ∀ p ∈ FM.evalTrace_deps ι rec t, rec' p.q = p.r) :
    FM.evalTrace_inputs ι rec t = FM.evalTrace_inputs ι' rec' t := by
  induction t with
  | pure a => rfl
  | input i k ih =>
    have hi : ι i = ι' i := (hin ⟨i, ι i⟩ (.head _)).symm
    show (⟨i, ι i⟩ : InputEntry ℭ) :: _ = ⟨i, ι' i⟩ :: _
    rw [← hi, ih (ι i) (fun p hp => hin p (.tail _ hp)) hdep]
  | fetch q hq k ih =>
    have hr : rec q = rec' q := (hdep ⟨q, hq, rec q⟩ (.head _)).symm
    show FM.evalTrace_inputs ι rec (k (rec q)) = FM.evalTrace_inputs ι' rec' (k (rec' q))
    rw [← hr]
    exact ih (rec q) hin (fun p hp => hdep p (.tail _ hp))

theorem evalTrace_deps_cross {q₀ : ℭ.Q} {α : Type} (ι ι' : ∀ i, ℭ.V i)
    (rec rec' : ∀ q, ℭ.R q) (t : FM ℭ q₀ α)
    (hin : ∀ p ∈ FM.evalTrace_inputs ι rec t, ι' p.i = p.v)
    (hdep : ∀ p ∈ FM.evalTrace_deps ι rec t, rec' p.q = p.r) :
    FM.evalTrace_deps ι rec t = FM.evalTrace_deps ι' rec' t := by
  induction t with
  | pure a => rfl
  | input i k ih =>
    have hi : ι i = ι' i := (hin ⟨i, ι i⟩ (.head _)).symm
    show FM.evalTrace_deps ι rec (k (ι i)) = FM.evalTrace_deps ι' rec' (k (ι' i))
    rw [← hi]
    exact ih (ι i) (fun p hp => hin p (.tail _ hp)) hdep
  | fetch q hq k ih =>
    have hr : rec q = rec' q := (hdep ⟨q, hq, rec q⟩ (.head _)).symm
    show (⟨q, hq, rec q⟩ : DepEntry ℭ q₀) :: _ = ⟨q, hq, rec' q⟩ :: _
    rw [← hr, ih (rec q) hin (fun p hp => hdep p (.tail _ hp))]

theorem evalTrace_inputs_value {q₀ : ℭ.Q} {α : Type} (ι : ∀ i, ℭ.V i) (rec : ∀ q, ℭ.R q)
    (t : FM ℭ q₀ α) : ∀ p ∈ FM.evalTrace_inputs ι rec t, p.v = ι p.i := by
  induction t with
  | pure _ => nofun
  | input i k ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hr
    · rfl
    · exact ih (ι i) p hr
  | fetch q hq k ih => exact ih (rec q)

section

variable
  {H : Type}
  [BEq ℭ.Q] [Hashable ℭ.Q] [LawfulBEq ℭ.Q]

def Extends (revision : Nat) (memos memos' : Memos ℭ H) : Prop :=
  ∀ q m, memos.get? q = some m → ∃ m', memos'.get? q = some m' ∧
    ((m'.changedAt = m.changedAt ∧ m'.value = m.value) ∨ revision ≤ m'.changedAt) ∧
    (m.verifiedAt = revision → m'.verifiedAt = revision)

theorem Extends.refl (revision : Nat) (memos : Memos ℭ H) : Extends revision memos memos :=
  fun _ m hm => ⟨m, hm, Or.inl ⟨rfl, rfl⟩, id⟩

theorem Extends.trans {revision : Nat} {m₁ m₂ m₃ : Memos ℭ H}
    (h₁ : Extends revision m₁ m₂) (h₂ : Extends revision m₂ m₃) :
    Extends revision m₁ m₃ := by
  intro q m hm
  have ⟨m', hm', hc', hv'⟩ := h₁ q m hm
  have ⟨m'', hm'', hc'', hv''⟩ := h₂ q m' hm'
  refine ⟨m'', hm'', ?_, fun h => hv'' (hv' h)⟩
  rcases hc' with ⟨he, hv⟩ | hr <;> rcases hc'' with ⟨he', hv'⟩ | hr'
  · exact Or.inl ⟨he'.trans he, hv'.trans hv⟩
  · exact Or.inr hr'
  · exact Or.inr (he' ▸ hr)
  · exact Or.inr hr'

theorem get?_insert_ne {M : Memos ℭ H} {q₀ p : ℭ.Q} (nm : Memo ℭ H q₀) (h : q₀ ≠ p) :
    (M.insert q₀ nm).get? p = M.get? p := by
  rw [DHashMap.get?_insert]
  exact dif_neg (by simpa using h)

theorem insert_field {q₀ : ℭ.Q} {M : Memos ℭ H} {nm : Memo ℭ H q₀}
    {P : ∀ q, Memo ℭ H q → Prop} (hnm : P q₀ nm)
    (hM : ∀ p mp, M.get? p = some mp → P p mp) :
    ∀ p mp, (M.insert q₀ nm).get? p = some mp → P p mp := by
  intro p mp hp
  by_cases hpq : q₀ = p
  · subst hpq; rw [DHashMap.get?_insert_self] at hp
    obtain rfl := Option.some.inj hp; exact hnm
  · rw [get?_insert_ne _ hpq] at hp; exact hM p mp hp

section

variable [BEq ℭ.I] [Hashable ℭ.I]

structure Inv (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ) (ι₀ : ∀ i, ℭ.V i) (revision : Nat)
    (inputRevisions : HashMap ℭ.I Nat) (hist : Nat → ∀ i, ℭ.V i)
    (memos : Memos ℭ H) : Prop where
  histNow : hist revision = ι₀
  histStable : ∀ i t, (inputRevisions.getD i 0 : Nat) ≤ t → t ≤ revision → hist t i = ι₀ i
  bounds : ∀ q m, memos.get? q = some m → m.changedAt ≤ m.verifiedAt ∧ m.verifiedAt ≤ revision
  hashOk : ∀ q m, memos.get? q = some m → m.hash = hR q m.value
  value : ∀ q m, memos.get? q = some m →
      m.value = compute tasks (hist m.verifiedAt) q
  traceIn : ∀ q m, memos.get? q = some m →
      m.inputDeps.toList =
        (FM.evalTrace_inputs (hist m.verifiedAt) (compute tasks (hist m.verifiedAt))
          (tasksTree ℭ tasks q)).map (fun p => ⟨p.i⟩)
  traceDep : ∀ q m, memos.get? q = some m →
      m.queryDeps.toList =
        (FM.evalTrace_deps (hist m.verifiedAt) (compute tasks (hist m.verifiedAt))
          (tasksTree ℭ tasks q)).map (fun p => ⟨p.q, p.hq⟩)
  cross : ∀ q m, memos.get? q = some m → ∀ dep ∈ m.queryDeps, ∃ m',
      memos.get? dep.q = some m' ∧
      (m'.changedAt ≤ m.verifiedAt → m'.value = compute tasks (hist m.verifiedAt) dep.q)

def FetchSpec (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q')) : Prop :=
  ∀ q' (hq' : ℭ.rel q' q₀) (memos : Memos ℭ H),
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos →
      Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist (fetchRec q' hq' memos).2 ∧
      Extends c.revision memos (fetchRec q' hq' memos).2 ∧
      (fetchRec q' hq' memos).1 = compute c.tasks (hist c.revision) q' ∧
      (∀ p, ¬ Relation.TransGen ℭ.rel p q' → p ≠ q' →
        (fetchRec q' hq' memos).2.get? p = memos.get? p) ∧
      ∃ m, (fetchRec q' hq' memos).2.get? q' = some m ∧
        m.verifiedAt = c.revision ∧ m.value = (fetchRec q' hq' memos).1

def DepsAtR (c : Ctx ℭ H) (q₀ : ℭ.Q) (memos : Memos ℭ H)
    (deps : Array (QueryDep ℭ q₀)) : Prop :=
  ∀ d ∈ deps, ∃ md, memos.get? d.q = some md ∧ md.verifiedAt = c.revision

theorem depsAtR_extends {c : Ctx ℭ H} {q₀ : ℭ.Q} {memos memos' : Memos ℭ H}
    {deps : Array (QueryDep ℭ q₀)} (hext : Extends c.revision memos memos')
    (h : DepsAtR c q₀ memos deps) : DepsAtR c q₀ memos' deps := by
  intro d hd
  have ⟨md, hmd, hver⟩ := h d hd
  have ⟨md', hmd', _, hver'⟩ := hext d.q md hmd
  exact ⟨md', hmd', hver' hver⟩

def CrossAt (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (V : Nat) (q' : ℭ.Q)
    (memos : Memos ℭ H) : Prop :=
  ∃ m', memos.get? q' = some m' ∧
    (m'.changedAt ≤ V → m'.value = compute c.tasks (hist V) q')

theorem crossAt_extends {c : Ctx ℭ H} {hist : Nat → ∀ i, ℭ.V i} {V : Nat} {q' : ℭ.Q}
    {memos memos' : Memos ℭ H} (hext : Extends c.revision memos memos')
    (hV : V < c.revision) (h : CrossAt c hist V q' memos) : CrossAt c hist V q' memos' := by
  have ⟨m'₀, hpre, heq⟩ := h
  have ⟨m', hpost, hdisj, _⟩ := hext q' m'₀ hpre
  refine ⟨m', hpost, fun hch => ?_⟩
  rcases hdisj with ⟨hc, hvv⟩ | hr
  · rw [hvv]; exact heq (hc ▸ hch)
  · exact absurd hch (Nat.not_le.mpr (Nat.lt_of_lt_of_le hV hr))

def traceAction (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q) :
    MonadAction (StateT (RunState ℭ H q₀) Id) (FM ℭ q₀) where
  rel {α β} P ma t := ∀ s : RunState ℭ H q₀,
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist s.memos →
    DepsAtR c q₀ s.memos s.deps →
      P (ma s).1 (FM.evalTree c.ι₀ (compute c.tasks c.ι₀) t) ∧
      Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist (ma s).2.memos ∧
      Extends c.revision s.memos (ma s).2.memos ∧
      (ma s).2.ins = s.ins ++ ((FM.evalTrace_inputs c.ι₀ (compute c.tasks c.ι₀) t).map
          (fun p => (⟨p.i⟩ : InputDep ℭ.I))).toArray ∧
      (ma s).2.deps = s.deps ++ ((FM.evalTrace_deps c.ι₀ (compute c.tasks c.ι₀) t).map
          (fun p => (⟨p.q, p.hq⟩ : QueryDep ℭ q₀))).toArray ∧
      DepsAtR c q₀ (ma s).2.memos (ma s).2.deps ∧
      (∀ p, ¬ Relation.TransGen ℭ.rel p q₀ → (ma s).2.memos.get? p = s.memos.get? p)
  rel_pure {α β R a b} hab s hinv hdeps := by
    refine ⟨hab, hinv, Extends.refl _ _, ?_, ?_, hdeps, fun _ _ => rfl⟩
    · show s.ins = s.ins ++ _
      simp [FM.evalTrace_inputs]
    · show s.deps = s.deps ++ _
      simp [FM.evalTrace_deps]
  rel_bind {α₁ α₂ β₁ β₂ R S ma mb ka kb} hma hk s hinv hdeps := by
    have ⟨hR, hinv', hext', hin', hdep', hda', hfp'⟩ := hma s hinv hdeps
    have ⟨hS, hinv'', hext'', hin'', hdep'', hda'', hfp''⟩ := hk _ _ hR (ma s).2 hinv' hda'
    have hstep : (ma >>= ka) s = ka (ma s).1 (ma s).2 := rfl
    refine ⟨FM.evalTree_bind .. ▸ hS, hinv'', Extends.trans hext' hext'', ?_, ?_,
      hstep ▸ hda'', fun p hp => ?_⟩
    · rw [hstep, hin'', hin']
      change _ = s.ins ++ ((FM.evalTrace_inputs c.ι₀ (compute c.tasks c.ι₀)
        (FM.bind mb kb)).map _).toArray
      simp only [FM.evalTrace_inputs_bind, List.map_append, List.append_toArray,
        Array.append_assoc]
    · rw [hstep, hdep'', hdep']
      change _ = s.deps ++ ((FM.evalTrace_deps c.ι₀ (compute c.tasks c.ι₀)
        (FM.bind mb kb)).map _).toArray
      simp only [FM.evalTrace_deps_bind, List.map_append, List.append_toArray,
        Array.append_assoc]
    · rw [hstep]; exact (hfp'' p hp).trans (hfp' p hp)

theorem runInput_rel (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q) (i : ℭ.I) :
    (traceAction c hist q₀).rel Eq (runInput c q₀ i) (FM.pureInput i) := by
  intro s hinv hdeps
  refine ⟨rfl, hinv, Extends.refl _ _, ?_, ?_, hdeps, fun _ _ => rfl⟩
  · show s.ins.push _ = s.ins ++ _
    simp [FM.evalTrace_inputs]
  · show s.deps = s.deps ++ _
    simp [FM.evalTrace_deps]

theorem runFetch_rel (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (hfr : FetchSpec c hist q₀ fetchRec) (q' : ℭ.Q) (hq' : ℭ.rel q' q₀) :
    (traceAction c hist q₀).rel Eq (runFetch q₀ fetchRec q' hq') (FM.pureFetch q' hq') := by
  intro s hinv hdeps
  have ⟨hinv', hext, hval, hfp, m', hm', hver', hmval'⟩ := hfr q' hq' s.memos hinv
  have hval' : (fetchRec q' hq' s.memos).1 = compute c.tasks c.ι₀ q' := by
    rw [hval, hinv.histNow]
  refine ⟨?_, hinv', hext, ?_, ?_, ?_, ?_⟩
  · exact hval'
  · show s.ins = s.ins ++ _
    simp [FM.evalTrace_inputs]
  · show s.deps.push _ = s.deps ++ _
    simp [FM.evalTrace_deps]
  · show DepsAtR c q₀ (fetchRec q' hq' s.memos).2 (s.deps.push ⟨q', hq'⟩)
    intro d hd
    rcases Array.mem_push.mp hd with hd | rfl
    · exact depsAtR_extends hext hdeps d hd
    · exact ⟨m', hm', hver'⟩
  · intro p hp
    exact hfp p (fun ht => hp (ht.tail hq')) (fun he => hp (he ▸ Relation.TransGen.single hq'))

theorem reExec_spec (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (hfr : FetchSpec c hist q₀ fetchRec) (memos : Memos ℭ H)
    (hinv : Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos) :
    (reExec c q₀ fetchRec memos).1.1 = compute c.tasks c.ι₀ q₀ ∧
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist (reExec c q₀ fetchRec memos).2 ∧
    Extends c.revision memos (reExec c q₀ fetchRec memos).2 ∧
    (reExec c q₀ fetchRec memos).1.2.1.toList =
      (FM.evalTrace_inputs c.ι₀ (compute c.tasks c.ι₀) (tasksTree ℭ c.tasks q₀)).map
        (fun p => ⟨p.i⟩) ∧
    (reExec c q₀ fetchRec memos).1.2.2.toList =
      (FM.evalTrace_deps c.ι₀ (compute c.tasks c.ι₀) (tasksTree ℭ c.tasks q₀)).map
        (fun p => ⟨p.q, p.hq⟩) ∧
    DepsAtR c q₀ (reExec c q₀ fetchRec memos).2 (reExec c q₀ fetchRec memos).1.2.2 ∧
    (∀ p, ¬ Relation.TransGen ℭ.rel p q₀ →
      (reExec c q₀ fetchRec memos).2.get? p = memos.get? p) := by
  have hrel := (c.tasks q₀).param (traceAction c hist q₀)
    (runFetch q₀ fetchRec) FM.pureFetch
    (runInput_rel c hist q₀) (runFetch_rel c hist q₀ fetchRec hfr)
  have ⟨hval, hinv', hext, hin, hdep, hda, hfp⟩ := hrel ⟨#[], #[], memos⟩ hinv nofun
  refine ⟨hval.trans (tasksTree_eval_compute ℭ c.tasks q₀ c.ι₀), hinv', hext, ?_, ?_, hda, hfp⟩
  · show ((c.tasks q₀).fn (StateT (RunState ℭ H q₀) Id) (runInput c q₀)
        (runFetch q₀ fetchRec) ⟨#[], #[], memos⟩).2.ins.toList = _
    rw [hin]; simp [tasksTree]
  · show ((c.tasks q₀).fn (StateT (RunState ℭ H q₀) Id) (runInput c q₀)
        (runFetch q₀ fetchRec) ⟨#[], #[], memos⟩).2.deps.toList = _
    rw [hdep]; simp [tasksTree]

theorem verifyDeps_footprint (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (hfr : FetchSpec c hist q₀ fetchRec) (V : Nat) :
    ∀ (l : List (QueryDep ℭ q₀)) (memos : Memos ℭ H),
      Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos →
      ∀ p, (∀ dep ∈ l, ¬ Relation.TransGen ℭ.rel p dep.q ∧ p ≠ dep.q) →
        (verifyDeps c q₀ V fetchRec l memos).2.get? p = memos.get? p := by
  intro l
  induction l with
  | nil => intro memos _ p _; rfl
  | cons dep rest ih =>
    have ⟨q', hq'⟩ := dep
    intro memos hinv p hp
    have ⟨hinv1, _, _, hfp1, m', hm', _, _⟩ := hfr q' hq' memos hinv
    have hs1 : (fetchRec q' hq' memos).2.get? p = memos.get? p :=
      hfp1 p (hp ⟨q', hq'⟩ List.mem_cons_self).1 (hp ⟨q', hq'⟩ List.mem_cons_self).2
    have e1 : verifyDeps c q₀ V fetchRec (⟨q', hq'⟩ :: rest) memos =
        (match (fetchRec q' hq' memos).2.get? q' with
         | some m'' => if m''.verifiedAt == c.revision ∧ m''.changedAt ≤ V then
             verifyDeps c q₀ V fetchRec rest (fetchRec q' hq' memos).2
           else (false, (fetchRec q' hq' memos).2)
         | none => (false, (fetchRec q' hq' memos).2)) := rfl
    rw [e1]; simp only [hm']
    by_cases hcheck : m'.verifiedAt == c.revision ∧ m'.changedAt ≤ V
    · rw [if_pos hcheck,
        ih (fetchRec q' hq' memos).2 hinv1 p (fun dep hd => hp dep (List.mem_cons_of_mem _ hd))]
      exact hs1
    · rw [if_neg hcheck]; exact hs1

theorem verifyDeps_spec (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (hfr : FetchSpec c hist q₀ fetchRec) (V : Nat) (hV : V < c.revision) :
    ∀ (l : List (QueryDep ℭ q₀)) (memos : Memos ℭ H),
      Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos →
      (∀ dep ∈ l, CrossAt c hist V dep.q memos) →
      Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist
          (verifyDeps c q₀ V fetchRec l memos).2 ∧
      Extends c.revision memos (verifyDeps c q₀ V fetchRec l memos).2 ∧
      ((verifyDeps c q₀ V fetchRec l memos).1 = true →
        (∀ dep ∈ l, compute c.tasks (hist V) dep.q = compute c.tasks (hist c.revision) dep.q) ∧
        (∀ dep ∈ l, ∃ m', (verifyDeps c q₀ V fetchRec l memos).2.get? dep.q = some m' ∧
          m'.verifiedAt = c.revision)) := by
  intro l
  induction l with
  | nil =>
    intro memos hinv _
    exact ⟨hinv, Extends.refl _ _, fun _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩⟩
  | cons dep rest ih =>
    have ⟨q', hq'⟩ := dep
    intro memos hinv hcross
    have ⟨hinv1, hext1, hval1, _, m', hm', hver', hmval'⟩ := hfr q' hq' memos hinv
    have e1 : verifyDeps c q₀ V fetchRec (⟨q', hq'⟩ :: rest) memos =
        (match (fetchRec q' hq' memos).2.get? q' with
         | some m'' => if m''.verifiedAt == c.revision ∧ m''.changedAt ≤ V then
             verifyDeps c q₀ V fetchRec rest (fetchRec q' hq' memos).2
           else (false, (fetchRec q' hq' memos).2)
         | none => (false, (fetchRec q' hq' memos).2)) := rfl
    rw [e1]; simp only [hm']
    by_cases hcheck : m'.verifiedAt == c.revision ∧ m'.changedAt ≤ V
    · rw [if_pos hcheck]
      have hcrossRest : ∀ dep ∈ rest, CrossAt c hist V dep.q (fetchRec q' hq' memos).2 :=
        fun dep hd => crossAt_extends hext1 hV (hcross dep (List.mem_cons_of_mem _ hd))
      have ⟨hinvR, hextR, htrueR⟩ := ih (fetchRec q' hq' memos).2 hinv1 hcrossRest
      have htransHead : compute c.tasks (hist V) q' = compute c.tasks (hist c.revision) q' := by
        have ⟨m'', hm'', heqm''⟩ := crossAt_extends hext1 hV (hcross ⟨q', hq'⟩ List.mem_cons_self)
        rw [hm'] at hm''; obtain rfl := Option.some.inj hm''
        rw [← heqm'' hcheck.2, hmval', hval1]
      refine ⟨hinvR, Extends.trans hext1 hextR, fun htrue => ⟨?_, ?_⟩⟩
      · intro dep hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact htransHead
        · exact (htrueR htrue).1 dep hd
      · intro dep hd
        rcases List.mem_cons.mp hd with rfl | hd
        · have ⟨mf, hmf, _, hverf⟩ := hextR q' m' hm'
          exact ⟨mf, hmf, hverf (by simpa using hcheck.1)⟩
        · exact (htrueR htrue).2 dep hd
    · rw [if_neg hcheck]
      exact ⟨hinv1, hext1, fun htrue => absurd htrue (by simp)⟩

theorem initInv (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ) (ι₀ : ∀ i, ℭ.V i) :
    Inv hR tasks ι₀ 0 (HashMap.emptyWithCapacity 1024)
      (Erased.mk (fun _ => ι₀)).out
      (DHashMap.emptyWithCapacity 4096 : Memos ℭ H) where
  histNow := by simp only [Erased.out_mk]
  histStable i t _ _ := by simp only [Erased.out_mk]
  bounds q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm
  hashOk q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm
  value q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm
  traceIn q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm
  traceDep q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm
  cross q m hm := by simp [Std.DHashMap.get?_emptyWithCapacity] at hm

variable [LawfulBEq ℭ.I] in
theorem setInv (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ) (ι₀ ι₀' : ∀ i, ℭ.V i) (revision : Nat)
    (inputRevisions : HashMap ℭ.I Nat) (hist : Nat → ∀ i, ℭ.V i)
    (memos : Memos ℭ H) (i : ℭ.I) (hne : ∀ i', i' ≠ i → ι₀' i' = ι₀ i')
    (h : Inv hR tasks ι₀ revision inputRevisions hist memos) :
    Inv hR tasks ι₀' (revision + 1)
      (inputRevisions.insert i (revision + 1))
      (fun t => if t ≤ revision then hist t else ι₀')
      memos := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [if_neg (by omega)]
  · intro i' t h1 h2
    by_cases hi : i' = i
    · subst hi
      rw [HashMap.getD_insert_self] at h1
      rw [if_neg (by omega)]
    · rw [HashMap.getD_insert] at h1
      split_ifs at h1 with hbeq
      · exact absurd (LawfulBEq.eq_of_beq hbeq).symm hi
      · by_cases ht : t ≤ revision
        · rw [if_pos ht, h.histStable i' t h1 (by omega), hne i' hi]
        · rw [if_neg ht]
  · intro q m hm; exact ⟨(h.bounds q m hm).1, Nat.le_succ_of_le (h.bounds q m hm).2⟩
  · intro q m hm; exact h.hashOk q m hm
  · intro q m hm
    rw [if_pos (h.bounds q m hm).2]; exact h.value q m hm
  · intro q m hm
    rw [if_pos (h.bounds q m hm).2]; exact h.traceIn q m hm
  · intro q m hm
    rw [if_pos (h.bounds q m hm).2]; exact h.traceDep q m hm
  · intro q m hm dep hdep
    rw [if_pos (h.bounds q m hm).2]; exact h.cross q m hm dep hdep

section

variable [DecidableEq H]

theorem insertReExec_spec (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) (q₀ : ℭ.Q)
    (fetchRec : ∀ q', ℭ.rel q' q₀ → StateM (Memos ℭ H) (ℭ.R q'))
    (hfr : FetchSpec c hist q₀ fetchRec) (memos : Memos ℭ H)
    (hinv : Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos) :
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist
        (insertReExec c q₀ fetchRec memos).2 ∧
    Extends c.revision memos (insertReExec c q₀ fetchRec memos).2 ∧
    (insertReExec c q₀ fetchRec memos).1 = compute c.tasks (hist c.revision) q₀ ∧
    (∀ p, ¬ Relation.TransGen ℭ.rel p q₀ → p ≠ q₀ →
      (insertReExec c q₀ fetchRec memos).2.get? p = memos.get? p) ∧
    ∃ m, (insertReExec c q₀ fetchRec memos).2.get? q₀ = some m ∧
      m.verifiedAt = c.revision ∧ m.value = (insertReExec c q₀ fetchRec memos).1 := by
  have ⟨hv, hinvM, hextM, hinT, hdepT, hda, hfpM⟩ :=
    reExec_spec c hist q₀ fetchRec hfr memos hinv
  let M := (reExec c q₀ fetchRec memos).2
  let ca : Nat := match M.get? q₀ with
    | some m => if c.hR q₀ (reExec c q₀ fetchRec memos).1.1 == m.hash then m.changedAt
        else c.revision
    | none => c.revision
  let nm : Memo ℭ H q₀ :=
    { value := (reExec c q₀ fetchRec memos).1.1
      hash := c.hR q₀ (reExec c q₀ fetchRec memos).1.1
      changedAt := ca, verifiedAt := c.revision,
      inputDeps := (reExec c q₀ fetchRec memos).1.2.1,
      queryDeps := (reExec c q₀ fetchRec memos).1.2.2 }
  have hstate : (insertReExec c q₀ fetchRec memos).2 = M.insert q₀ nm := rfl
  have hcae : ca = (match M.get? q₀ with
    | some m => if c.hR q₀ (reExec c q₀ fetchRec memos).1.1 == m.hash then m.changedAt
        else c.revision
    | none => c.revision) := rfl
  have hnmval : nm.value = compute c.tasks (hist c.revision) q₀ := by
    show (reExec c q₀ fetchRec memos).1.1 = _
    rw [hv, hinv.histNow]
  have hcaR : ca ≤ c.revision := by
    rw [hcae]
    split
    next m hm =>
      have hb := hinvM.bounds q₀ m hm
      split
      · exact Nat.le_trans hb.1 hb.2
      · exact Nat.le_refl _
    next => exact Nat.le_refl _
  refine ⟨⟨hinvM.histNow, hinvM.histStable,
      insert_field ⟨hcaR, Nat.le_refl _⟩ hinvM.bounds, insert_field rfl hinvM.hashOk,
      insert_field hnmval hinvM.value, insert_field ?_ hinvM.traceIn,
      insert_field ?_ hinvM.traceDep, ?_⟩, ?_, hnmval,
    ?_, nm, by rw [hstate]; exact DHashMap.get?_insert_self, rfl, rfl⟩
  · rw [← hinv.histNow] at hinT; exact hinT
  · rw [← hinv.histNow] at hdepT; exact hdepT
  · intro p mp hp dep hdep
    by_cases hpq : q₀ = p
    · subst hpq; rw [hstate, DHashMap.get?_insert_self] at hp
      obtain rfl := Option.some.inj hp
      have ⟨md, hmd, hmdR⟩ := hda dep hdep
      refine ⟨md, ?_, fun _ => ?_⟩
      · rw [hstate, get?_insert_ne _ (rel_ne dep.rel).symm]; exact hmd
      · rw [hinvM.value dep.q md hmd, hmdR]
    · rw [hstate, get?_insert_ne _ hpq] at hp
      have hcross := hinvM.cross p mp hp dep hdep
      by_cases hdq : q₀ = dep.q
      · rw [← hdq] at hcross ⊢
        have ⟨m0, hm0, hm0eq⟩ := hcross
        refine ⟨nm, by rw [hstate]; exact DHashMap.get?_insert_self, fun hguard => ?_⟩
        have hguard' : (if c.hR q₀ (reExec c q₀ fetchRec memos).1.1 == m0.hash
            then m0.changedAt else c.revision) ≤ mp.verifiedAt := by
          have hg : ca ≤ mp.verifiedAt := hguard
          rwa [hcae, hm0] at hg
        show (reExec c q₀ fetchRec memos).1.1 = _
        split_ifs at hguard' with hbd
        · have hveq : (reExec c q₀ fetchRec memos).1.1 = m0.value :=
            (c.hR q₀).injective ((eq_of_beq hbd).trans (hinvM.hashOk q₀ m0 hm0))
          rw [hveq]; exact hm0eq hguard'
        · have hpr : mp.verifiedAt = c.revision :=
            Nat.le_antisymm (hinvM.bounds p mp hp).2 hguard'
          rw [hv, hpr, hinv.histNow]
      · have ⟨m0, hm0, hm0eq⟩ := hcross
        exact ⟨m0, by rw [hstate, get?_insert_ne _ hdq]; exact hm0, hm0eq⟩
  · refine Extends.trans hextM (fun p mp hp => ?_)
    by_cases hpq : q₀ = p
    · subst hpq
      refine ⟨nm, by rw [hstate]; exact DHashMap.get?_insert_self, ?_, fun _ => rfl⟩
      have hcaeq : ca = if c.hR q₀ (reExec c q₀ fetchRec memos).1.1 == mp.hash
          then mp.changedAt else c.revision := by rw [hcae, hp]
      by_cases hbd : c.hR q₀ (reExec c q₀ fetchRec memos).1.1 == mp.hash
      · refine Or.inl ⟨?_, ?_⟩
        · show ca = mp.changedAt; rw [hcaeq, if_pos hbd]
        · show (reExec c q₀ fetchRec memos).1.1 = mp.value
          exact (c.hR q₀).injective ((eq_of_beq hbd).trans (hinvM.hashOk q₀ mp hp))
      · refine Or.inr ?_
        have hcarev : ca = c.revision := by rw [hcaeq, if_neg hbd]
        exact Nat.le_of_eq hcarev.symm
    · exact ⟨mp, by rw [hstate, get?_insert_ne _ hpq]; exact hp, Or.inl ⟨rfl, rfl⟩, id⟩
  · intro p hpt hpne
    rw [hstate, get?_insert_ne _ (Ne.symm hpne)]
    exact hfpM p hpt

theorem fetch_spec (c : Ctx ℭ H) (hist : Nat → ∀ i, ℭ.V i) :
    ∀ (q₀ : ℭ.Q) (memos : Memos ℭ H),
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist memos →
    Inv c.hR c.tasks c.ι₀ c.revision c.inputRevisions hist (fetch c q₀ memos).2 ∧
    Extends c.revision memos (fetch c q₀ memos).2 ∧
    (fetch c q₀ memos).1 = compute c.tasks (hist c.revision) q₀ ∧
    (∀ p, ¬ Relation.TransGen ℭ.rel p q₀ → p ≠ q₀ →
      (fetch c q₀ memos).2.get? p = memos.get? p) ∧
    ∃ m, (fetch c q₀ memos).2.get? q₀ = some m ∧
      m.verifiedAt = c.revision ∧ m.value = (fetch c q₀ memos).1 := by
  intro q₀
  induction q₀ using ℭ.wf.induction with
  | _ q₀ IH =>
    intro memos h
    have hfr : FetchSpec c hist q₀ (fun q' _hq => fetch c q') :=
      fun q' hq' m hm => IH q' hq' m hm
    rw [fetch]
    split
    next m hget =>
      by_cases hvereq : m.verifiedAt == c.revision
      · rw [if_pos hvereq]
        have hmv : m.verifiedAt = c.revision := by simpa using hvereq
        refine ⟨h, Extends.refl _ _, ?_, fun _ _ _ => rfl, m, hget, hmv, rfl⟩
        rw [h.value q₀ m hget, hmv]
      · rw [if_neg hvereq]
        have hfoot : ∀ p, ¬ Relation.TransGen ℭ.rel p q₀ →
            ∀ dep ∈ m.queryDeps.toList, ¬ Relation.TransGen ℭ.rel p dep.q ∧ p ≠ dep.q :=
          fun p hpt dep _ => ⟨fun ht => hpt (ht.tail dep.rel),
            fun he => hpt (he ▸ Relation.TransGen.single dep.rel)⟩
        by_cases hclean : inputsClean c m.verifiedAt m.inputDeps
        · rw [if_pos hclean]
          have hVlt : m.verifiedAt < c.revision :=
            Nat.lt_of_le_of_ne (h.bounds q₀ m hget).2 (by simpa using hvereq)
          have hcrossDeps : ∀ dep ∈ m.queryDeps.toList,
              CrossAt c hist m.verifiedAt dep.q memos :=
            fun dep hd => h.cross q₀ m hget dep (by simpa using hd)
          have ⟨hinvS, hextS, htrueS⟩ := verifyDeps_spec c hist q₀ (fun q' _hq => fetch c q')
            hfr m.verifiedAt hVlt m.queryDeps.toList memos h hcrossDeps
          have hfootS := verifyDeps_footprint c hist q₀ (fun q' _hq => fetch c q')
            hfr m.verifiedAt m.queryDeps.toList memos h
          have hq0S : (verifyDeps c q₀ m.verifiedAt (fun q' _hq => fetch c q')
              m.queryDeps.toList memos).2.get? q₀ = some m :=
            (hfootS q₀ (hfoot q₀ (transGen_irrefl q₀))).trans hget
          by_cases hok : (verifyDeps c q₀ m.verifiedAt (fun q' _hq => fetch c q')
              m.queryDeps.toList memos).1 = true
          · rw [if_pos hok]
            have ⟨htrans, hdepsR⟩ := htrueS hok
            have hInAgree : ∀ p ∈ FM.evalTrace_inputs (hist m.verifiedAt)
                (compute c.tasks (hist m.verifiedAt)) (tasksTree ℭ c.tasks q₀),
                (hist c.revision) p.i = p.v := by
              intro p hp
              have hkey : (⟨p.i⟩ : InputDep ℭ.I) ∈ m.inputDeps := by
                rw [← Array.mem_toList_iff, h.traceIn q₀ m hget]; exact List.mem_map_of_mem hp
              have hir : c.inputRevisions.getD p.i 0 ≤ m.verifiedAt := by
                have hc := hclean; rw [inputsClean, Array.all_eq_true'] at hc
                simpa using hc _ hkey
              rw [evalTrace_inputs_value _ _ _ p hp,
                h.histStable p.i m.verifiedAt hir (h.bounds q₀ m hget).2, ← h.histNow]
            have hDepAgree : ∀ p ∈ FM.evalTrace_deps (hist m.verifiedAt)
                (compute c.tasks (hist m.verifiedAt)) (tasksTree ℭ c.tasks q₀),
                compute c.tasks (hist c.revision) p.q = p.r := by
              intro p hp
              have hdq : (⟨p.q, p.hq⟩ : QueryDep ℭ q₀) ∈ m.queryDeps.toList := by
                rw [h.traceDep q₀ m hget]; exact List.mem_map_of_mem hp
              rw [FM.evalTrace_deps_value _ _ _ p hp, ← htrans ⟨p.q, p.hq⟩ hdq]
            have hmVal : m.value = compute c.tasks (hist c.revision) q₀ := by
              rw [h.value q₀ m hget]
              exact compute_cross ℭ c.tasks q₀ (hist m.verifiedAt) (hist c.revision)
                hInAgree hDepAgree
            have hbnd := h.bounds q₀ m hget
            refine ⟨⟨h.histNow, h.histStable,
                insert_field ⟨Nat.le_trans hbnd.1 hbnd.2, Nat.le_refl _⟩ hinvS.bounds,
                insert_field (h.hashOk q₀ m hget) hinvS.hashOk,
                insert_field hmVal hinvS.value, insert_field ?_ hinvS.traceIn,
                insert_field ?_ hinvS.traceDep, ?_⟩,
              ?_, hmVal, ?_, { m with verifiedAt := c.revision },
              by rw [DHashMap.get?_insert_self], rfl, rfl⟩
            · have h2 := h.traceIn q₀ m hget
              rw [evalTrace_inputs_cross (hist m.verifiedAt) (hist c.revision)
                (compute c.tasks (hist m.verifiedAt)) (compute c.tasks (hist c.revision))
                _ hInAgree hDepAgree] at h2
              exact h2
            · have h2 := h.traceDep q₀ m hget
              rw [evalTrace_deps_cross (hist m.verifiedAt) (hist c.revision)
                (compute c.tasks (hist m.verifiedAt)) (compute c.tasks (hist c.revision))
                _ hInAgree hDepAgree] at h2
              exact h2
            · intro p mp hp dep hdep
              by_cases hpq : q₀ = p
              · subst hpq; rw [DHashMap.get?_insert_self] at hp
                obtain rfl := Option.some.inj hp
                have ⟨md, hmd, hmdR⟩ := hdepsR dep (by simpa using hdep)
                refine ⟨md, ?_, fun _ => ?_⟩
                · rw [get?_insert_ne _ (rel_ne dep.rel).symm]; exact hmd
                · rw [hinvS.value dep.q md hmd, hmdR]
              · rw [get?_insert_ne _ hpq] at hp
                have hcross := hinvS.cross p mp hp dep hdep
                by_cases hdq : q₀ = dep.q
                · rw [← hdq] at hcross ⊢
                  have ⟨m0, hm0, hm0eq⟩ := hcross
                  rw [hq0S] at hm0; obtain rfl := Option.some.inj hm0
                  exact ⟨{ m with verifiedAt := c.revision },
                    by rw [DHashMap.get?_insert_self], fun hguard => hm0eq hguard⟩
                · have ⟨m0, hm0, hm0eq⟩ := hcross
                  exact ⟨m0, by rw [get?_insert_ne _ hdq]; exact hm0, hm0eq⟩
            · refine Extends.trans hextS (fun p mp hp => ?_)
              by_cases hpq : q₀ = p
              · subst hpq
                rw [hq0S] at hp; obtain rfl := Option.some.inj hp
                exact ⟨{ m with verifiedAt := c.revision }, by rw [DHashMap.get?_insert_self],
                  Or.inl ⟨rfl, rfl⟩, fun _ => rfl⟩
              · exact ⟨mp, by rw [get?_insert_ne _ hpq]; exact hp, Or.inl ⟨rfl, rfl⟩, id⟩
            · intro p hpt hpne
              rw [get?_insert_ne _ (Ne.symm hpne)]
              exact hfootS p (hfoot p hpt)
          · rw [if_neg hok]
            have ⟨hi, he, hv, hfp, hm⟩ := insertReExec_spec c hist q₀ (fun q' _hq => fetch c q')
              hfr _ hinvS
            exact ⟨hi, Extends.trans hextS he, hv,
              fun p hpt hpne => (hfp p hpt hpne).trans (hfootS p (hfoot p hpt)), hm⟩
        · rw [if_neg hclean]
          exact insertReExec_spec c hist q₀ (fun q' _hq => fetch c q') hfr memos h
    · exact insertReExec_spec c hist q₀ (fun q' _hq => fetch c q') hfr memos h

end

end

end

end Salsa

public def Salsa
    (ℭ : BuildConfig) (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ) :
    Build ℭ J tasks Id Id where
  σ := { s : Salsa.Store ℭ H J //
    Salsa.Inv hR tasks (Input.get s.inputs) s.revision s.inputRevisions s.history.out s.memos }
  init j := ⟨{ inputs := j, revision := 0
               memos := DHashMap.emptyWithCapacity 4096
               inputRevisions := HashMap.emptyWithCapacity 1024
               history := Erased.mk (fun _ => Input.get j) },
             Salsa.initInv hR tasks (Input.get j)⟩
  inputs s := Input.get s.val.inputs
  set i v := fun s =>
    ((), ⟨{ inputs := Input.set s.val.inputs i v
            revision := s.val.revision + 1
            memos := s.val.memos
            inputRevisions := s.val.inputRevisions.insert i (s.val.revision + 1)
            history := s.val.history.map fun hh t =>
              if t ≤ s.val.revision then hh t
              else Input.get (Input.set s.val.inputs i v) },
          by
            rw [Erased.map_out]
            exact Salsa.setInv hR tasks (Input.get s.val.inputs)
              (Input.get (Input.set s.val.inputs i v)) s.val.revision
              s.val.inputRevisions s.val.history.out s.val.memos i
              (fun i' hi' => Input.get_set_other _ _ _ _ hi') s.property⟩)
  build q s :=
    let c : Salsa.Ctx ℭ H :=
      ⟨hR, tasks, Input.get s.val.inputs, s.val.revision, s.val.inputRevisions⟩
    let r := Salsa.fetch c q s.val.memos
    have hspec := Salsa.fetch_spec c s.val.history.out q s.val.memos s.property
    (⟨r.1, by rw [hspec.2.2.1, (s.property).histNow]⟩,
     ⟨{ s.val with memos := r.2 }, hspec.1⟩)

end Incremental
