module

public import Incremental.Shake.Basic
public import Incremental.Shake.Standard
public import Mathlib.Data.List.Perm.Subperm

namespace Incremental

open Std (DHashMap)

namespace ShakeStandardRdeps

section

variable {α : Type _}

private theorem push_toList_inUniv
    {visited : Array α} {univ : List α} {k : α}
    (hVisInUniv : ∀ x ∈ visited.toList, x ∈ univ) (hkInUniv : k ∈ univ) :
    ∀ x ∈ (visited.push k).toList, x ∈ univ := by
  intro x hx
  rw [Array.toList_push] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hVisInUniv x hx
  · cases List.mem_singleton.mp hx
    exact hkInUniv

private theorem push_toList_nodup
    {visited : Array α} {k : α}
    (hVisNodup : visited.toList.Nodup) (hkNotInVis : k ∉ visited) :
    (visited.push k).toList.Nodup := by
  rw [Array.toList_push]
  refine List.nodup_append.mpr ⟨hVisNodup, List.nodup_cons.mpr ⟨nofun, List.nodup_nil⟩, ?_⟩
  intro a ha b hb hab
  have : b = k := List.mem_singleton.mp hb
  subst this
  subst hab
  exact hkNotInVis (Array.mem_def.mpr ha)

private theorem visited_size_lt
    {visited : Array α} {univ : List α} {bound : Nat}
    (hBound : univ.length + 1 ≤ bound)
    (hVisInUniv : ∀ x ∈ visited.toList, x ∈ univ)
    (hVisNodup : visited.toList.Nodup) : visited.size < bound := by
  have hLenLe : visited.toList.length ≤ univ.length :=
    (hVisNodup.subperm hVisInUniv).length_le
  rw [← Array.length_toList]
  omega

end

section

variable {ℭ : BuildConfig} [BEq ℭ.Q]

def closureGo (rdeps : Array (ℭ.Q × ℭ.Q)) (bound : Nat) (worklist : List ℭ.Q)
    (visited : Array ℭ.Q) (hv : visited.size ≤ bound) : Array ℭ.Q :=
  match worklist with
  | [] => visited
  | k :: rest =>
    if visited.toList.contains k then
      closureGo rdeps bound rest visited hv
    else
      if h : visited.size < bound then
        let new := rdeps.foldl (init := []) fun acc (p, c) =>
          if p == k then c :: acc else acc
        let visited' := visited.push k
        have hv' : visited'.size ≤ bound := by
          rw [Array.size_push]
          omega
        closureGo rdeps bound (new ++ rest) visited' hv'
      else visited
termination_by (bound - visited.size, worklist.length)
decreasing_by
  · simp
    omega
  · simp
    omega

def closure (rdeps : Array (ℭ.Q × ℭ.Q)) (seed : Array ℭ.Q) : Array ℭ.Q :=
  closureGo rdeps (seed.size + rdeps.size + 1) seed.toList #[] (Nat.zero_le _)

theorem closureGo_visited_subset
    (rdeps : Array (ℭ.Q × ℭ.Q)) (bound : Nat)
    (worklist : List ℭ.Q) (visited : Array ℭ.Q) (hv : visited.size ≤ bound)
    (q : ℭ.Q) (hq : q ∈ visited) :
    q ∈ closureGo rdeps bound worklist visited hv := by
  match worklist with
  | [] =>
    unfold closureGo
    exact hq
  | k :: rest =>
    unfold closureGo
    split
    · exact closureGo_visited_subset rdeps bound rest visited hv q hq
    · next hnotc =>
      split
      next hsize =>
        apply closureGo_visited_subset rdeps bound _ _ _ q
        exact Array.mem_push.mpr (Or.inl hq)
      next hnsize => exact hq
termination_by (bound - visited.size, worklist.length)
decreasing_by
  · simp_wf
    refine Prod.lex_def.mpr (Or.inl ?_)
    omega
  · simp_wf
    refine Prod.lex_def.mpr (Or.inr ⟨rfl, ?_⟩)
    omega

private theorem rdeps_foldl_new_in_univ
    (rdeps : Array (ℭ.Q × ℭ.Q)) (univ : List ℭ.Q) (k : ℭ.Q)
    (hRdepsInUniv : ∀ p ∈ rdeps, p.snd ∈ univ) (acc : List ℭ.Q)
    (hAcc : ∀ x ∈ acc, x ∈ univ) :
    ∀ x ∈ rdeps.foldl (init := acc) (fun acc p => if p.fst == k then p.snd :: acc else acc),
      x ∈ univ :=
  Array.foldl_induction
    (motive := fun _ l => ∀ x ∈ l, x ∈ univ)
    hAcc
    (fun i acc' ih => by
      dsimp only
      split
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hRdepsInUniv _ (Array.mem_of_getElem rfl)
        · exact ih x hx
      · exact ih)

end

section

variable {ℭ : BuildConfig} [BEq ℭ.Q] [LawfulBEq ℭ.Q]

private theorem visited_of_contains
    {visited : Array ℭ.Q} {k : ℭ.Q}
    (hc : visited.toList.contains k = true) : k ∈ visited :=
  Array.mem_def.mpr (List.mem_of_elem_eq_true hc)

private theorem not_visited_of_not_contains
    {visited : Array ℭ.Q} {k : ℭ.Q}
    (hnotc : ¬(visited.toList.contains k = true)) : k ∉ visited := fun h =>
  hnotc (List.contains_iff_mem.mpr (Array.mem_def.mp h))

theorem closureGo_worklist_subset
    (rdeps : Array (ℭ.Q × ℭ.Q)) (univ : List ℭ.Q)
    (bound : Nat) (hBound : univ.length + 1 ≤ bound)
    (hRdepsInUniv : ∀ p ∈ rdeps, p.snd ∈ univ)
    (worklist : List ℭ.Q) (visited : Array ℭ.Q) (hv : visited.size ≤ bound)
    (hWorkInUniv : ∀ x ∈ worklist, x ∈ univ)
    (hVisInUniv : ∀ x ∈ visited.toList, x ∈ univ)
    (hVisNodup : visited.toList.Nodup)
    (q : ℭ.Q) (hq : q ∈ worklist) :
    q ∈ closureGo rdeps bound worklist visited hv :=
  match worklist with
  | [] => absurd hq List.not_mem_nil
  | k :: rest => by
    unfold closureGo
    split
    next hcontains =>
      have hkInVis : k ∈ visited := visited_of_contains hcontains
      rcases List.mem_cons.mp hq with rfl | hqRest
      · exact closureGo_visited_subset rdeps bound rest visited hv q hkInVis
      · exact closureGo_worklist_subset rdeps univ bound hBound hRdepsInUniv rest visited hv
          (fun x hx => hWorkInUniv x (List.mem_cons_of_mem _ hx))
          hVisInUniv hVisNodup q hqRest
    next hnotc =>
      have hkNotInVis : k ∉ visited := not_visited_of_not_contains hnotc
      have hkInUniv : k ∈ univ := hWorkInUniv k List.mem_cons_self
      split
      next hsize =>
        have hv' : (visited.push k).size ≤ bound := by
          rw [Array.size_push]
          omega
        have hVisInUniv' := push_toList_inUniv hVisInUniv hkInUniv
        have hVisNodup' := push_toList_nodup hVisNodup hkNotInVis
        have hNewInUniv := rdeps_foldl_new_in_univ rdeps univ k hRdepsInUniv []
          (fun _ h => absurd h List.not_mem_nil)
        rcases List.mem_cons.mp hq with rfl | hqRest
        · apply closureGo_visited_subset rdeps bound _ _ hv' q
          show q ∈ visited.push q
          exact Array.mem_push_self
        · apply closureGo_worklist_subset rdeps univ bound hBound hRdepsInUniv _ _ hv'
          · intro x hx
            rcases List.mem_append.mp hx with hxNew | hxRest
            · exact hNewInUniv x hxNew
            · exact hWorkInUniv x (List.mem_cons_of_mem _ hxRest)
          · exact hVisInUniv'
          · exact hVisNodup'
          · exact List.mem_append.mpr (Or.inr hqRest)
      next hnsize =>
        exact absurd (visited_size_lt hBound hVisInUniv hVisNodup) hnsize
termination_by (bound - visited.size, worklist.length)
decreasing_by
  · simp_wf
    refine Prod.lex_def.mpr (Or.inl ?_)
    omega
  · simp_wf
    refine Prod.lex_def.mpr (Or.inr ⟨rfl, ?_⟩)
    omega

theorem closureGo_step_closed_aux
    (rdeps : Array (ℭ.Q × ℭ.Q)) (univ : List ℭ.Q)
    (bound : Nat) (hBound : univ.length + 1 ≤ bound)
    (hRdepsInUniv : ∀ p ∈ rdeps, p.snd ∈ univ)
    (worklist : List ℭ.Q) (visited : Array ℭ.Q) (hv : visited.size ≤ bound)
    (hWorkInUniv : ∀ x ∈ worklist, x ∈ univ)
    (hVisInUniv : ∀ x ∈ visited.toList, x ∈ univ)
    (hVisNodup : visited.toList.Nodup)
    (hInv : ∀ k ∈ visited, ∀ q', (k, q') ∈ rdeps → q' ∈ visited ∨ q' ∈ worklist)
    (k : ℭ.Q) (hk : k ∈ closureGo rdeps bound worklist visited hv)
    (q' : ℭ.Q) (hedge : (k, q') ∈ rdeps) :
    q' ∈ closureGo rdeps bound worklist visited hv := by
  match worklist with
  | [] =>
    unfold closureGo at hk ⊢
    exact (hInv k hk q' hedge).resolve_right List.not_mem_nil
  | k0 :: rest =>
    by_cases hcontains : visited.toList.contains k0 = true
    · have hk0InVis : k0 ∈ visited := visited_of_contains hcontains
      have hStepEq : closureGo rdeps bound (k0 :: rest) visited hv =
          closureGo rdeps bound rest visited hv := by
        conv_lhs => unfold closureGo
        rw [if_pos hcontains]
      have hInv' : ∀ k ∈ visited, ∀ q', (k, q') ∈ rdeps → q' ∈ visited ∨ q' ∈ rest :=
        fun k hk q' hedge => (hInv k hk q' hedge).elim Or.inl fun h =>
          (List.mem_cons.mp h).elim (· ▸ Or.inl hk0InVis) Or.inr
      rw [hStepEq] at hk ⊢
      exact closureGo_step_closed_aux rdeps univ bound hBound hRdepsInUniv rest visited hv
        (fun x hx => hWorkInUniv x (List.mem_cons_of_mem _ hx))
        hVisInUniv hVisNodup hInv' k hk q' hedge
    · have hkNotInVis : k0 ∉ visited := not_visited_of_not_contains hcontains
      by_cases hsize : visited.size < bound
      · have hv' : (visited.push k0).size ≤ bound := by rw [Array.size_push]; omega
        have hk0InUniv : k0 ∈ univ := hWorkInUniv k0 List.mem_cons_self
        have hVisInUniv' := push_toList_inUniv hVisInUniv hk0InUniv
        have hVisNodup' := push_toList_nodup hVisNodup hkNotInVis
        have hNewInUniv := rdeps_foldl_new_in_univ rdeps univ k0 hRdepsInUniv []
          (fun _ h => absurd h List.not_mem_nil)
        let new := rdeps.foldl (init := [])
          fun acc p => if p.fst == k0 then p.snd :: acc else acc
        have hNewWorkInUniv : ∀ x ∈ new ++ rest, x ∈ univ := by
          intro x hx
          rcases List.mem_append.mp hx with hxNew | hxRest
          · exact hNewInUniv x hxNew
          · exact hWorkInUniv x (List.mem_cons_of_mem _ hxRest)
        have hNewContainsConsumers : ∀ q', (k0, q') ∈ rdeps → q' ∈ new := by
          intro q' hedge
          show q' ∈ rdeps.foldl
            (init := []) (fun acc p => if p.fst == k0 then p.snd :: acc else acc)
          have ⟨i, hi, hieq⟩ := Array.getElem_of_mem hedge
          refine Array.foldl_induction
            (motive := fun n l =>
              n > i → q' ∈ l)
            ?_ ?_ (by omega)
          · omega
          · intro j acc' ih hj
            dsimp only
            by_cases hij : j = i
            · subst hij
              have : rdeps[j] = (k0, q') := hieq
              rw [this]
              simp only [BEq.refl, if_true, List.mem_cons, true_or]
            · have hji : j > i := by omega
              have := ih hji
              split
              · exact List.mem_cons_of_mem _ this
              · exact this
        have hInv' : ∀ k ∈ visited.push k0, ∀ q', (k, q') ∈ rdeps →
            q' ∈ visited.push k0 ∨ q' ∈ new ++ rest := by
          intro k hk q' hedge
          rcases Array.mem_push.mp hk with hk | rfl
          · rcases hInv k hk q' hedge with h | h
            · exact Or.inl (Array.mem_push.mpr (Or.inl h))
            · rcases List.mem_cons.mp h with rfl | h
              · exact Or.inl Array.mem_push_self
              · exact Or.inr (List.mem_append.mpr (Or.inr h))
          · exact Or.inr (List.mem_append.mpr (Or.inl (hNewContainsConsumers q' hedge)))
        have hStepEq : closureGo rdeps bound (k0 :: rest) visited hv =
            closureGo rdeps bound (new ++ rest) (visited.push k0) hv' := by
          conv_lhs => unfold closureGo
          rw [if_neg hcontains, dif_pos hsize]
        rw [hStepEq] at hk ⊢
        exact closureGo_step_closed_aux rdeps univ bound hBound hRdepsInUniv (new ++ rest)
          (visited.push k0) hv' hNewWorkInUniv hVisInUniv' hVisNodup' hInv' k hk q' hedge
      · exact absurd (visited_size_lt hBound hVisInUniv hVisNodup) hsize
termination_by (bound - visited.size, worklist.length)
decreasing_by
  · simp_wf
    refine Prod.lex_def.mpr (Or.inr ⟨rfl, ?_⟩)
    omega
  · simp_wf
    refine Prod.lex_def.mpr (Or.inl ?_)
    omega

theorem closure_seed_subset
    (rdeps : Array (ℭ.Q × ℭ.Q)) (seed : Array ℭ.Q)
    (q : ℭ.Q) (hq : q ∈ seed) : q ∈ closure rdeps seed := by
  unfold closure
  apply closureGo_worklist_subset rdeps (seed.toList ++ rdeps.toList.map (·.2))
    (seed.size + rdeps.size + 1)
  · simp
  · intro p hp
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩))
  · intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  · nofun
  · simp
  · exact Array.mem_toList_iff.mpr hq

theorem closure_step_closed
    (rdeps : Array (ℭ.Q × ℭ.Q)) (seed : Array ℭ.Q)
    (k : ℭ.Q) (hk : k ∈ closure rdeps seed)
    (q' : ℭ.Q) (hedge : (k, q') ∈ rdeps) :
    q' ∈ closure rdeps seed := by
  unfold closure at hk ⊢
  apply closureGo_step_closed_aux rdeps (seed.toList ++ rdeps.toList.map (·.2))
    (seed.size + rdeps.size + 1)
  · simp
  · intro p hp
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, Array.mem_toList_iff.mpr hp, rfl⟩))
  · intro x hx
    exact List.mem_append.mpr (Or.inl hx)
  · nofun
  · simp
  · nofun
  · exact hk
  · exact hedge

end

section

variable {ℭ : BuildConfig} [BEq ℭ.I]

def seedOf (rdeps : Array (ℭ.I × ℭ.Q)) (i : ℭ.I) : Array ℭ.Q :=
  rdeps.foldl (init := #[]) fun acc (i', q) =>
    if i' == i then acc.push q else acc

end

section

variable {ℭ : BuildConfig} [BEq ℭ.I] [LawfulBEq ℭ.I]

theorem mem_seedOf (rdeps : Array (ℭ.I × ℭ.Q)) (i : ℭ.I) (q : ℭ.Q) :
    q ∈ seedOf rdeps i ↔ (i, q) ∈ rdeps := by
  unfold seedOf
  constructor
  · intro hMem
    refine (Array.foldl_induction
        (motive := fun _ (a : Array ℭ.Q) =>
          q ∈ a → q ∈ (#[] : Array ℭ.Q) ∨ (i, q) ∈ rdeps)
        Or.inl
        (fun j acc' ih hMem' => by
          dsimp only at hMem'
          split at hMem'
          next heq =>
            rcases Array.mem_push.mp hMem' with hMem' | hqEq
            · exact ih hMem'
            · right
              have hieq : rdeps[j.val].fst = i := LawfulBEq.eq_of_beq heq
              have hpair : (i, q) = rdeps[j.val] := by
                rw [hqEq, ← hieq]
                exact Prod.mk.eta
              rw [hpair]
              exact Array.getElem_mem _
          next => exact ih hMem')
        hMem).resolve_left ?_
    nofun
  · intro hMem
    have ⟨j, hj, hieq⟩ := Array.getElem_of_mem hMem
    refine Array.foldl_induction
      (motive := fun n a => n > j → q ∈ a)
      ?_ ?_ (by omega)
    · omega
    · intro j' acc' ih hj'
      dsimp only
      by_cases hjj : j' = j
      · subst hjj
        have : rdeps[j'] = (i, q) := hieq
        rw [this]
        simp only [BEq.refl, if_true, Array.mem_push_self]
      · have hji : j' > j := by omega
        have := ih hji
        split
        · exact Array.mem_push.mpr (Or.inl this)
        · exact this

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [Hashable ℭ.Q]

structure Persist where
  cache : Shake.Cache hI hR tasks
  queryRdeps : Array (ℭ.Q × ℭ.Q)
  inputRdeps : Array (ℭ.I × ℭ.Q)
  dirty : Array ℭ.Q

private theorem foldl_inputRdeps_unchanged {α} (xs : Array α)
    (p : Persist hI hR tasks) (f : Persist hI hR tasks → α → ℭ.I × ℭ.Q) :
    let p' := xs.foldl (init := p) fun p x =>
      { p with inputRdeps := p.inputRdeps.push (f p x) }
    p'.cache = p.cache ∧ p'.dirty = p.dirty ∧ p'.queryRdeps = p.queryRdeps :=
  Array.foldl_induction
    (motive := fun _ (p' : Persist hI hR tasks) =>
      p'.cache = p.cache ∧ p'.dirty = p.dirty ∧ p'.queryRdeps = p.queryRdeps)
    ⟨rfl, rfl, rfl⟩ (fun _ _ h => h)

private theorem foldl_queryRdeps_unchanged {α} (xs : Array α)
    (p : Persist hI hR tasks) (f : Persist hI hR tasks → α → ℭ.Q × ℭ.Q) :
    let p' := xs.foldl (init := p) fun p x =>
      { p with queryRdeps := p.queryRdeps.push (f p x) }
    p'.cache = p.cache ∧ p'.dirty = p.dirty ∧ p'.inputRdeps = p.inputRdeps :=
  Array.foldl_induction
    (motive := fun _ (p' : Persist hI hR tasks) =>
      p'.cache = p.cache ∧ p'.dirty = p.dirty ∧ p'.inputRdeps = p.inputRdeps)
    ⟨rfl, rfl, rfl⟩ (fun _ _ h => h)

private theorem foldl_inputRdeps_mono {α} (xs : Array α)
    (p : Persist hI hR tasks) (f : Persist hI hR tasks → α → ℭ.I × ℭ.Q)
    (e : ℭ.I × ℭ.Q) (he : e ∈ p.inputRdeps) :
    e ∈ (xs.foldl (init := p) fun p x =>
      { p with inputRdeps := p.inputRdeps.push (f p x) }).inputRdeps :=
  Array.foldl_induction
    (motive := fun _ (p' : Persist hI hR tasks) => e ∈ p'.inputRdeps)
    he (fun _ _ h => Array.mem_push.mpr (Or.inl h))

private theorem foldl_queryRdeps_mono {α} (xs : Array α)
    (p : Persist hI hR tasks) (f : Persist hI hR tasks → α → ℭ.Q × ℭ.Q)
    (e : ℭ.Q × ℭ.Q) (he : e ∈ p.queryRdeps) :
    e ∈ (xs.foldl (init := p) fun p x =>
      { p with queryRdeps := p.queryRdeps.push (f p x) }).queryRdeps :=
  Array.foldl_induction
    (motive := fun _ (p' : Persist hI hR tasks) => e ∈ p'.queryRdeps)
    he (fun _ _ h => Array.mem_push.mpr (Or.inl h))

def recordRdeps
    (q : ℭ.Q) (mm : Shake.Memo hI hR tasks q)
    (p : Persist hI hR tasks) : Persist hI hR tasks :=
  let p := mm.inputDeps.foldl (init := p) fun p d =>
    { p with inputRdeps := p.inputRdeps.push (d.key, q) }
  mm.queryDeps.foldl (init := p) fun p d =>
    { p with queryRdeps := p.queryRdeps.push (d.q, q) }

theorem recordRdeps_cache (q : ℭ.Q) (mm : Shake.Memo hI hR tasks q)
    (p : Persist hI hR tasks) : (recordRdeps hI hR tasks q mm p).cache = p.cache := by
  unfold recordRdeps
  exact (foldl_queryRdeps_unchanged hI hR tasks _ _ _).left.trans
    (foldl_inputRdeps_unchanged hI hR tasks _ _ _).left

theorem recordRdeps_dirty (q : ℭ.Q) (mm : Shake.Memo hI hR tasks q)
    (p : Persist hI hR tasks) : (recordRdeps hI hR tasks q mm p).dirty = p.dirty := by
  unfold recordRdeps
  exact (foldl_queryRdeps_unchanged hI hR tasks _ _ _).right.left.trans
    (foldl_inputRdeps_unchanged hI hR tasks _ _ _).right.left

partial def closureFastGo
    (rdepsMap : Std.HashMap ℭ.Q (Array ℭ.Q))
    (worklist : List ℭ.Q) (visited : Std.HashSet ℭ.Q) : Std.HashSet ℭ.Q :=
  match worklist with
  | [] => visited
  | k :: rest =>
    if visited.contains k then closureFastGo rdepsMap rest visited
    else
      let visited' := visited.insert k
      let new := (rdepsMap.getD k #[]).toList
      closureFastGo rdepsMap (new ++ rest) visited'

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [Hashable ℭ.Q] [BEq ℭ.I]

def invalidateFast (p : Persist hI hR tasks) (i : ℭ.I) : Persist hI hR tasks :=
  let rdepsMap : Std.HashMap ℭ.Q (Array ℭ.Q) :=
    p.queryRdeps.foldl (init := Std.HashMap.emptyWithCapacity p.queryRdeps.size)
      fun m (k, c) => m.alter k (·.getD #[] |>.push c)
  let seed : List ℭ.Q :=
    p.inputRdeps.foldl (init := [])
      fun s (i', q) => if i' == i then q :: s else s
  let visited := closureFastGo rdepsMap seed
    (Std.HashSet.emptyWithCapacity (seed.length + p.queryRdeps.size))
  { p with dirty := visited.fold (init := p.dirty) fun a q => a.push q }

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]

def Sound (ι₀ : ∀ i, ℭ.V i) (p : Persist hI hR tasks) : Prop :=
  ∀ q (mm : Shake.Memo hI hR tasks q),
    p.cache.get? q = some mm → q ∉ p.dirty →
    (∀ d ∈ mm.inputDeps, hI d.key (ι₀ d.key) = d.hash) ∧
    (∀ d ∈ mm.queryDeps, hR d.q (compute tasks ι₀ d.q) = d.hash)

def Sound.value
    {ι₀ : ∀ i, ℭ.V i} {p : Persist hI hR tasks}
    (hSound : Sound hI hR tasks ι₀ p) :
    ∀ q (mm : Shake.Memo hI hR tasks q),
      p.cache.get? q = some mm → q ∉ p.dirty →
      mm.value = compute tasks ι₀ q := fun q mm hGet hNotDirty =>
  let ⟨hI', hR'⟩ := hSound q mm hGet hNotDirty
  mm.invariant ι₀ hI' hR'

def Complete (p : Persist hI hR tasks) : Prop :=
  (∀ q (mm : Shake.Memo hI hR tasks q),
      p.cache.get? q = some mm →
      ∀ d ∈ mm.inputDeps, (d.key, q) ∈ p.inputRdeps) ∧
  (∀ q (mm : Shake.Memo hI hR tasks q),
      p.cache.get? q = some mm →
      ∀ d ∈ mm.queryDeps, (d.q, q) ∈ p.queryRdeps)

def Closed (p : Persist hI hR tasks) : Prop :=
  ∀ q (mm : Shake.Memo hI hR tasks q),
    p.cache.get? q = some mm →
    ∀ d ∈ mm.queryDeps, ∃ mm', p.cache.get? d.q = some mm'

def DownClosed (p : Persist hI hR tasks) : Prop :=
  ∀ q (mm : Shake.Memo hI hR tasks q),
    p.cache.get? q = some mm → q ∉ p.dirty →
    ∀ d ∈ mm.queryDeps, d.q ∉ p.dirty

private theorem cache_insert_cases {p : Persist hI hR tasks} {q q' : ℭ.Q}
    {memo : Shake.Memo hI hR tasks q} {mm' : Shake.Memo hI hR tasks q'}
    (hGet : (p.cache.insert q memo).get? q' = some mm') :
    (∃ h : q = q', mm' = h ▸ memo) ∨ (q ≠ q' ∧ p.cache.get? q' = some mm') := by
  rw [DHashMap.get?_insert] at hGet
  by_cases hq : (q == q') = true
  · simp [hq] at hGet
    have hqq : q = q' := LawfulBEq.eq_of_beq hq
    subst hqq
    cases hGet
    exact Or.inl ⟨rfl, rfl⟩
  · simp [hq] at hGet
    exact Or.inr ⟨fun h => hq (h ▸ beq_self_eq_true q), hGet⟩

private theorem cache_insert_get?_exists {p : Persist hI hR tasks} {q q' : ℭ.Q}
    (memo : Shake.Memo hI hR tasks q) {mm' : Shake.Memo hI hR tasks q'}
    (hGet : p.cache.get? q' = some mm') :
    ∃ mm'', (p.cache.insert q memo).get? q' = some mm'' := by
  by_cases hqq : q = q'
  · subst hqq
    exact ⟨memo, DHashMap.get?_insert_self⟩
  · refine ⟨mm', ?_⟩
    rw [DHashMap.get?_insert]
    have hbeq : (q == q') = false := by simpa using hqq
    simpa [hbeq] using hGet

def Persist.empty : Persist hI hR tasks where
  cache := DHashMap.emptyWithCapacity 1024
  queryRdeps := #[]
  inputRdeps := #[]
  dirty := #[]

private def empty_cache_get?_elim {q} {mm : Shake.Memo hI hR tasks q} {α : Sort _}
    (hget : (Persist.empty hI hR tasks).cache.get? q = some mm) : α :=
  nomatch hget.symm.trans DHashMap.get?_emptyWithCapacity

private theorem queryPass_queryRdeps_adds {q : ℭ.Q} (q' : ℭ.Q) (xs : Array (QueryDepHash ℭ q H))
    (p : Persist hI hR tasks) (d : QueryDepHash ℭ q H) (hd : d ∈ xs) :
    (d.q, q') ∈ (xs.foldl (init := p) fun p d =>
      { p with queryRdeps := p.queryRdeps.push (d.q, q') }).queryRdeps := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hd
  refine Array.foldl_induction
    (motive := fun n (p' : Persist hI hR tasks) =>
      n > i → (xs[i].q, q') ∈ p'.queryRdeps)
    ?_ ?_ (by omega)
  · omega
  · intro j p' h hj
    by_cases hij : j = i
    · subst hij
      show (xs[j].q, q') ∈ (p'.queryRdeps.push (xs[j].q, q'))
      exact Array.mem_push_self
    · have hji : j > i := by omega
      have := h hji
      show (xs[i].q, q') ∈ (p'.queryRdeps.push (xs[j].q, q'))
      exact Array.mem_push.mpr (Or.inl this)

theorem recordRdeps_preserves_sound
    (p : Persist hI hR tasks) (ι₀ : ∀ i, ℭ.V i) (q : ℭ.Q)
    (mm : Shake.Memo hI hR tasks q) (newDirty : Array ℭ.Q)
    (hDirtyMem : ∀ q', q' ≠ q → q' ∈ p.dirty → q' ∈ newDirty)
    (hVerifyIns : ∀ d ∈ mm.inputDeps, hI d.key (ι₀ d.key) = d.hash)
    (hVerifyDeps : ∀ d ∈ mm.queryDeps, hR d.q (compute tasks ι₀ d.q) = d.hash)
    (hSound : Sound hI hR tasks ι₀ p) :
    Sound hI hR tasks ι₀
      (recordRdeps hI hR tasks q mm { p with
        cache := p.cache.insert q mm
        dirty := newDirty }) := by
  intro q' mm' hGet' hNotDirty'
  rw [recordRdeps_cache] at hGet'
  rw [recordRdeps_dirty] at hNotDirty'
  rcases cache_insert_cases hI hR tasks hGet' with ⟨rfl, rfl⟩ | ⟨hne, hOld⟩
  · exact ⟨hVerifyIns, hVerifyDeps⟩
  · exact hSound q' mm' hOld fun hContains =>
      hNotDirty' (hDirtyMem q' (Ne.symm hne) hContains)

structure WellFormed (ι₀ : ∀ i, ℭ.V i) (p : Persist hI hR tasks) : Prop where
  sound : Sound hI hR tasks ι₀ p
  complete : Complete hI hR tasks p
  closed : Closed hI hR tasks p
  downClosed : DownClosed hI hR tasks p

theorem wellFormed_empty (ι₀ : ∀ i, ℭ.V i) :
    WellFormed hI hR tasks ι₀ (.empty hI hR tasks) where
  sound _ _ hget _ := empty_cache_get?_elim hI hR tasks hget
  complete := ⟨fun _ _ hget _ _ => empty_cache_get?_elim hI hR tasks hget,
               fun _ _ hget _ _ => empty_cache_get?_elim hI hR tasks hget⟩
  closed _ _ hget := empty_cache_get?_elim hI hR tasks hget
  downClosed _ _ hget _ := empty_cache_get?_elim hI hR tasks hget

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  [BEq ℭ.I]

def invalidate (p : Persist hI hR tasks) (i : ℭ.I) : Persist hI hR tasks :=
  { p with dirty := p.dirty ++ closure p.queryRdeps (seedOf p.inputRdeps i) }

theorem invalidate_preserves_downClosed
    (p : Persist hI hR tasks) (i : ℭ.I)
    (hComplete : Complete hI hR tasks p)
    (hDownClosed : DownClosed hI hR tasks p) :
    DownClosed hI hR tasks (invalidate hI hR tasks p i) := by
  have ⟨_, hCompQ⟩ := hComplete
  intro q mm hGet hNotDirty d hd
  have hNotP : q ∉ p.dirty := fun h => hNotDirty (Array.mem_append.mpr (Or.inl h))
  have hNotC : q ∉ closure p.queryRdeps (seedOf p.inputRdeps i) :=
    fun h => hNotDirty (Array.mem_append.mpr (Or.inr h))
  exact fun h => (Array.mem_append.mp h).elim
    (hDownClosed q mm hGet hNotP d hd)
    (fun hc => hNotC (closure_step_closed _ _ d.q hc q (hCompQ q mm hGet d hd)))

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  [BEq ℭ.I] [LawfulBEq ℭ.I]

private theorem inputPass_inputRdeps_adds (q' : ℭ.Q) (xs : Array (InputDepHash ℭ.I H))
    (p : Persist hI hR tasks) (d : InputDepHash ℭ.I H) (hd : d ∈ xs) :
    (d.key, q') ∈ (xs.foldl (init := p) fun p d =>
      { p with inputRdeps := p.inputRdeps.push (d.key, q') }).inputRdeps := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hd
  refine Array.foldl_induction
    (motive := fun n (p' : Persist hI hR tasks) =>
      n > i → (xs[i].key, q') ∈ p'.inputRdeps)
    ?_ ?_ (by omega)
  · omega
  · intro j p' h hj
    by_cases hij : j = i
    · subst hij
      show (xs[j].key, q') ∈ (p'.inputRdeps.push (xs[j].key, q'))
      exact Array.mem_push_self
    · have hji : j > i := by omega
      have := h hji
      show (xs[i].key, q') ∈ (p'.inputRdeps.push (xs[j].key, q'))
      exact Array.mem_push.mpr (Or.inl this)

theorem recordRdeps_preserves_complete
    (p : Persist hI hR tasks) (q : ℭ.Q)
    (mm : Shake.Memo hI hR tasks q)
    (newDirty : Array ℭ.Q)
    (hComplete : Complete hI hR tasks p) :
    Complete hI hR tasks
      (recordRdeps hI hR tasks q mm { p with
        cache := p.cache.insert q mm
        dirty := newDirty }) := by
  have ⟨hCompIn, hCompQ⟩ := hComplete
  refine ⟨?_, ?_⟩
  · intro q' mm' hGet' d hd
    rw [recordRdeps_cache] at hGet'
    unfold recordRdeps
    rw [(foldl_queryRdeps_unchanged hI hR tasks _ _ _).right.right]
    rcases cache_insert_cases hI hR tasks hGet' with ⟨rfl, rfl⟩ | ⟨_, hOld⟩
    · exact inputPass_inputRdeps_adds hI hR tasks q mm'.inputDeps _ d hd
    · exact foldl_inputRdeps_mono hI hR tasks _ _ _ _ (hCompIn q' mm' hOld d hd)
  · intro q' mm' hGet' d hd
    rw [recordRdeps_cache] at hGet'
    unfold recordRdeps
    rcases cache_insert_cases hI hR tasks hGet' with ⟨rfl, rfl⟩ | ⟨_, hOld⟩
    · exact queryPass_queryRdeps_adds hI hR tasks q mm'.queryDeps _ d hd
    · refine foldl_queryRdeps_mono hI hR tasks _ _ _ _ ?_
      rw [(foldl_inputRdeps_unchanged hI hR tasks mm.inputDeps _ _).right.right]
      exact hCompQ q' mm' hOld d hd

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [DecidableEq ℭ.I]

theorem invalidate_preserves_sound
    (p : Persist hI hR tasks) (ι₀ : ∀ i, ℭ.V i) (i : ℭ.I) (v : ℭ.V i)
    (hSound : Sound hI hR tasks ι₀ p)
    (hComplete : Complete hI hR tasks p)
    (hClosed : Closed hI hR tasks p)
    (hDownClosed : DownClosed hI hR tasks p) :
    Sound hI hR tasks (Function.update ι₀ i v) (invalidate hI hR tasks p i) := by
  have ⟨hCompIn, hCompQ⟩ := hComplete
  intro q'
  induction q' using ℭ.wf.induction with
  | _ q' IH =>
    intro mm' hGet' hNotDirty'
    have hNotP : q' ∉ p.dirty := fun h => hNotDirty' (Array.mem_append.mpr (Or.inl h))
    have hNotC : q' ∉ closure p.queryRdeps (seedOf p.inputRdeps i) :=
      fun h => hNotDirty' (Array.mem_append.mpr (Or.inr h))
    have ⟨hVI₀, hVD₀⟩ := hSound q' mm' hGet' hNotP
    refine ⟨?_, ?_⟩
    · intro d hd
      by_cases hki : d.key = i
      · exfalso
        apply hNotC
        apply closure_seed_subset
        rw [mem_seedOf, ← hki]
        exact hCompIn q' mm' hGet' d hd
      · rw [Function.update_of_ne hki]
        exact hVI₀ d hd
    · intro d hd
      have hEdge : (d.q, q') ∈ p.queryRdeps := hCompQ q' mm' hGet' d hd
      have hDqNotC : d.q ∉ closure p.queryRdeps (seedOf p.inputRdeps i) :=
        fun h => hNotC (closure_step_closed _ _ d.q h q' hEdge)
      have hDqNotP : d.q ∉ p.dirty := hDownClosed q' mm' hGet' hNotP d hd
      have ⟨mm'', hMM''⟩ := hClosed q' mm' hGet' d hd
      have hDqNotInInv : d.q ∉ (invalidate hI hR tasks p i).dirty :=
        fun h => (Array.mem_append.mp h).elim hDqNotP hDqNotC
      have hIH : (∀ (d_1 : InputDepHash ℭ.I H), d_1 ∈ mm''.inputDeps →
            (hI d_1.key) (Function.update ι₀ i v d_1.key) = d_1.hash) ∧
          ∀ (d_1 : QueryDepHash ℭ d.q H), d_1 ∈ mm''.queryDeps →
            (hR d_1.q) (compute tasks (Function.update ι₀ i v) d_1.q) = d_1.hash :=
        IH d.q d.rel mm'' hMM'' hDqNotInInv
      have hComputeEq : compute tasks (Function.update ι₀ i v) d.q = compute tasks ι₀ d.q :=
        (mm''.invariant _ hIH.left hIH.right).symm.trans
          (Sound.value hI hR tasks hSound d.q mm'' hMM'' hDqNotP)
      rw [hComputeEq]
      exact hVD₀ d hd

theorem wellFormed_invalidate
    (p : Persist hI hR tasks) (ι₀ : ∀ i, ℭ.V i) (i : ℭ.I) (v : ℭ.V i)
    (hWF : WellFormed hI hR tasks ι₀ p) :
    WellFormed hI hR tasks (Function.update ι₀ i v) (invalidate hI hR tasks p i) where
  sound := invalidate_preserves_sound hI hR tasks p ι₀ i v
    hWF.sound hWF.complete hWF.closed hWF.downClosed
  complete := hWF.complete
  closed := hWF.closed
  downClosed := invalidate_preserves_downClosed hI hR tasks p i hWF.complete hWF.downClosed

end

section

variable
  {ℭ : BuildConfig} {H : Type}
  (hI : ∀ i, ℭ.V i ↪ H)
  (hR : ∀ q, ℭ.R q ↪ H)
  (tasks : Tasks ℭ)
  [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
  [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [DecidableEq ℭ.I]
  [DecidableEq H]
  (ι₀ : ∀ i, ℭ.V i)

structure PopulateResult (q : ℭ.Q) (pIn : Persist hI hR tasks) where
  persist : Persist hI hR tasks
  value : Value tasks ι₀ q
  hWF : WellFormed hI hR tasks ι₀ persist
  hNotDirty : q ∉ persist.dirty
  memo : Shake.Memo hI hR tasks q
  hCache : persist.cache.get? q = some memo
  hValEq : memo.value = value.val
  hCacheMono : ∀ q' (mm' : Shake.Memo hI hR tasks q'),
    pIn.cache.get? q' = some mm' → ∃ mm'', persist.cache.get? q' = some mm''
  hDirtyAntiMono : ∀ q', q' ∈ persist.dirty → q' ∈ pIn.dirty

structure RunWalkResult {q₀ : ℭ.Q} {α : Type}
    (t : FM ℭ q₀ α) (pIn : Persist hI hR tasks)
    (accQueryDeps : Array (QueryDepHash ℭ q₀ H)) where
  value : α
  persist : Persist hI hR tasks
  hWF : WellFormed hI hR tasks ι₀ persist
  inputDepsList : List (InputDepHash ℭ.I H)
  queryDepsArr : Array (QueryDepHash ℭ q₀ H)
  hValue : value = FM.evalTree ι₀ (compute tasks ι₀) t
  hInputDeps : inputDepsList =
    (FM.evalTrace_inputs ι₀ (compute tasks ι₀) t).map (fun e => ⟨⟨e.i⟩, hI e.i e.v⟩)
  hQueryDeps : queryDepsArr =
    Shake.pushAll hR (FM.evalTrace_deps ι₀ (compute tasks ι₀) t) accQueryDeps
  hDepsInCache : ∀ d ∈ FM.evalTrace_deps ι₀ (compute tasks ι₀) t,
    ∃ mm, persist.cache.get? d.q = some mm
  hDepsNotDirty : ∀ d ∈ FM.evalTrace_deps ι₀ (compute tasks ι₀) t, d.q ∉ persist.dirty
  hCacheMono : ∀ q' (mm' : Shake.Memo hI hR tasks q'),
    pIn.cache.get? q' = some mm' → ∃ mm'', persist.cache.get? q' = some mm''
  hDirtyAntiMono : ∀ q', q' ∈ persist.dirty → q' ∈ pIn.dirty

def runWalk (q₀ : ℭ.Q) {α : Type} (t : FM ℭ q₀ α)
    (p : Persist hI hR tasks) (hWF : WellFormed hI hR tasks ι₀ p)
    (accQueryDeps : Array (QueryDepHash ℭ q₀ H))
    (ih : ∀ q', ℭ.rel q' q₀ → ∀ (p' : Persist hI hR tasks)
        (_ : WellFormed hI hR tasks ι₀ p'),
      PopulateResult hI hR tasks ι₀ q' p') :
    RunWalkResult hI hR tasks ι₀ t p accQueryDeps :=
  match t with
  | FM.pure a =>
    { value := a, persist := p, hWF
      inputDepsList := []
      queryDepsArr := accQueryDeps
      hValue := rfl
      hInputDeps := rfl
      hQueryDeps := rfl
      hDepsInCache := nofun
      hDepsNotDirty := nofun
      hCacheMono := fun _ _ h => ⟨_, h⟩
      hDirtyAntiMono := fun _ h => h }
  | FM.input i k =>
    let v := ι₀ i
    let r := runWalk q₀ (k v) p hWF accQueryDeps ih
    { r with
      inputDepsList := ⟨⟨i⟩, hI i v⟩ :: r.inputDepsList
      hInputDeps := congrArg _ r.hInputDeps }
  | FM.fetch q hq k =>
    let pr := ih q hq p hWF
    have hVEq : pr.value.val = compute tasks ι₀ q := pr.value.spec
    let newAcc := Shake.dedupPush
      (⟨⟨q, hq⟩, hR q pr.value.val⟩ : QueryDepHash ℭ q₀ H) accQueryDeps
    let r := runWalk q₀ (k pr.value.val) pr.persist pr.hWF newAcc ih
    { r with
      hValue := by
        change r.value = FM.evalTree ι₀ (compute tasks ι₀) (k (compute tasks ι₀ q))
        rw [← hVEq]
        exact r.hValue
      hInputDeps := by
        change r.inputDepsList = (FM.evalTrace_inputs ι₀ (compute tasks ι₀)
          (k (compute tasks ι₀ q))).map _
        rw [← hVEq]
        exact r.hInputDeps
      hQueryDeps := by
        change r.queryDepsArr =
          Shake.pushAll hR (FM.evalTrace_deps ι₀ (compute tasks ι₀) (k (compute tasks ι₀ q)))
            (Shake.dedupPush ⟨⟨q, hq⟩, hR q (compute tasks ι₀ q)⟩ accQueryDeps)
        rw [← hVEq]
        exact r.hQueryDeps
      hDepsInCache := fun d hd => by
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact r.hCacheMono q pr.memo pr.hCache
        · rw [← hVEq] at hd'
          exact r.hDepsInCache d hd'
      hDepsNotDirty := fun d hd hMem => by
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact pr.hNotDirty (r.hDirtyAntiMono q hMem)
        · rw [← hVEq] at hd'
          exact r.hDepsNotDirty d hd' hMem
      hCacheMono := fun q' mm' h =>
        let ⟨mm'', h''⟩ := pr.hCacheMono q' mm' h
        r.hCacheMono q' mm'' h''
      hDirtyAntiMono := fun q' h =>
        pr.hDirtyAntiMono q' (r.hDirtyAntiMono q' h) }

def populateRecompute
    (q : ℭ.Q)
    (ih : ∀ q', ℭ.rel q' q → ∀ (p : Persist hI hR tasks)
        (_ : WellFormed hI hR tasks ι₀ p),
      PopulateResult hI hR tasks ι₀ q' p)
    (p : Persist hI hR tasks) (hWF : WellFormed hI hR tasks ι₀ p) :
    PopulateResult hI hR tasks ι₀ q p :=
  let r := runWalk hI hR tasks ι₀ q (tasksTree ℭ tasks q) p hWF #[] ih
  let inputDeps := r.inputDepsList.toArray
  let queryDeps := r.queryDepsArr
  have hVal : r.value = compute tasks ι₀ q :=
    r.hValue.trans (Incremental.tasksTree_eval_compute ℭ tasks q ι₀)
  have hInputDepsEq : inputDeps =
      ((FM.evalTrace_inputs ι₀ (compute tasks ι₀) (tasksTree ℭ tasks q)).map
        (fun e => ⟨⟨e.i⟩, hI e.i e.v⟩)).toArray :=
    congrArg List.toArray r.hInputDeps
  have hQueryDepsEq : queryDeps =
      Shake.pushAll hR (FM.evalTrace_deps ι₀ (compute tasks ι₀) (tasksTree ℭ tasks q)) #[] :=
    r.hQueryDeps
  let memo : Shake.Memo hI hR tasks q := {
    value := r.value
    inputDeps
    queryDeps
    invariant := Shake.cacheMiss_invariant hI hR tasks hVal hInputDepsEq hQueryDepsEq
  }
  have hVI : ∀ d ∈ memo.inputDeps, hI d.key (ι₀ d.key) = d.hash :=
    Shake.cacheMiss_verify_ins (hI := hI) (tasks := tasks) hInputDepsEq
  have hVD : ∀ d ∈ memo.queryDeps, hR d.q (compute tasks ι₀ d.q) = d.hash :=
    Shake.cacheMiss_verify_deps (hR := hR) (tasks := tasks) hQueryDepsEq
  let pAfter := recordRdeps hI hR tasks q memo {
    r.persist with
    cache := r.persist.cache.insert q memo
    dirty := r.persist.dirty.filter (· != q)
  }
  have hCacheEq : pAfter.cache = r.persist.cache.insert q memo := recordRdeps_cache ..
  have hDirtyEq : pAfter.dirty = r.persist.dirty.filter (· != q) := recordRdeps_dirty ..
  have hSound : Sound hI hR tasks ι₀ pAfter :=
    recordRdeps_preserves_sound hI hR tasks r.persist ι₀ q memo _
      (fun _ hne hMem => Array.mem_filter.mpr ⟨hMem, by simpa using hne⟩) hVI hVD r.hWF.sound
  have hComplete : Complete hI hR tasks pAfter :=
    recordRdeps_preserves_complete hI hR tasks r.persist q memo _ r.hWF.complete
  have hMemoDepsOrigin : ∀ d ∈ memo.queryDeps,
      ∃ e ∈ FM.evalTrace_deps ι₀ (compute tasks ι₀) (tasksTree ℭ tasks q), d.q = e.q := by
    intro d hd
    have hd' : d ∈ Shake.pushAll hR
        (FM.evalTrace_deps ι₀ (compute tasks ι₀) (tasksTree ℭ tasks q)) #[] := hQueryDepsEq ▸ hd
    rcases Shake.pushAll_origin hR _ _ d hd' with hd_acc | ⟨e, he_mem, he_q⟩
    · nomatch hd_acc
    · exact ⟨e, he_mem, he_q⟩
  have hMemoDepsInCache : ∀ d ∈ memo.queryDeps,
      ∃ mm, r.persist.cache.get? d.q = some mm := fun d hd =>
    let ⟨e, he_mem, he_q⟩ := hMemoDepsOrigin d hd
    he_q ▸ r.hDepsInCache e he_mem
  have hMemoDepsNotDirty : ∀ d ∈ memo.queryDeps, d.q ∉ r.persist.dirty := fun d hd =>
    let ⟨e, he_mem, he_q⟩ := hMemoDepsOrigin d hd
    he_q ▸ r.hDepsNotDirty e he_mem
  have hClosed : Closed hI hR tasks pAfter := by
    intro q' mm' hGet' d hd
    rw [hCacheEq] at hGet'
    rw [hCacheEq]
    have ⟨_, hOld⟩ : ∃ mm'', r.persist.cache.get? d.q = some mm'' := by
      rcases cache_insert_cases hI hR tasks hGet' with ⟨rfl, rfl⟩ | ⟨_, hOld⟩
      · exact hMemoDepsInCache d hd
      · exact r.hWF.closed q' mm' hOld d hd
    exact cache_insert_get?_exists hI hR tasks memo hOld
  have hDownClosed : DownClosed hI hR tasks pAfter := by
    intro q' mm' hGet' hNotDirty' d hd
    rw [hCacheEq] at hGet'
    rw [hDirtyEq] at hNotDirty' ⊢
    have hdqNotDirty : d.q ∉ r.persist.dirty := by
      rcases cache_insert_cases hI hR tasks hGet' with ⟨rfl, rfl⟩ | ⟨hne, hOld⟩
      · exact hMemoDepsNotDirty d hd
      · refine r.hWF.downClosed q' mm' hOld (fun h => hNotDirty' ?_) d hd
        exact Array.mem_filter.mpr ⟨h, by simpa using Ne.symm hne⟩
    exact fun hMem => hdqNotDirty (Array.mem_filter.mp hMem).left
  let hWFAfter : WellFormed hI hR tasks ι₀ pAfter :=
    { sound := hSound, complete := hComplete, closed := hClosed, downClosed := hDownClosed }
  {
    persist := pAfter
    value := ⟨r.value, hVal⟩
    hWF := hWFAfter
    hNotDirty := fun hMem => by
      rw [hDirtyEq] at hMem
      exact absurd (Array.mem_filter.mp hMem).right (by simp)
    memo
    hCache := by
      rw [hCacheEq]
      exact DHashMap.get?_insert_self
    hValEq := rfl
    hCacheMono := fun q' mm' h => by
      let ⟨_, h''⟩ := r.hCacheMono q' mm' h
      rw [hCacheEq]
      exact cache_insert_get?_exists hI hR tasks memo h''
    hDirtyAntiMono := fun q' h => by
      rw [hDirtyEq] at h
      have ⟨hMem, _⟩ : q' ∈ r.persist.dirty ∧ _ := Array.mem_filter.mp h
      exact r.hDirtyAntiMono q' hMem
  }

def populateBody
    (q : ℭ.Q)
    (ih : ∀ q', ℭ.rel q' q → ∀ (p : Persist hI hR tasks),
      WellFormed hI hR tasks ι₀ p → PopulateResult hI hR tasks ι₀ q' p)
    (p : Persist hI hR tasks) (hWF : WellFormed hI hR tasks ι₀ p) :
    PopulateResult hI hR tasks ι₀ q p :=
  if hNotDirty : q ∉ p.dirty then
    match hCache : p.cache.get? q with
    | some mm =>
      let valSpec : mm.value = compute tasks ι₀ q :=
        Sound.value hI hR tasks hWF.sound q mm hCache hNotDirty
      { persist := p
        value := ⟨mm.value, valSpec⟩
        hWF
        hNotDirty
        memo := mm
        hCache
        hValEq := rfl
        hCacheMono := fun _ mm' h => ⟨mm', h⟩
        hDirtyAntiMono := fun _ h => h }
    | none => populateRecompute hI hR tasks ι₀ q ih p hWF
  else populateRecompute hI hR tasks ι₀ q ih p hWF

def populate (q : ℭ.Q) (p : Persist hI hR tasks) (hWF : WellFormed hI hR tasks ι₀ p) :
    PopulateResult hI hR tasks ι₀ q p :=
  ℭ.wf.fix (C := fun q' => ∀ p, WellFormed hI hR tasks ι₀ p → PopulateResult hI hR tasks ι₀ q' p)
    (populateBody hI hR tasks ι₀) q p hWF

end

end ShakeStandardRdeps

public def ShakeStandardRdeps
    (ℭ : BuildConfig)
    (J : Type) [Input ℭ J]
    [BEq ℭ.I] [LawfulBEq ℭ.I] [Hashable ℭ.I] [DecidableEq ℭ.I]
    [BEq ℭ.Q] [LawfulBEq ℭ.Q] [Hashable ℭ.Q]
    {H : Type} [DecidableEq H]
    (hI : ∀ i, ℭ.V i ↪ H) (hR : ∀ q, ℭ.R q ↪ H) (tasks : Tasks ℭ) :
    Build ℭ J tasks Id Id where
  σ := { sp : J × ShakeStandardRdeps.Persist hI hR tasks //
           ShakeStandardRdeps.WellFormed hI hR tasks (Input.get sp.fst) sp.snd }
  init j := ⟨(j, .empty hI hR tasks),
    ShakeStandardRdeps.wellFormed_empty hI hR tasks (Input.get j)⟩
  inputs s := Input.get s.val.fst
  set i v := fun ⟨(j, p), hWF⟩ =>
    if heq : hI i (Input.get j i) = hI i v then
      let j' := Input.set j i v
      have hsame : Input.get j i = v := (hI i).injective heq
      have hgeq : Input.get j' = Input.get j := by
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Input.get_set_self]
          exact hsame.symm
        · rw [Input.get_set_other _ _ _ _ hk]
      ((), ⟨(j', p), hgeq ▸ hWF⟩)
    else
      let j' := Input.set j i v
      let p' := ShakeStandardRdeps.invalidate hI hR tasks p i
      have hgeq : Input.get j' = Function.update (Input.get j) i v := by
        funext k
        by_cases hk : k = i
        · subst hk
          rw [Function.update_self, Input.get_set_self]
        · rw [Function.update_of_ne hk, Input.get_set_other _ _ _ _ hk]
      ((), ⟨(j', p'),
        hgeq ▸ ShakeStandardRdeps.wellFormed_invalidate hI hR tasks p (Input.get j) i v hWF⟩)
  build q := fun ⟨(j, p), hWF⟩ =>
    let result := ShakeStandardRdeps.populate hI hR tasks (Input.get j) q p hWF
    (result.value, ⟨(j, result.persist), result.hWF⟩)

end Incremental
