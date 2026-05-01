#include <lean/lean.h>

extern lean_object *lean_st_ref_take(lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
extern uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *l_Except_instMonad(lean_object *);

static lean_object *g_monad_inst = NULL;
static lean_object *g_empty_dhashmap_1024 = NULL;

static void ensure_init(void);

static lean_object *mk_empty_dhashmap(size_t cap) {
  lean_object *nil = lean_box(0);
  lean_object *cap_nat = lean_usize_to_nat(cap);
  lean_object *buckets = lean_mk_array(cap_nat, nil);
  lean_object *m = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(m, 0, lean_unsigned_to_nat(0u));
  lean_ctor_set(m, 1, buckets);
  return m;
}

/* Salsa.Memo: ctor(0, 5, 8)
 *   structure Salsa.Memo (q : Q) where
 *     value : R q            -- field 0
 *     changedAt : Nat        -- field 1
 *     verifiedAt : Nat       -- field 2
 *     deps : Array Q         -- field 3
 *     inputDeps : Array I    -- field 4
 *     hash : UInt64          -- scalar at offset 5*ptr */
static lean_object *mk_memo(lean_object *value, lean_object *changedAt,
    lean_object *verifiedAt, lean_object *deps, lean_object *inputDeps,
    uint64_t hash) {
  lean_object *m = lean_alloc_ctor(0, 5, sizeof(uint64_t));
  lean_ctor_set(m, 0, value);
  lean_ctor_set(m, 1, changedAt);
  lean_ctor_set(m, 2, verifiedAt);
  lean_ctor_set(m, 3, deps);
  lean_ctor_set(m, 4, inputDeps);
  lean_ctor_set_uint64(m, sizeof(void *) * 5, hash);
  return m;
}

/* Salsa.Store: ctor(0, 4, 0)
 *   structure Salsa.Store (J : Type) where
 *     inputs : J               -- field 0
 *     revision : Nat           -- field 1
 *     memos : DHashMap Q Memo  -- field 2
 *     inputRevisions : HashMap I Nat  -- field 3 */

static lean_object *salsa_fetch(lean_object *beqI, lean_object *hashI,
    lean_object *beqQ, lean_object *hashQ, lean_object *hashR,
    lean_object *input_fn, lean_object *tasks, lean_object *store,
    lean_object *memos_ref, lean_object *stack_ref, lean_object *key);

/* input' (i : I) : Except BuildError (V i) := do
 *   inputDepsRef.modify (·.push i)
 *   pure (Input.get store.inputs i) */
static lean_object *wrapped_input_cb(
    lean_object *input_deps_ref, lean_object *input_fn, lean_object *i) {
  lean_object *old = lean_st_ref_take(input_deps_ref);
  lean_inc(i);
  lean_object *new_arr = lean_array_push(old, i);
  lean_st_ref_set(input_deps_ref, new_arr);
  lean_dec(input_deps_ref);

  lean_object *v = lean_apply_1(input_fn, i);

  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

/* fetch' (q : Q) : Except BuildError (R q) := do
 *   let v ← fetch q
 *   depsRef.modify (·.push q)
 *   pure v */
static lean_object *salsa_fetch_cb(lean_object *beqI, lean_object *hashI,
    lean_object *beqQ, lean_object *hashQ, lean_object *hashR,
    lean_object *input_fn, lean_object *tasks, lean_object *store,
    lean_object *memos_ref, lean_object *stack_ref, lean_object *deps_ref,
    lean_object *key, lean_object *_proof) {
  (void)_proof;
  lean_object *value = salsa_fetch(beqI, hashI, beqQ, hashQ, hashR, input_fn,
      tasks, store, memos_ref, stack_ref, key);

  lean_object *ret;
  if (lean_obj_tag(value) == 0) {
    lean_dec(key);
    ret = value;
  } else {
    lean_object *v = lean_ctor_get(value, 0);
    lean_inc(v);
    lean_dec_ref(value);

    lean_object *old = lean_st_ref_take(deps_ref);
    lean_inc(key);
    lean_object *new_arr = lean_array_push(old, key);
    lean_st_ref_set(deps_ref, new_arr);

    lean_dec(key);
    ret = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(ret, 0, v);
  }

  lean_dec_ref(beqI);
  lean_dec_ref(hashI);
  lean_dec_ref(beqQ);
  lean_dec_ref(hashQ);
  lean_dec_ref(hashR);
  lean_dec_ref(input_fn);
  lean_dec_ref(tasks);
  lean_dec_ref(store);
  lean_dec(memos_ref);
  lean_dec(stack_ref);
  lean_dec(deps_ref);

  return ret;
}

/* verifyInputDeps (memo.inputDeps : Array I) : Bool :=
 *   memo.inputDeps.all fun i =>
 *     store.inputRevisions.getD i 0 ≤ memo.verifiedAt */
static int verify_input_revs(lean_object *beqI, lean_object *hashI,
    lean_object *input_revisions, lean_object *verified_at,
    lean_object *input_deps) {
  size_t n = lean_array_size(input_deps);
  for (size_t i = 0; i < n; i++) {
    lean_object *key = lean_array_uget(input_deps, i);
    lean_inc(key);
    lean_inc_ref(beqI);
    lean_inc_ref(hashI);
    lean_object *zero = lean_unsigned_to_nat(0u);
    lean_object *rev = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(
        beqI, hashI, input_revisions, key, zero);
    if (!lean_nat_dec_le(rev, verified_at)) {
      lean_dec(rev);
      return 0;
    }
    lean_dec(rev);
  }
  return 1;
}

/* verifyDeps (memo.deps : Array Q) : Except BuildError Bool := do
 *   for dep in memo.deps do
 *     let _ ← fetch dep
 *     match (← memos.get).get? dep with
 *     | some depMemo =>
 *       if depMemo.changedAt > memo.verifiedAt then
 *         clean := false; break
 *     | none => clean := false; break
 *   return clean
 *
 * Returns: 1 = clean, 0 = dirty, -1 = cycle */
static int verify_deps(lean_object *beqI, lean_object *hashI, lean_object *beqQ,
    lean_object *hashQ, lean_object *hashR, lean_object *input_fn,
    lean_object *tasks, lean_object *store, lean_object *memos_ref,
    lean_object *stack_ref, lean_object *verified_at, lean_object *deps) {
  size_t n = lean_array_size(deps);
  for (size_t i = 0; i < n; i++) {
    lean_object *dep = lean_array_uget(deps, i);

    /* salsa_fetch borrows dep */
    lean_object *result = salsa_fetch(beqI, hashI, beqQ, hashQ, hashR, input_fn,
        tasks, store, memos_ref, stack_ref, dep);
    if (lean_obj_tag(result) == 0) {
      lean_dec_ref(result);
      return -1;
    }
    lean_dec_ref(result);

    /* match (← memos.get).get? dep with */
    lean_object *memos = lean_st_ref_get(memos_ref);
    lean_inc(dep);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *dep_memo_opt =
        l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
            beqQ, hashQ, memos, dep);
    lean_dec(memos);

    if (lean_is_scalar(dep_memo_opt)) {
      lean_dec(dep_memo_opt);
      return 0;
    }

    lean_object *dep_memo = lean_ctor_get(dep_memo_opt, 0);
    lean_object *changed_at = lean_ctor_get(dep_memo, 1);
    uint8_t changed = lean_nat_dec_lt(verified_at, changed_at);
    lean_dec_ref(dep_memo_opt);

    if (changed)
      return 0;
  }
  return 1;
}

/* fetch (q : Q) : Except BuildError (R q)
 *
 * borrow all parameters
 * Returns Except: ctor(0) = error, ctor(1) = ok */
static lean_object *salsa_fetch(lean_object *beqI, lean_object *hashI,
    lean_object *beqQ, lean_object *hashQ, lean_object *hashR,
    lean_object *input_fn, lean_object *tasks, lean_object *store,
    lean_object *memos_ref, lean_object *stack_ref, lean_object *key) {
  lean_object *revision = lean_ctor_get(store, 1);
  lean_object *input_revisions = lean_ctor_get(store, 3);

  /* let memo? := (← memos.get).get? q */
  lean_object *memos = lean_st_ref_get(memos_ref);
  lean_inc(key);
  lean_inc_ref(beqQ);
  lean_inc_ref(hashQ);
  lean_object *memo_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
      beqQ, hashQ, memos, key);
  lean_dec(memos);

  /* if let some memo := memo? then
   *   if memo.verifiedAt == store.revision then
   *     return memo.value */
  if (!lean_is_scalar(memo_opt)) {
    lean_object *memo = lean_ctor_get(memo_opt, 0);
    lean_object *verified_at = lean_ctor_get(memo, 2);
    if (lean_nat_dec_eq(verified_at, revision)) {
      lean_object *value = lean_ctor_get(memo, 0);
      lean_inc(value);
      lean_dec_ref(memo_opt);
      lean_object *r = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(r, 0, value);
      return r;
    }
  }

  /* let stk ← stack.get
   * if stk.contains q then throw .cycle */
  {
    lean_object *stack = lean_st_ref_get(stack_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    uint8_t on_stack = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
        beqQ, hashQ, stack, key);
    lean_dec(stack);
    if (on_stack) {
      lean_dec_ref(memo_opt);
      lean_object *r = lean_alloc_ctor(0, 1, 0);
      lean_ctor_set(r, 0, lean_box(0));
      return r;
    }
  }

  /* stack.set (stk.insert q) */
  {
    lean_object *old_stack = lean_st_ref_take(stack_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *new_stack = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beqQ, hashQ, old_stack, key, lean_box(0));
    lean_st_ref_set(stack_ref, new_stack);
  }

  int had_memo = 0;
  uint64_t old_hash = 0;
  lean_object *old_changedAt = NULL;

  /* if let some memo := memo? then */
  if (!lean_is_scalar(memo_opt)) {
    lean_object *memo = lean_ctor_get(memo_opt, 0);
    lean_inc(memo);
    lean_dec_ref(memo_opt);

    lean_object *verified_at = lean_ctor_get(memo, 2);
    lean_object *memo_deps = lean_ctor_get(memo, 3);
    lean_object *memo_input_deps = lean_ctor_get(memo, 4);

    int input_clean = verify_input_revs(
        beqI, hashI, input_revisions, verified_at, memo_input_deps);

    int clean = input_clean;
    if (clean) {
      int dep_result = verify_deps(beqI, hashI, beqQ, hashQ, hashR, input_fn,
          tasks, store, memos_ref, stack_ref, verified_at, memo_deps);
      if (dep_result == -1) {
        lean_dec(memo);
        lean_object *r = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(r, 0, lean_box(0));
        return r;
      }
      clean = dep_result;
    }

    if (clean) {
      lean_object *value = lean_ctor_get(memo, 0);
      lean_inc(value);
      lean_inc(value);
      lean_object *changedAt = lean_ctor_get(memo, 1);
      lean_inc(changedAt);
      lean_inc(revision);
      lean_inc(memo_deps);
      lean_inc(memo_input_deps);
      uint64_t h = lean_ctor_get_uint64(memo, sizeof(void *) * 5);
      lean_dec(memo);

      lean_object *new_memo =
          mk_memo(value, changedAt, revision, memo_deps, memo_input_deps, h);

      lean_object *old_memos = lean_st_ref_take(memos_ref);
      lean_inc(key);
      lean_inc_ref(beqQ);
      lean_inc_ref(hashQ);
      lean_object *new_memos =
          l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
              beqQ, hashQ, old_memos, key, new_memo);
      lean_st_ref_set(memos_ref, new_memos);

      lean_object *r = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(r, 0, value);
      return r;
    }

    had_memo = 1;
    old_hash = lean_ctor_get_uint64(memo, sizeof(void *) * 5);
    old_changedAt = lean_ctor_get(memo, 1);
    lean_inc(old_changedAt);
    lean_dec(memo);
  } else {
    lean_dec(memo_opt);
  }

  /* recompute */
  {
    lean_object *empty_arr =
        lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(0u));
    lean_object *deps_ref = lean_st_mk_ref(empty_arr);

    lean_object *empty_arr2 =
        lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(0u));
    lean_object *input_deps_ref = lean_st_mk_ref(empty_arr2);

    lean_inc(input_deps_ref);
    lean_inc_ref(input_fn);
    lean_object *input_closure =
        lean_alloc_closure((void *)wrapped_input_cb, 3, 2);
    lean_closure_set(input_closure, 0, input_deps_ref);
    lean_closure_set(input_closure, 1, input_fn);

    lean_inc_ref(beqI);
    lean_inc_ref(hashI);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_inc_ref(hashR);
    lean_inc_ref(input_fn);
    lean_inc_ref(tasks);
    lean_inc_ref(store);
    lean_inc(memos_ref);
    lean_inc(stack_ref);
    lean_inc(deps_ref);
    lean_object *fetch_closure =
        lean_alloc_closure((void *)salsa_fetch_cb, 13, 11);
    lean_closure_set(fetch_closure, 0, beqI);
    lean_closure_set(fetch_closure, 1, hashI);
    lean_closure_set(fetch_closure, 2, beqQ);
    lean_closure_set(fetch_closure, 3, hashQ);
    lean_closure_set(fetch_closure, 4, hashR);
    lean_closure_set(fetch_closure, 5, input_fn);
    lean_closure_set(fetch_closure, 6, tasks);
    lean_closure_set(fetch_closure, 7, store);
    lean_closure_set(fetch_closure, 8, memos_ref);
    lean_closure_set(fetch_closure, 9, stack_ref);
    lean_closure_set(fetch_closure, 10, deps_ref);

    lean_inc(key);
    lean_inc_ref(tasks);
    lean_inc_ref(input_fn);
    lean_object *task = lean_apply_2(tasks, input_fn, key);
    lean_inc(task);
    lean_inc(g_monad_inst);
    lean_object *result = lean_apply_4(
        task, lean_box(0), g_monad_inst, input_closure, fetch_closure);
    lean_dec(task);

    if (lean_obj_tag(result) == 0) {
      if (had_memo)
        lean_dec(old_changedAt);
      lean_dec(deps_ref);
      lean_dec(input_deps_ref);
      return result;
    }

    lean_object *value = lean_ctor_get(result, 0);
    lean_inc(value);
    lean_dec_ref(result);

    lean_inc(key);
    lean_inc(value);
    lean_inc_ref(hashR);
    lean_object *h_box = lean_apply_2(hashR, key, value);
    uint64_t h = lean_unbox_uint64(h_box);
    lean_dec_ref(h_box);

    lean_object *changedAt;
    if (had_memo && h == old_hash) {
      changedAt = old_changedAt;
    } else {
      if (had_memo)
        lean_dec(old_changedAt);
      lean_inc(revision);
      changedAt = revision;
    }

    lean_object *final_deps = lean_st_ref_get(deps_ref);
    lean_dec(deps_ref);
    lean_object *final_input_deps = lean_st_ref_get(input_deps_ref);
    lean_dec(input_deps_ref);

    lean_inc(revision);
    lean_inc(value);
    lean_object *new_memo =
        mk_memo(value, changedAt, revision, final_deps, final_input_deps, h);

    lean_object *old_memos = lean_st_ref_take(memos_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *new_memos = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beqQ, hashQ, old_memos, key, new_memo);
    lean_st_ref_set(memos_ref, new_memos);

    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, value);
    return r;
  }
}

LEAN_EXPORT lean_object *lean_salsa_build(lean_object *_config,
    lean_object *beqI, lean_object *hashI, lean_object *beqQ,
    lean_object *hashQ, lean_object *hashR, lean_object *inputInst,
    lean_object *tasks, lean_object *target, lean_object *store) {
  (void)_config;
  lean_object *inputs = lean_ctor_get(store, 0);
  lean_inc(inputs);
  lean_inc(inputs);
  lean_object *revision = lean_ctor_get(store, 1);
  lean_inc(revision);
  lean_object *memos = lean_ctor_get(store, 2);
  lean_inc(memos);
  lean_object *input_revisions = lean_ctor_get(store, 3);
  lean_inc(input_revisions);

  lean_object *get_method = lean_ctor_get(inputInst, 0);
  lean_inc(get_method);
  lean_dec_ref(inputInst);
  lean_object *input_fn = lean_apply_1(get_method, inputs);

  ensure_init();

  lean_object *memos_ref = lean_st_mk_ref(memos);

  lean_inc(g_empty_dhashmap_1024);
  lean_object *stack_ref = lean_st_mk_ref(g_empty_dhashmap_1024);

  /* salsa_fetch borrows all params including target */
  lean_object *result = salsa_fetch(beqI, hashI, beqQ, hashQ, hashR, input_fn,
      tasks, store, memos_ref, stack_ref, target);

  lean_object *ret;
  lean_object *final_memos = lean_st_ref_get(memos_ref);
  lean_object *new_store = lean_alloc_ctor(0, 4, 0);
  lean_ctor_set(new_store, 0, inputs);
  lean_ctor_set(new_store, 1, revision);
  lean_ctor_set(new_store, 2, final_memos);
  lean_ctor_set(new_store, 3, input_revisions);

  if (lean_obj_tag(result) == 1) {
    lean_object *value = lean_ctor_get(result, 0);
    lean_inc(value);
    lean_dec_ref(result);
    ret = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(ret, 0, value);
    lean_ctor_set(ret, 1, new_store);
  } else {
    lean_dec_ref(result);
    ret = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(ret, 0, lean_box(0));
    lean_ctor_set(ret, 1, new_store);
  }

  lean_dec(memos_ref);
  lean_dec(stack_ref);

  lean_dec_ref(beqI);
  lean_dec_ref(hashI);
  lean_dec_ref(beqQ);
  lean_dec_ref(hashQ);
  lean_dec_ref(hashR);
  lean_dec_ref(input_fn);
  lean_dec_ref(tasks);
  lean_dec(target);
  lean_dec_ref(store);

  return ret;
}

static void ensure_init(void) {
  if (g_monad_inst == NULL) {
    g_monad_inst = l_Except_instMonad(lean_box(0));
    lean_mark_persistent(g_monad_inst);
    g_empty_dhashmap_1024 = mk_empty_dhashmap(1024);
    lean_mark_persistent(g_empty_dhashmap_1024);
  }
}
