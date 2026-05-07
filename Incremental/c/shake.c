#include <lean/lean.h>

extern lean_object *lean_st_ref_take(lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
extern uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern uint8_t l_Array_contains___redArg(
    lean_object *, lean_object *, lean_object *);
extern lean_object *l_Except_instMonad(lean_object *);

static lean_object *g_monad_inst = NULL;
static lean_object *g_empty_dhashmap_2048 = NULL;
static lean_object *g_empty_dhashmap_128 = NULL;

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

/* Memo: ctor(0, 3, 8) — value, deps, inputDeps, hash
 *   structure Shake.Memo (q : Q) where
 *     value : R q
 *     deps : HashMap Q UInt64
 *     inputDeps : HashMap I UInt64
 *     hash : UInt64 := hash value */
static lean_object *mk_memo(lean_object *value, lean_object *deps,
    lean_object *input_deps, uint64_t hash) {
  lean_object *m = lean_alloc_ctor(0, 3, sizeof(uint64_t));
  lean_ctor_set(m, 0, value);
  lean_ctor_set(m, 1, deps);
  lean_ctor_set(m, 2, input_deps);
  lean_ctor_set_uint64(m, sizeof(void *) * 3, hash);
  return m;
}

/* Internal convention: NULL = BuildError.cycle, non-NULL = value.
 * Converted to Except only at the lean_shake_build entry point.
 * NULL is safe because no lean_object* (boxed scalar or heap pointer) is ever
 * 0. */
#define CYCLE NULL
#define IS_CYCLE(r) ((r) == CYCLE)

static lean_object *shake_fetch(lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *beqQ, lean_object *hashQ,
    lean_object *hashR, lean_object *input_fn, lean_object *tasks,
    lean_object *cache_ref, lean_object *started_ref, lean_object *stack_ref,
    lean_object *key);

/* input' (i : I) : EST BuildError σ (V i) := do
 *   let v := Input.get store.inputs i
 *   if !(← inputDeps.get).contains i then
 *     inputDeps.modify (·.insert i (hash v))
 *   pure v
 *
 * Returns Except because it's passed to the task as a closure. */
static lean_object *wrapped_input_cb(lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *input_fn, lean_object *input_deps_ref,
    lean_object *i) {
  lean_inc(i);
  lean_inc_ref(input_fn);
  lean_object *v = lean_apply_1(input_fn, i);

  lean_object *ds = lean_st_ref_get(input_deps_ref);
  lean_inc(i);
  lean_inc_ref(beqI);
  lean_inc_ref(hashI);
  uint8_t has =
      l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(beqI, hashI, ds, i);
  lean_dec(ds);

  if (!has) {
    lean_inc(i);
    lean_inc(v);
    lean_inc_ref(hashV);
    lean_object *h_box = lean_apply_2(hashV, i, v);

    lean_object *old_ds = lean_st_ref_take(input_deps_ref);
    lean_inc(i);
    lean_inc_ref(beqI);
    lean_inc_ref(hashI);
    lean_object *new_ds = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beqI, hashI, old_ds, i, h_box);
    lean_st_ref_set(input_deps_ref, new_ds);
  }

  lean_dec(i);
  /* Except.ok v */
  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, v);
  return r;
}

/* fetch' (q : Q) : EST BuildError σ (R q) := do
 *   let v ← fetch q
 *   if !(← deps.get).contains q then
 *     let h := match (← started.get).get? q with
 *       | some m => m.hash
 *       | none => hash v
 *     deps.modify (·.insert q h)
 *   pure v
 *
 * Returns Except because it's passed to the task as a closure. */
static lean_object *shake_fetch_cb(lean_object *beqQ, lean_object *hashQ,
    lean_object *hashR, lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *input_fn, lean_object *tasks,
    lean_object *cache_ref, lean_object *started_ref, lean_object *stack_ref,
    lean_object *deps_ref, lean_object *key, lean_object *_proof) {
  (void)_proof;
  lean_object *value = shake_fetch(beqI, hashI, hashV, beqQ, hashQ, hashR,
      input_fn, tasks, cache_ref, started_ref, stack_ref, key);
  if (IS_CYCLE(value)) {
    /* Except.error BuildError.cycle */
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, lean_box(0));
    return r;
  }

  lean_object *ds = lean_st_ref_get(deps_ref);
  lean_inc(key);
  lean_inc_ref(beqQ);
  lean_inc_ref(hashQ);
  uint8_t has =
      l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(beqQ, hashQ, ds, key);
  lean_dec(ds);

  if (!has) {
    uint64_t h;
    lean_object *started = lean_st_ref_get(started_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *memo_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        beqQ, hashQ, started, key);
    lean_dec(started);

    if (!lean_is_scalar(memo_opt)) {
      /* some m => m.hash */
      lean_object *memo = lean_ctor_get(memo_opt, 0);
      h = lean_ctor_get_uint64(memo, sizeof(void *) * 3);
      lean_dec_ref(memo_opt);
    } else {
      /* none => hash v */
      lean_dec(memo_opt);
      lean_inc(key);
      lean_inc(value);
      lean_inc_ref(hashR);
      lean_object *h_box = lean_apply_2(hashR, key, value);
      h = lean_unbox_uint64(h_box);
      lean_dec_ref(h_box);
    }

    lean_object *old_ds = lean_st_ref_take(deps_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *new_ds = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beqQ, hashQ, old_ds, key, lean_box_uint64(h));
    lean_st_ref_set(deps_ref, new_ds);
  }

  lean_dec(key);
  /* Except.ok value */
  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, value);
  return r;
}

/* verifyDeps (deps : HashMap Q UInt64) : EST BuildError σ Bool := do
 *   for (depKey, oldHash) in deps do
 *     let _ ← fetch depKey
 *     let h := match (← started.get).get? depKey with
 *       | some m => m.hash
 *       | none => 0
 *     if h != oldHash then return false
 *   return true
 *
 * Returns: 0 = all deps valid, 1 = hash mismatch, 2 = error (cycle).  */
static int verify_deps(lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *beqQ, lean_object *hashQ,
    lean_object *hashR, lean_object *input_fn, lean_object *tasks,
    lean_object *cache_ref, lean_object *started_ref, lean_object *stack_ref,
    lean_object *deps) {
  lean_object *buckets = lean_ctor_get(deps, 1);
  size_t n = lean_array_size(buckets);

  for (size_t i = 0; i < n; i++) {
    lean_object *node = lean_array_uget(buckets, i);
    while (!lean_is_scalar(node)) {
      lean_object *dep_key = lean_ctor_get(node, 0);
      lean_object *old_hash_box = lean_ctor_get(node, 1);
      uint64_t old_hash = lean_unbox_uint64(old_hash_box);

      /* let _ ← fetch depKey */
      lean_object *value = shake_fetch(beqI, hashI, hashV, beqQ, hashQ, hashR,
          input_fn, tasks, cache_ref, started_ref, stack_ref, dep_key);
      if (IS_CYCLE(value))
        return 2;
      lean_dec(value);

      /* let h := match (← started.get).get? depKey with ... */
      lean_object *started = lean_st_ref_get(started_ref);
      lean_inc(dep_key);
      lean_inc_ref(beqQ);
      lean_inc_ref(hashQ);
      lean_object *memo_opt =
          l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
              beqQ, hashQ, started, dep_key);
      lean_dec(started);

      uint64_t cur_hash;
      if (!lean_is_scalar(memo_opt)) {
        lean_object *memo = lean_ctor_get(memo_opt, 0);
        cur_hash = lean_ctor_get_uint64(memo, sizeof(void *) * 3);
      } else {
        cur_hash = 0;
      }
      lean_dec_ref(memo_opt);

      /* if h != oldHash then return false */
      if (cur_hash != old_hash)
        return 1;

      node = lean_ctor_get(node, 2);
    }
  }
  return 0;
}

/* verifyInputDeps (inputDeps : HashMap I UInt64) : Bool :=
 *   inputDeps.all fun i oldHash =>
 *     hash (Input.get store.inputs i) == oldHash */
static int verify_input_deps(
    lean_object *hashV, lean_object *input_fn, lean_object *input_deps) {
  lean_object *buckets = lean_ctor_get(input_deps, 1);
  size_t n = lean_array_size(buckets);

  for (size_t i = 0; i < n; i++) {
    lean_object *node = lean_array_uget(buckets, i);
    while (!lean_is_scalar(node)) {
      lean_object *key = lean_ctor_get(node, 0);
      lean_object *old_hash_box = lean_ctor_get(node, 1);
      uint64_t old_hash = lean_unbox_uint64(old_hash_box);

      lean_inc(key);
      lean_inc_ref(input_fn);
      lean_object *cur_v = lean_apply_1(input_fn, key);

      lean_inc(key);
      lean_inc(cur_v);
      lean_inc_ref(hashV);
      lean_object *cur_hash_box = lean_apply_2(hashV, key, cur_v);
      uint64_t cur_hash = lean_unbox_uint64(cur_hash_box);
      lean_dec_ref(cur_hash_box);
      lean_dec(cur_v);

      if (cur_hash != old_hash)
        return 1;

      node = lean_ctor_get(node, 2);
    }
  }
  return 0;
}

/* recompute : EST BuildError σ (R q) := do
 *   let value ← tasks q (EST BuildError σ) input' fetch'
 *   let m : Shake.Memo I Q R q := { value, deps := ← deps.get, inputDeps := ←
 * inputDeps.get } started.modify (·.insert q m) memos.modify (·.insert q m)
 *   return value
 *
 * Runs the task, records the memo. Returns value or NULL on error. */
static lean_object *run_task(lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *beqQ, lean_object *hashQ,
    lean_object *hashR, lean_object *input_fn, lean_object *tasks,
    lean_object *cache_ref, lean_object *started_ref, lean_object *stack_ref,
    lean_object *task, lean_object *key, lean_object **out_deps,
    lean_object **out_input_deps) {
  lean_inc(g_empty_dhashmap_128);
  lean_object *deps_ref = lean_st_mk_ref(g_empty_dhashmap_128);

  lean_inc(g_empty_dhashmap_128);
  lean_object *input_deps_ref = lean_st_mk_ref(g_empty_dhashmap_128);

  /* Build input' closure */
  lean_inc_ref(beqI);
  lean_inc_ref(hashI);
  lean_inc_ref(hashV);
  lean_inc_ref(input_fn);
  lean_inc(input_deps_ref);
  lean_object *input_closure =
      lean_alloc_closure((void *)wrapped_input_cb, 6, 5);
  lean_closure_set(input_closure, 0, beqI);
  lean_closure_set(input_closure, 1, hashI);
  lean_closure_set(input_closure, 2, hashV);
  lean_closure_set(input_closure, 3, input_fn);
  lean_closure_set(input_closure, 4, input_deps_ref);

  /* Build fetch' closure */
  lean_inc_ref(beqQ);
  lean_inc_ref(hashQ);
  lean_inc_ref(hashR);
  lean_inc_ref(beqI);
  lean_inc_ref(hashI);
  lean_inc_ref(hashV);
  lean_inc_ref(input_fn);
  lean_inc_ref(tasks);
  lean_inc(cache_ref);
  lean_inc(started_ref);
  lean_inc(stack_ref);
  lean_inc(deps_ref);
  lean_object *fetch_closure =
      lean_alloc_closure((void *)shake_fetch_cb, 14, 12);
  lean_closure_set(fetch_closure, 0, beqQ);
  lean_closure_set(fetch_closure, 1, hashQ);
  lean_closure_set(fetch_closure, 2, hashR);
  lean_closure_set(fetch_closure, 3, beqI);
  lean_closure_set(fetch_closure, 4, hashI);
  lean_closure_set(fetch_closure, 5, hashV);
  lean_closure_set(fetch_closure, 6, input_fn);
  lean_closure_set(fetch_closure, 7, tasks);
  lean_closure_set(fetch_closure, 8, cache_ref);
  lean_closure_set(fetch_closure, 9, started_ref);
  lean_closure_set(fetch_closure, 10, stack_ref);
  lean_closure_set(fetch_closure, 11, deps_ref);

  /* let value ← tasks q (Except BuildError) input' fetch' */
  lean_inc(task);
  lean_inc(g_monad_inst);
  lean_object *result = lean_apply_4(
      task, lean_box(0), g_monad_inst, input_closure, fetch_closure);

  if (lean_obj_tag(result) == 0) {
    /* Except.error — task failed */
    lean_dec_ref(result);
    lean_dec(deps_ref);
    lean_dec(input_deps_ref);
    return CYCLE;
  }

  lean_object *value = lean_ctor_get(result, 0);
  lean_inc(value);
  lean_dec_ref(result);

  *out_deps = lean_st_ref_get(deps_ref);
  lean_dec(deps_ref);

  *out_input_deps = lean_st_ref_get(input_deps_ref);
  lean_dec(input_deps_ref);

  return value;
}

/* fetch (q : Q) : EST BuildError σ (R q)
 *
 * Returns the value directly, or NULL on error (cycle). */
static lean_object *shake_fetch(lean_object *beqI, lean_object *hashI,
    lean_object *hashV, lean_object *beqQ, lean_object *hashQ,
    lean_object *hashR, lean_object *input_fn, lean_object *tasks,
    lean_object *cache_ref, lean_object *started_ref, lean_object *stack_ref,
    lean_object *key) {

  /* if let some m := (← started.get).get? q then
   *   return m.value */
  {
    lean_object *started = lean_st_ref_get(started_ref);
    lean_inc(key);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *memo_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        beqQ, hashQ, started, key);
    lean_dec(started);
    if (!lean_is_scalar(memo_opt)) {
      lean_object *memo = lean_ctor_get(memo_opt, 0);
      lean_object *value = lean_ctor_get(memo, 0);
      lean_inc(value);
      lean_dec_ref(memo_opt);
      return value;
    }
    lean_dec(memo_opt);
  }

  /* if stk.contains q then throw .cycle */
  {
    lean_object *stack = lean_st_ref_get(stack_ref);
    lean_inc(key);
    lean_inc(stack);
    lean_inc_ref(beqQ);
    uint8_t on_stack = l_Array_contains___redArg(beqQ, stack, key);
    lean_dec(stack);
    if (on_stack)
      return CYCLE;
  }

  /* stack.set (stk.push q) */
  {
    lean_object *stack = lean_st_ref_take(stack_ref);
    lean_inc(key);
    stack = lean_array_push(stack, key);
    lean_st_ref_set(stack_ref, stack);
  }

  lean_object *value;

  /* match (← memos.get).get? q with ... */
  lean_object *cache = lean_st_ref_get(cache_ref);
  lean_inc(key);
  lean_inc_ref(beqQ);
  lean_inc_ref(hashQ);
  lean_object *cached_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
      beqQ, hashQ, cache, key);
  lean_dec(cache);

  if (lean_is_scalar(cached_opt)) {
    /* | none => recompute */
    lean_dec(cached_opt);
    goto recompute;
  } else {
    /* | some m => ... */
    lean_object *cached_memo = lean_ctor_get(cached_opt, 0);
    lean_inc(cached_memo);
    lean_dec_ref(cached_opt);

    /* if verifyInputDeps m.inputDeps && ... */
    lean_object *cached_input_deps = lean_ctor_get(cached_memo, 2);
    if (verify_input_deps(hashV, input_fn, cached_input_deps)) {
      lean_dec(cached_memo);
      goto recompute;
    }

    /* ... (← verifyDeps m.deps) then */
    lean_object *cached_deps = lean_ctor_get(cached_memo, 1);
    int vr = verify_deps(beqI, hashI, hashV, beqQ, hashQ, hashR, input_fn,
        tasks, cache_ref, started_ref, stack_ref, cached_deps);

    if (vr == 2) {
      /* error from verify_deps */
      lean_dec(cached_memo);
      value = CYCLE;
    } else if (vr == 0) {
      /* started.modify (·.insert q m)
       * pure m.value */
      lean_object *old_started = lean_st_ref_take(started_ref);
      lean_inc(key);
      lean_inc(cached_memo);
      lean_inc_ref(beqQ);
      lean_inc_ref(hashQ);
      lean_object *new_started =
          l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
              beqQ, hashQ, old_started, key, cached_memo);
      lean_st_ref_set(started_ref, new_started);

      value = lean_ctor_get(cached_memo, 0);
      lean_inc(value);
      lean_dec(cached_memo);
    } else {
      /* else recompute */
      lean_dec(cached_memo);
      goto recompute;
    }
    goto done;
  }

recompute:;
  /* let value ← tasks q ... input' fetch'
   * let m := { value, deps, inputDeps }
   * started.modify (·.insert q m)
   * memos.modify (·.insert q m) */
  {
    lean_inc(key);
    lean_inc_ref(tasks);
    lean_object *task = lean_apply_1(tasks, key);

    lean_object *deps, *input_deps;
    value = run_task(beqI, hashI, hashV, beqQ, hashQ, hashR, input_fn, tasks,
        cache_ref, started_ref, stack_ref, task, key, &deps, &input_deps);
    lean_dec(task);

    if (IS_CYCLE(value))
      goto done;

    lean_inc(key);
    lean_inc(value);
    lean_inc_ref(hashR);
    lean_object *h_box = lean_apply_2(hashR, key, value);
    uint64_t h = lean_unbox_uint64(h_box);
    lean_dec_ref(h_box);

    lean_inc(value);
    lean_inc(deps);
    lean_inc(input_deps);
    lean_object *memo = mk_memo(value, deps, input_deps, h);

    lean_object *old_started = lean_st_ref_take(started_ref);
    lean_inc(key);
    lean_inc(memo);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *new_started =
        l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            beqQ, hashQ, old_started, key, memo);
    lean_st_ref_set(started_ref, new_started);

    lean_object *old_cache = lean_st_ref_take(cache_ref);
    lean_inc(key);
    lean_inc(memo);
    lean_inc_ref(beqQ);
    lean_inc_ref(hashQ);
    lean_object *new_cache = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beqQ, hashQ, old_cache, key, memo);
    lean_st_ref_set(cache_ref, new_cache);

    lean_dec(memo);
  }

done:
  /* stack.modify Array.pop */
  {
    lean_object *stack = lean_st_ref_take(stack_ref);
    stack = lean_array_pop(stack);
    lean_st_ref_set(stack_ref, stack);
  }

  return value;
}

/* build tasks q := fun store => ...
 *   return (← fetch q, ⟨store.inputs, ← memos.get⟩) */
LEAN_EXPORT lean_object *lean_shake_build(lean_object *_config,
    lean_object *beqI, lean_object *hashI, lean_object *hashV,
    lean_object *beqQ, lean_object *hashQ, lean_object *hashR,
    lean_object *inputInst, lean_object *tasks, lean_object *target,
    lean_object *store) {
  (void)_config;
  /* let inputs := store.inputs */
  lean_object *inputs = lean_ctor_get(store, 0);
  lean_inc(inputs);
  lean_inc(inputs);
  lean_object *cache = lean_ctor_get(store, 1);
  lean_inc(cache);
  lean_dec_ref(store);

  /* Input.get store.inputs (partially applied) */
  lean_object *get_method = lean_ctor_get(inputInst, 0);
  lean_inc(get_method);
  lean_dec_ref(inputInst);
  lean_object *input_fn = lean_apply_1(get_method, inputs);

  ensure_init();

  /* let memos ← ST.mkRef store.memos
   * let started ← ST.mkRef (DHashMap.emptyWithCapacity 1024)
   * let stack ← ST.mkRef #[] */
  lean_object *cache_ref = lean_st_mk_ref(cache);

  lean_inc(g_empty_dhashmap_2048);
  lean_object *started_ref = lean_st_mk_ref(g_empty_dhashmap_2048);

  lean_object *empty_arr =
      lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(0u));
  lean_object *stack_ref = lean_st_mk_ref(empty_arr);

  /* ← fetch q */
  lean_object *value = shake_fetch(beqI, hashI, hashV, beqQ, hashQ, hashR,
      input_fn, tasks, cache_ref, started_ref, stack_ref, target);

  lean_object *result;
  if (!IS_CYCLE(value)) {
    lean_object *final_cache = lean_st_ref_get(cache_ref);
    lean_object *new_store = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(new_store, 0, inputs);
    lean_ctor_set(new_store, 1, final_cache);
    result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, value);
    lean_ctor_set(result, 1, new_store);
  } else {
    lean_object *final_cache = lean_st_ref_get(cache_ref);
    lean_object *new_store = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(new_store, 0, inputs);
    lean_ctor_set(new_store, 1, final_cache);
    result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_box(0));
    lean_ctor_set(result, 1, new_store);
  }

  lean_dec(cache_ref);
  lean_dec(started_ref);
  lean_dec(stack_ref);

  lean_dec_ref(beqI);
  lean_dec_ref(hashI);
  lean_dec_ref(hashV);
  lean_dec_ref(beqQ);
  lean_dec_ref(hashQ);
  lean_dec_ref(hashR);
  lean_dec_ref(input_fn);
  lean_dec_ref(tasks);
  lean_dec(target);

  return result;
}

static void ensure_init(void) {
  if (g_monad_inst == NULL) {
    g_monad_inst = l_Except_instMonad(lean_box(0));
    lean_mark_persistent(g_monad_inst);
    g_empty_dhashmap_2048 = mk_empty_dhashmap(2048);
    lean_mark_persistent(g_empty_dhashmap_2048);
    g_empty_dhashmap_128 = mk_empty_dhashmap(128);
    lean_mark_persistent(g_empty_dhashmap_128);
  }
}
