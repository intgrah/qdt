#include <lean/lean.h>

extern lean_object *lean_st_ref_take(lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern lean_object *l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *, lean_object *);
extern uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
    lean_object *, lean_object *, lean_object *, lean_object *);
extern uint8_t l_Array_contains___redArg(lean_object *, lean_object *,
                                         lean_object *);
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

/* Except.error = tag 0 */
static lean_object *mk_err(lean_object *err) {
  lean_object *r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, err);
  return r;
}

/* Except.ok = tag 1 */
static lean_object *mk_ok(lean_object *val) {
  lean_object *r = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(r, 0, val);
  return r;
}

#define IS_ERR(r) (lean_obj_tag(r) == 0)
#define IS_OK(r) (lean_obj_tag(r) == 1)

/* BuildError.cycle = tag 0 */
static lean_object *mk_err_cycle(void) { return mk_err(lean_box(0)); }

#define GET_VAL(r) lean_ctor_get(r, 0)

static lean_object *mk_memo(lean_object *value, lean_object *deps,
                            uint64_t hash) {
  lean_object *m = lean_alloc_ctor(0, 2, sizeof(uint64_t));
  lean_ctor_set(m, 0, value);
  lean_ctor_set(m, 1, deps);
  lean_ctor_set_uint64(m, sizeof(void *) * 2, hash);
  return m;
}

static lean_object *shake_fetch(lean_object *beq, lean_object *hashQ,
                                lean_object *hashR, lean_object *input_fn,
                                lean_object *tasks, lean_object *cache_ref,
                                lean_object *started_ref,
                                lean_object *stack_ref, lean_object *key);

/* fetch' callback for tasks. Returns Except BuildError (R q) directly.
 * Closure captures: beq, hashQ, hashR, input_fn, tasks, cache_ref,
 * started_ref, stack_ref, deps_ref. Free arg: key. */
static lean_object *shake_fetch_cb(lean_object *beq, lean_object *hashQ,
                                   lean_object *hashR, lean_object *input_fn,
                                   lean_object *tasks, lean_object *cache_ref,
                                   lean_object *started_ref,
                                   lean_object *stack_ref,
                                   lean_object *deps_ref, lean_object *key) {
  lean_object *result = shake_fetch(beq, hashQ, hashR, input_fn, tasks,
                                    cache_ref, started_ref, stack_ref, key);
  if (IS_ERR(result))
    return result;

  lean_object *value = GET_VAL(result);
  lean_inc(value);
  lean_dec_ref(result);

  lean_object *ds = lean_st_ref_get(deps_ref);
  lean_inc(key);
  lean_inc_ref(beq);
  lean_inc_ref(hashQ);
  uint8_t has =
      l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(beq, hashQ, ds, key);
  lean_dec(ds);

  if (!has) {
    uint64_t h;
    lean_object *started = lean_st_ref_get(started_ref);
    lean_inc(key);
    lean_inc_ref(beq);
    lean_inc_ref(hashQ);
    lean_object *memo_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        beq, hashQ, started, key);
    lean_dec(started);

    if (!lean_is_scalar(memo_opt)) {
      lean_object *memo = lean_ctor_get(memo_opt, 0);
      h = lean_ctor_get_uint64(memo, sizeof(void *) * 2);
      lean_dec_ref(memo_opt);
    } else {
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
    lean_inc_ref(beq);
    lean_inc_ref(hashQ);
    lean_object *new_ds = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beq, hashQ, old_ds, key, lean_box_uint64(h));
    lean_st_ref_set(deps_ref, new_ds);
  }

  lean_dec(key);
  return mk_ok(value);
}

static int verify_deps(lean_object *beq, lean_object *hashQ, lean_object *hashR,
                       lean_object *input_fn, lean_object *tasks,
                       lean_object *cache_ref, lean_object *started_ref,
                       lean_object *stack_ref, lean_object *deps,
                       lean_object **err_out) {
  lean_object *buckets = lean_ctor_get(deps, 1);
  size_t n = lean_array_size(buckets);

  for (size_t i = 0; i < n; i++) {
    lean_object *node = lean_array_uget(buckets, i);
    while (!lean_is_scalar(node)) {
      lean_object *dep_key = lean_ctor_get(node, 0);
      lean_object *old_hash_box = lean_ctor_get(node, 1);
      uint64_t old_hash = lean_unbox_uint64(old_hash_box);

      lean_object *result =
          shake_fetch(beq, hashQ, hashR, input_fn, tasks, cache_ref,
                      started_ref, stack_ref, dep_key);
      if (IS_ERR(result)) {
        *err_out = result;
        return 2;
      }
      lean_dec_ref(result);

      lean_object *started = lean_st_ref_get(started_ref);
      lean_inc(dep_key);
      lean_inc_ref(beq);
      lean_inc_ref(hashQ);
      lean_object *memo_opt =
          l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(beq, hashQ,
                                                             started, dep_key);
      lean_dec(started);

      uint64_t cur_hash;
      if (!lean_is_scalar(memo_opt)) {
        lean_object *memo = lean_ctor_get(memo_opt, 0);
        cur_hash = lean_ctor_get_uint64(memo, sizeof(void *) * 2);
      } else {
        cur_hash = 0;
      }
      lean_dec_ref(memo_opt);

      if (cur_hash != old_hash)
        return 1;

      node = lean_ctor_get(node, 2);
    }
  }
  return 0;
}

static lean_object *run_task(lean_object *beq, lean_object *hashQ,
                             lean_object *hashR, lean_object *input_fn,
                             lean_object *tasks, lean_object *cache_ref,
                             lean_object *started_ref, lean_object *stack_ref,
                             lean_object *task) {
  lean_inc(g_empty_dhashmap_128);
  lean_object *deps_ref = lean_st_mk_ref(g_empty_dhashmap_128);

  /* fetch' closure: 10 args total, 9 captured, 1 free (key) */
  lean_inc_ref(beq);
  lean_inc_ref(hashQ);
  lean_inc_ref(hashR);
  lean_inc_ref(input_fn);
  lean_inc_ref(tasks);
  lean_inc(cache_ref);
  lean_inc(started_ref);
  lean_inc(stack_ref);
  lean_inc(deps_ref);
  lean_object *fetch_closure =
      lean_alloc_closure((void *)shake_fetch_cb, 10, 9);
  lean_closure_set(fetch_closure, 0, beq);
  lean_closure_set(fetch_closure, 1, hashQ);
  lean_closure_set(fetch_closure, 2, hashR);
  lean_closure_set(fetch_closure, 3, input_fn);
  lean_closure_set(fetch_closure, 4, tasks);
  lean_closure_set(fetch_closure, 5, cache_ref);
  lean_closure_set(fetch_closure, 6, started_ref);
  lean_closure_set(fetch_closure, 7, stack_ref);
  lean_closure_set(fetch_closure, 8, deps_ref);

  /* task : ∀ f [Monad f], (∀ i, V i) → (∀ q, f (R q)) → f (R q)
   * f = Except BuildError, so result is Except directly */
  lean_inc(task);
  lean_inc(g_monad_inst);
  lean_inc_ref(input_fn);
  lean_object *result =
      lean_apply_4(task, lean_box(0), g_monad_inst, input_fn, fetch_closure);

  if (IS_ERR(result)) {
    lean_dec(deps_ref);
    return result;
  }

  lean_object *value = GET_VAL(result);
  lean_inc(value);
  lean_dec_ref(result);

  lean_object *recorded_deps = lean_st_ref_get(deps_ref);
  lean_dec(deps_ref);

  lean_object *pair = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(pair, 0, value);
  lean_ctor_set(pair, 1, recorded_deps);
  return mk_ok(pair);
}

static lean_object *shake_fetch(lean_object *beq, lean_object *hashQ,
                                lean_object *hashR, lean_object *input_fn,
                                lean_object *tasks, lean_object *cache_ref,
                                lean_object *started_ref,
                                lean_object *stack_ref, lean_object *key) {
  /* Check started map */
  {
    lean_object *started = lean_st_ref_get(started_ref);
    lean_inc(key);
    lean_inc_ref(beq);
    lean_inc_ref(hashQ);
    lean_object *memo_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
        beq, hashQ, started, key);
    lean_dec(started);
    if (!lean_is_scalar(memo_opt)) {
      lean_object *memo = lean_ctor_get(memo_opt, 0);
      lean_object *value = lean_ctor_get(memo, 0);
      lean_inc(value);
      lean_dec_ref(memo_opt);
      return mk_ok(value);
    }
    lean_dec(memo_opt);
  }

  /* Cycle detection */
  {
    lean_object *stack = lean_st_ref_get(stack_ref);
    lean_inc(key);
    lean_inc(stack);
    lean_inc_ref(beq);
    uint8_t on_stack = l_Array_contains___redArg(beq, stack, key);
    lean_dec(stack);
    if (on_stack)
      return mk_err_cycle();
  }

  /* Push onto stack */
  {
    lean_object *stack = lean_st_ref_take(stack_ref);
    lean_inc(key);
    stack = lean_array_push(stack, key);
    lean_st_ref_set(stack_ref, stack);
  }

  lean_object *result;

  /* Get the task (always returns a Task, no Option) */
  lean_inc(key);
  lean_inc_ref(tasks);
  lean_object *task = lean_apply_1(tasks, key);

  /* Check cache for existing memo */
  lean_object *cache = lean_st_ref_get(cache_ref);
  lean_inc(key);
  lean_inc_ref(beq);
  lean_inc_ref(hashQ);
  lean_object *cached_opt = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(
      beq, hashQ, cache, key);
  lean_dec(cache);

  if (lean_is_scalar(cached_opt)) {
    lean_dec(cached_opt);
    goto compute;
  } else {
    lean_object *cached_memo = lean_ctor_get(cached_opt, 0);
    lean_inc(cached_memo);
    lean_dec_ref(cached_opt);

    lean_object *cached_deps = lean_ctor_get(cached_memo, 1);
    lean_object *err = NULL;
    int vr = verify_deps(beq, hashQ, hashR, input_fn, tasks, cache_ref,
                         started_ref, stack_ref, cached_deps, &err);

    if (vr == 2) {
      lean_dec(cached_memo);
      lean_dec(task);
      result = err;
    } else if (vr == 0) {
      lean_dec(task);
      lean_object *old_started = lean_st_ref_take(started_ref);
      lean_inc(key);
      lean_inc(cached_memo);
      lean_inc_ref(beq);
      lean_inc_ref(hashQ);
      lean_object *new_started =
          l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
              beq, hashQ, old_started, key, cached_memo);
      lean_st_ref_set(started_ref, new_started);

      lean_object *value = lean_ctor_get(cached_memo, 0);
      lean_inc(value);
      lean_dec(cached_memo);
      result = mk_ok(value);
    } else {
      lean_dec(cached_memo);
      goto compute;
    }
    goto done;
  }

compute:;
  lean_object *comp_result = run_task(beq, hashQ, hashR, input_fn, tasks,
                                      cache_ref, started_ref, stack_ref, task);
  lean_dec(task);

  if (IS_ERR(comp_result)) {
    result = comp_result;
  } else {
    lean_object *pair = GET_VAL(comp_result);
    lean_object *value = lean_ctor_get(pair, 0);
    lean_object *deps = lean_ctor_get(pair, 1);
    lean_inc(value);
    lean_inc(deps);
    lean_dec_ref(comp_result);

    lean_inc(key);
    lean_inc(value);
    lean_inc_ref(hashR);
    lean_object *h_box = lean_apply_2(hashR, key, value);
    uint64_t h = lean_unbox_uint64(h_box);
    lean_dec_ref(h_box);

    lean_inc(value);
    lean_inc(deps);
    lean_object *memo = mk_memo(value, deps, h);

    lean_object *old_started = lean_st_ref_take(started_ref);
    lean_inc(key);
    lean_inc(memo);
    lean_inc_ref(beq);
    lean_inc_ref(hashQ);
    lean_object *new_started =
        l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
            beq, hashQ, old_started, key, memo);
    lean_st_ref_set(started_ref, new_started);

    lean_object *old_cache = lean_st_ref_take(cache_ref);
    lean_inc(key);
    lean_inc(memo);
    lean_inc_ref(beq);
    lean_inc_ref(hashQ);
    lean_object *new_cache = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(
        beq, hashQ, old_cache, key, memo);
    lean_st_ref_set(cache_ref, new_cache);

    lean_dec(memo);
    result = mk_ok(value);
  }

done: {
  lean_object *stack = lean_st_ref_take(stack_ref);
  stack = lean_array_pop(stack);
  lean_st_ref_set(stack_ref, stack);
}

  return result;
}

LEAN_EXPORT lean_object *
lean_shake_build(lean_object *beq, lean_object *hashQ, lean_object *hashR,
                 lean_object *input_fn, lean_object *tasks, lean_object *target,
                 lean_object *cache) {
  ensure_init();
  lean_object *cache_ref = lean_st_mk_ref(cache);

  lean_inc(g_empty_dhashmap_2048);
  lean_object *started_ref = lean_st_mk_ref(g_empty_dhashmap_2048);

  lean_object *empty_arr =
      lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(0u));
  lean_object *stack_ref = lean_st_mk_ref(empty_arr);

  lean_object *result = shake_fetch(beq, hashQ, hashR, input_fn, tasks,
                                    cache_ref, started_ref, stack_ref, target);

  if (IS_OK(result)) {
    lean_object *value = GET_VAL(result);
    lean_inc(value);
    lean_dec_ref(result);

    lean_object *final_cache = lean_st_ref_get(cache_ref);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, value);
    lean_ctor_set(pair, 1, final_cache);
    result = mk_ok(pair);
  }

  lean_dec(cache_ref);
  lean_dec(started_ref);
  lean_dec(stack_ref);

  lean_dec_ref(beq);
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
