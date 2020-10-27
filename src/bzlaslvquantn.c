/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2015-2017 Mathias Preiner.
 *  Copyright (C) 2017 Aina Niemetz.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include "bzlaabort.h"
#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlamodel.h"
#include "bzlaprintmodel.h"
#include "bzlaslvfun.h"
#include "bzlaslvquant.h"
#include "bzlasynth.h"
#include "dumper/bzladumpsmt.h"
#include "preprocess/bzlader.h"
#include "preprocess/bzlaminiscope.h"
#include "preprocess/bzlanormquant.h"
#include "preprocess/bzlaskolemize.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#if 1

static void
qlog(const char *fmt, ...)
{
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  fflush(stdout);
  va_end(ap);
}

#else

#define qlog(...)        \
  while (false)          \
  {                      \
    printf(__VA_ARGS__); \
  }

#endif

/*------------------------------------------------------------------------*/

struct Instance
{
  BzlaNode *instance;
  BzlaNode *q;
  BzlaNode *args;
};

typedef struct Instance Instance;

/*------------------------------------------------------------------------*/
/* Solver State                                                           */
/*------------------------------------------------------------------------*/

struct QuantSolverState
{
  Bzla *bzla;
  /* Contains currently active quantifiers (populatd by
   * get_active_quantifiers). The flag indiciates the current polarity of
   * the quantifier. */
  BzlaPtrHashTable *active_quantifiers;
  BzlaPtrHashTable *inactive_quantifiers;
  BzlaPtrHashTable *deps;
  BzlaPtrHashTable *backrefs;
  BzlaPtrHashTable *instances;

  BzlaPtrHashTable *instantiated;

  /* Maps quantifier to introduced skolem. */
  BzlaPtrHashTable *skolems;
  /* Maps quantifier to instantiation constant. */
  BzlaPtrHashTable *instantiation_constants;
  /* Cache for added skolemization lemmas. */
  BzlaPtrHashTable *added_skolemization_lemmas;
  /* Cache for quantified formulas instantiated by instantiation constants. */
  BzlaPtrHashTable *default_instantiations;
  /* Pending lemmas to be added. */
  BzlaNodePtrStack lemmas_pending;
  /* Cache of added lemmas. */
  BzlaPtrHashTable *lemma_cache;

  BzlaPtrHashTable *ce_literals;

  bool added_lemma;
};

typedef struct QuantSolverState QuantSolverState;

QuantSolverState *
new_quant_solver_state(Bzla *bzla)
{
  QuantSolverState *state;
  BZLA_CNEW(bzla->mm, state);

  state->bzla = bzla;
  state->active_quantifiers =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->inactive_quantifiers =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->deps = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  state->backrefs =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->instances =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->instantiated =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->skolems = bzla_hashptr_table_new(bzla->mm,
                                          (BzlaHashPtr) bzla_node_hash_by_id,
                                          (BzlaCmpPtr) bzla_node_compare_by_id);
  state->instantiation_constants =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->added_skolemization_lemmas =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->default_instantiations =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->lemma_cache =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  state->ce_literals =
      bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);
  BZLA_INIT_STACK(bzla->mm, state->lemmas_pending);
  return state;
}

void
delete_quant_solver_state(QuantSolverState *state)
{
  Bzla *bzla;
  BzlaPtrHashTableIterator it;

  bzla = state->bzla;

  bzla_hashptr_table_delete(state->active_quantifiers);

  // TODO: proper cleanup
  bzla_hashptr_table_delete(state->deps);
  bzla_hashptr_table_delete(state->instantiated);
  bzla_hashptr_table_delete(state->instances);
  // end

  bzla_iter_hashptr_init(&it, state->skolems);
  bzla_iter_hashptr_queue(&it, state->instantiation_constants);
  bzla_iter_hashptr_queue(&it, state->default_instantiations);
  bzla_iter_hashptr_queue(&it, state->ce_literals);
  bzla_iter_hashptr_queue(&it, state->backrefs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, it.bucket->data.as_ptr);
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(state->skolems);
  bzla_hashptr_table_delete(state->instantiation_constants);
  bzla_hashptr_table_delete(state->default_instantiations);
  bzla_hashptr_table_delete(state->backrefs);

  bzla_iter_hashptr_init(&it, state->added_skolemization_lemmas);
  bzla_iter_hashptr_queue(&it, state->lemma_cache);
  bzla_iter_hashptr_queue(&it, state->inactive_quantifiers);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(state->added_skolemization_lemmas);
  bzla_hashptr_table_delete(state->lemma_cache);

  BZLA_RELEASE_STACK(state->lemmas_pending);
  BZLA_DELETE(bzla->mm, state);
}

/*------------------------------------------------------------------------*/

struct BzlaQuantSolver
{
  BZLA_SOLVER_STRUCT;

  QuantSolverState *state;
};

typedef struct BzlaQuantSolver BzlaQuantSolver;

/*------------------------------------------------------------------------*/

///////////////////////////////////////////////////////////////////////////////

static BzlaNode *
find_backref(QuantSolverState *state, BzlaNode *q)
{
  BzlaPtrHashBucket *b;

  while ((b = bzla_hashptr_table_get(state->backrefs, q)))
  {
    q = b->data.as_ptr;
  }

  return q;
}

static void
add_backref(QuantSolverState *state, BzlaNode *qfrom, BzlaNode *qto)
{
  BzlaPtrHashBucket *b;
  BzlaNode *backref;

  backref = find_backref(state, qto);

  if ((b = bzla_hashptr_table_get(state->backrefs, qfrom)))
  {
    assert(b->data.as_ptr == backref);
  }
  else
  {
    bzla_hashptr_table_add(state->backrefs, bzla_node_copy(state->bzla, qfrom))
        ->data.as_ptr = bzla_node_copy(state->bzla, backref);

    //    log ("::: %s -> %s\n", bzla_util_node2string(qfrom),
    //    bzla_util_node2string(qto));
  }
}

static void
get_active_quantifiers(QuantSolverState *state)
{
  double start, delta;
  uint32_t i;
  Bzla *bzla;
  BzlaBitVector *value;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *quantifiers;
  BzlaNodePtrStack visit;
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache;

  start = bzla_util_time_stamp();
  bzla  = state->bzla;
  mm    = bzla->mm;

  quantifiers = bzla_hashptr_table_new(mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);

  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, visit);

  /* collect all reachable function equalities */
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  // add assumptions later?
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(visit, bzla_iter_hashptr_next(&it));
  }

  qlog("Active quantifiers:\n");
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id) || !cur->quantifier_below)
      continue;

    bzla_hashint_table_add(cache, cur->id);

    // TODO: check if this is required
    assert(bzla_node_is_synth(cur));

    if (bzla_node_is_quantifier(cur))
    {
      if (!bzla_hashptr_table_get(state->inactive_quantifiers, cur))
      {
        assert(!bzla_hashptr_table_get(quantifiers, cur));
        value = bzla_model_get_bv_assignment(bzla, cur);
        assert(value);
        bool phase = bzla_bv_is_true(value);
        bzla_bv_free(mm, value);
        bzla_hashptr_table_add(quantifiers, cur)->data.flag = phase;
        qlog("  %s (%s) (instance: %s)\n",
             bzla_util_node2string(cur),
             phase ? "true" : "false",
             bzla_util_node2string(find_backref(state, cur)));
      }
    }
    else
    {
      for (i = 0; i < cur->arity; ++i)
      {
        BZLA_PUSH_STACK(visit, cur->e[i]);
      }
    }
  }
  BZLA_RELEASE_STACK(visit);

  bzla_hashptr_table_delete(state->active_quantifiers);
  state->active_quantifiers = quantifiers;

  delta = bzla_util_time_stamp() - start;
}

static bool
is_forall(QuantSolverState *state, BzlaNode *q)
{
  BzlaPtrHashBucket *b;

  q = bzla_node_real_addr(q);
  b = bzla_hashptr_table_get(state->active_quantifiers, q);
  if (!b)
  {
    return false;
  }
  return b->data.flag;
}

static bool
is_exists(QuantSolverState *state, BzlaNode *q)
{
  BzlaPtrHashBucket *b;

  q = bzla_node_real_addr(q);
  b = bzla_hashptr_table_get(state->active_quantifiers, q);
  if (!b)
  {
    return false;
  }
  return !b->data.flag;
}

static BzlaNode *
substitute(Bzla *bzla,
           BzlaNode *n,
           BzlaPtrHashTable *substs,
           BzlaPtrHashTable *backref)
{
  assert(bzla);
  assert(n);
  assert(substs);

  uint32_t i;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *subst, *result, *e[4], *c;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d, *dd;
  BzlaPtrHashBucket *b;

  mm    = bzla->mm;
  cache = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, n);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    d        = bzla_hashint_map_get(cache, real_cur->id);

    if (!d)
    {
      d = bzla_hashint_map_add(cache, real_cur->id);
      if ((b = bzla_hashptr_table_get(substs, real_cur)))
      {
        subst     = b->data.as_ptr;
        d->as_ptr = bzla_node_copy(bzla, subst);

        /* Keep track of instantiated variables */
        if (bzla_node_is_param(real_cur)
            && bzla_node_param_is_forall_var(real_cur))
        {
          bzla_hashptr_table_add(backref, real_cur)->data.as_ptr =
              bzla_node_copy(bzla, subst);
          // printf ("backref: %s -> %s\n", bzla_util_node2string(real_cur),
          // bzla_util_node2string(subst));
        }

        continue;
      }

      BZLA_PUSH_STACK(visit, cur);
      for (i = 0; i < real_cur->arity; ++i)
      {
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      for (i = 0; i < real_cur->arity; ++i)
      {
        c = bzla_node_real_addr(real_cur->e[i]);
        assert(bzla_hashint_map_contains(cache, c->id));
        dd   = bzla_hashint_map_get(cache, c->id);
        e[i] = bzla_node_cond_invert(real_cur->e[i], dd->as_ptr);
      }

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur))
        {
          result = bzla_node_mk_param_with_unique_symbol(bzla, real_cur);
        }
        else
        {
          result = bzla_node_copy(bzla, real_cur);
        }
      }
      else if (bzla_node_is_bv_slice(real_cur))
      {
        result = bzla_exp_bv_slice(bzla,
                                   e[0],
                                   bzla_node_bv_slice_get_upper(real_cur),
                                   bzla_node_bv_slice_get_lower(real_cur));
      }
      else if (bzla_node_is_fp_to_sbv(real_cur))
      {
        result = bzla_exp_fp_to_sbv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_ubv(real_cur))
      {
        result = bzla_exp_fp_to_ubv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_bv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_bv(
            bzla, e[0], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_fp(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_fp(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_int(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_int(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_uint(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_uint(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else
      {
        /* if the param of a quantifier gets subtituted by a non-param,
         * we do not create a quantifier, but return the body instead */
        if (bzla_node_is_quantifier(real_cur) && !bzla_node_is_param(e[0]))
        {
          result = bzla_node_copy(bzla, e[1]);
        }
        else
        {
          result = bzla_exp_create(bzla, real_cur->kind, e, real_cur->arity);

          if (bzla_node_is_quantifier(real_cur)
              && bzla_node_is_quantifier(result))
          {
            bzla_hashptr_table_add(backref, real_cur)->data.as_ptr =
                bzla_node_copy(bzla, result);
            // printf ("backref: %s -> %s\n", bzla_util_node2string(real_cur),
            // bzla_util_node2string(result));
          }
        }
      }
      assert(bzla_node_get_sort_id(real_cur) == bzla_node_get_sort_id(result));

      if (bzla_node_is_param(real_cur)
          && bzla_node_param_is_forall_var(real_cur))
      {
        bzla_hashptr_table_add(backref, real_cur)->data.as_ptr =
            bzla_node_copy(bzla, result);
        //  printf ("backref: %s -> %s\n", bzla_util_node2string(real_cur),
        //  bzla_util_node2string(result));
      }

      d->as_ptr = result;
    }
  }
  assert(bzla_hashint_map_contains(cache, bzla_node_real_addr(n)->id));
  dd     = bzla_hashint_map_get(cache, bzla_node_real_addr(n)->id);
  result = bzla_node_cond_invert(n, bzla_node_copy(bzla, dd->as_ptr));

  BZLA_RELEASE_STACK(visit);
  for (size_t j = 0; j < cache->size; ++j)
  {
    if (!cache->data[j].as_ptr) continue;
    bzla_node_release(bzla, cache->data[j].as_ptr);
  }
  bzla_hashint_map_delete(cache);
  return result;
}

static void
add_instance(QuantSolverState *state,
             BzlaNode *q,
             BzlaNode *qi,
             BzlaPtrHashTable *substs)
{
  Bzla *bzla;
  BzlaNode *cur;
  BzlaPtrHashBucket *b, *bi;
  BzlaNodePtrStack args;
  BzlaNodePtrStack *qdeps, *qideps;

  bzla = state->bzla;

  if (q == qi)
  {
    return;
  }

  if ((bi = bzla_hashptr_table_get(state->deps, qi)))
  {
    // TODO: check if we need to do anything here
    // log("******* already added\n");
    return;
  }
  else
  {
    bi = bzla_hashptr_table_add(state->deps, qi);
  }

  b = bzla_hashptr_table_get(state->deps, q);
  assert(b);
  qdeps = b->data.as_ptr;

  BZLA_CNEW(bzla->mm, qideps);
  BZLA_INIT_STACK(bzla->mm, *qideps);
  bi->data.as_ptr = qideps;

  qlog("Add new instance: %s\n", bzla_util_node2string(qi));
  for (size_t i = 0, size = BZLA_COUNT_STACK(*qdeps); i < size; ++i)
  {
    cur = BZLA_PEEK_STACK(*qdeps, i);
    if ((b = bzla_hashptr_table_get(substs, cur)))
    {
      BZLA_PUSH_STACK(*qideps, bzla_node_copy(bzla, b->data.as_ptr));
      qlog("  dep: %s -> %s\n",
           bzla_util_node2string(cur),
           bzla_util_node2string(b->data.as_ptr));
    }
    else
    {
      BZLA_PUSH_STACK(*qideps, bzla_node_copy(bzla, cur));
      qlog("  dep: %s\n", bzla_util_node2string(cur));
    }
  }
}

static BzlaNode *
instantiate(QuantSolverState *state, BzlaNode *q, BzlaPtrHashTable *substs)
{
  assert(bzla_node_is_quantifier(q));

  Bzla *bzla;
  BzlaPtrHashTable *backref;
  BzlaNode *qi, *result;
  BzlaPtrHashTableIterator it;

  bzla    = state->bzla;
  backref = bzla_hashptr_table_new(bzla->mm,
                                   (BzlaHashPtr) bzla_node_hash_by_id,
                                   (BzlaCmpPtr) bzla_node_compare_by_id);

  result = substitute(bzla, q, substs, backref);

  bzla_iter_hashptr_init(&it, backref);
  while (bzla_iter_hashptr_has_next(&it))
  {
    qi = it.bucket->data.as_ptr;
    q  = bzla_iter_hashptr_next(&it);

    if (!bzla_node_is_quantifier(q)) continue;

    add_backref(state, qi, q);
    add_instance(state, q, qi, backref);
    bzla_node_release(bzla, qi);
  }

  return result;
}

static BzlaNode *
get_inst_constant(QuantSolverState *state, BzlaNode *q)
{
  Bzla *bzla;
  BzlaNode *sk;
  BzlaSortId sort;
  BzlaPtrHashBucket *b;

  if ((b = bzla_hashptr_table_get(state->instantiation_constants, q)))
  {
    return b->data.as_ptr;
  }
  bzla = state->bzla;

  sort = bzla_node_get_sort_id(q->e[0]);

  char *sym = bzla_node_get_symbol(bzla, q->e[0]);
  if (sym)
  {
    size_t len = strlen(sym) + 5;
    char buf[len];
    snprintf(buf, len, "ic(%s)", sym);
    sk = bzla_node_create_var(bzla, sort, buf);
  }
  else
  {
    sk = bzla_node_create_var(bzla, sort, 0);
  }

  bzla_hashptr_table_add(state->instantiation_constants,
                         bzla_node_copy(bzla, q))
      ->data.as_ptr = sk;

  return sk;
}

static BzlaNode *
mk_skolem_aux(QuantSolverState *state, BzlaNode *q, const char *sym)
{
  Bzla *bzla;
  BzlaNode *result = 0, *backref, *cur, *sk;
  BzlaNodePtrStack *deps, args;
  BzlaPtrHashBucket *b;
  BzlaSortIdStack sorts;
  BzlaSortId domain, codomain, sort;

  bzla = state->bzla;

  if ((b = bzla_hashptr_table_get(state->deps, q)))
  {
    BZLA_INIT_STACK(state->bzla->mm, sorts);
    BZLA_INIT_STACK(state->bzla->mm, args);

    qlog("# SKOLEM UF: %s\n", bzla_util_node2string(q));
    // log ("# backref: %s\n", bzla_util_node2string(backref));

    /* Collect sorts of universal variable dependencies. */
    deps = b->data.as_ptr;
    for (size_t i = 0, size = BZLA_COUNT_STACK(*deps); i < size; ++i)
    {
      cur = BZLA_PEEK_STACK(*deps, i);
      if (bzla_node_is_param(cur))
      {
        assert(is_exists(state, bzla_node_param_get_binder(cur)));
      }
      else
      {
        qlog("  %s\n", bzla_util_node2string(cur));
        BZLA_PUSH_STACK(sorts, bzla_node_get_sort_id(cur));
        BZLA_PUSH_STACK(args, cur);
      }
    }

    if (!BZLA_EMPTY_STACK(sorts))
    {
      backref = find_backref(state, q);
      if ((b = bzla_hashptr_table_get(state->skolems, backref)))
      {
        sk = b->data.as_ptr;
      }
      else
      {
        domain   = bzla_sort_tuple(bzla, sorts.start, BZLA_COUNT_STACK(sorts));
        codomain = bzla_node_get_sort_id(q->e[0]);
        sort     = bzla_sort_fun(bzla, domain, codomain);
        bzla_sort_release(bzla, domain);
        sk = bzla_exp_uf(bzla, sort, sym);
        bzla_hashptr_table_add(state->skolems, bzla_node_copy(bzla, backref))
            ->data.as_ptr = sk;
      }
      assert(BZLA_COUNT_STACK(args) == bzla_node_fun_get_arity(bzla, sk));

      result = bzla_exp_apply_n(bzla, sk, args.start, BZLA_COUNT_STACK(args));
    }

    BZLA_RELEASE_STACK(sorts);
    BZLA_RELEASE_STACK(args);
  }
  return result;
}

static BzlaNode *
mk_skolem(QuantSolverState *state, BzlaNode *q, const char *sym)
{
  Bzla *bzla;
  BzlaNode *sk;
  BzlaSortId sort;

  bzla = state->bzla;
  sort = bzla_node_get_sort_id(q->e[0]);

  sk = mk_skolem_aux(state, q, sym);
  if (!sk)
  {
    sk = bzla_node_create_var(bzla, sort, sym);
  }
  return sk;
}

static BzlaNode *
get_skolem(QuantSolverState *state, BzlaNode *q)
{
  Bzla *bzla;
  BzlaNode *sk;
  BzlaPtrHashBucket *b;

  if ((b = bzla_hashptr_table_get(state->skolems, q)))
  {
    return b->data.as_ptr;
  }
  bzla = state->bzla;

  char *sym = bzla_node_get_symbol(bzla, q->e[0]);
  if (sym)
  {
    size_t len = strlen(sym) + 5;
    char buf[len];
    snprintf(buf, len, "sk(%s)", sym);
    sk = mk_skolem(state, q, buf);
  }
  else
  {
    sk = mk_skolem(state, q, 0);
  }

  qlog("New skolem %s for %s\n",
       bzla_util_node2string(sk),
       bzla_util_node2string(q));
  bzla_hashptr_table_add(state->skolems, bzla_node_copy(bzla, q))->data.as_ptr =
      sk;

  return sk;
}

static BzlaNode *
get_ce_literal(QuantSolverState *state, BzlaNode *q)
{
  Bzla *bzla;
  BzlaNode *lit;
  BzlaSortId sort;
  BzlaPtrHashBucket *b;

  if ((b = bzla_hashptr_table_get(state->ce_literals, q)))
  {
    return b->data.as_ptr;
  }
  bzla = state->bzla;

  sort = bzla_sort_bool(bzla);

  size_t len = bzla_util_num_digits(bzla_node_get_id(q)) + 8;
  char buf[len];
  snprintf(buf, len, "celit(%u)", bzla_node_get_id(q));
  lit = bzla_node_create_var(bzla, sort, buf);

  bzla_hashptr_table_add(state->ce_literals, bzla_node_copy(bzla, q))
      ->data.as_ptr = lit;

  return lit;
}

// ~l_i => ~P[sk(x)]
static BzlaNode *
get_skolemization_lemma(QuantSolverState *state, BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  Bzla *bzla;
  BzlaNode *cur, *sk, *inst, *lemma;
  BzlaNodeIterator it;
  BzlaPtrHashTable *map;
  BzlaPtrHashBucket *b;

  if ((b = bzla_hashptr_table_get(state->added_skolemization_lemmas, q)))
  {
    return b->data.as_ptr;
  }
  qlog("Add skolemization lemma: %s\n", bzla_util_node2string(q));

  bzla = state->bzla;
  map  = bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    sk  = get_skolem(state, cur);
    bzla_hashptr_table_add(map, cur->e[0])->data.as_ptr = sk;
    qlog("  %s -> %s\n",
         bzla_util_node2string(cur->e[0]),
         bzla_util_node2string(sk));
  }

  // inst = substitute (bzla, body, map, true, 0);
  inst = instantiate(state, q, map);
  bzla_hashptr_table_delete(map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  lemma = bzla_exp_implies(bzla, bzla_node_invert(q), bzla_node_invert(inst));
  bzla_node_release(bzla, inst);
  bzla_hashptr_table_add(state->added_skolemization_lemmas,
                         bzla_node_copy(bzla, q))
      ->data.as_ptr = lemma;
  // BZLA_PUSH_STACK (state->lemmas_pending, lemma);
  return lemma;
}

BzlaNode *
get_ce_lemma(QuantSolverState *state, BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  Bzla *bzla;
  BzlaNode *cur, *ic, *inst, *lemma;
  BzlaNodeIterator it;
  BzlaPtrHashTable *map;
  BzlaPtrHashBucket *b;

  if ((b = bzla_hashptr_table_get(state->default_instantiations, q)))
  {
    return b->data.as_ptr;
  }

  qlog("Add CE lemma: %s (%s)\n",
       bzla_util_node2string(q),
       bzla_util_node2string(find_backref(state, q)));

  bzla = state->bzla;
  map  = bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
  /* Get instantiations constants for variables in q. */
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur = bzla_iter_binder_next(&it);
    ic  = get_inst_constant(state, cur);
    bzla_hashptr_table_add(map, cur->e[0])->data.as_ptr = ic;
  }

  inst = instantiate(state, q, map);
  bzla_hashptr_table_delete(map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  lemma =
      bzla_exp_implies(bzla, get_ce_literal(state, q), bzla_node_invert(inst));
  bzla_node_release(bzla, inst);

  bzla_hashptr_table_add(state->default_instantiations, bzla_node_copy(bzla, q))
      ->data.as_ptr = lemma;
  return lemma;
}

BzlaNode *
get_value(Bzla *bzla, BzlaNode *n)
{
  BzlaFloatingPoint *fp_value;
  BzlaBitVector *bv_value;
  BzlaNode *value = 0;

  bv_value = bzla_model_get_bv_assignment(bzla, n);
  if (bzla_node_is_bv(bzla, n))
  {
    value = bzla_exp_bv_const(bzla, bv_value);
  }
  else if (bzla_node_is_fp(bzla, n))
  {
    fp_value = bzla_fp_from_bv(bzla, bzla_node_get_sort_id(n), bv_value);
    value    = bzla_exp_fp_const_fp(bzla, fp_value);
    bzla_fp_free(bzla, fp_value);
  }
  assert(value);
  bzla_bv_free(bzla->mm, bv_value);
  return value;
}

static void
add_lemma(QuantSolverState *state, BzlaNode *lem)
{
  if (bzla_hashptr_table_get(state->lemma_cache, lem))
  {
    // log ("Duplicate lemma: %s\n", bzla_util_node2string (lem));
    return;
  }
  // log ("Add lemma: %s\n", bzla_util_node2string(lem));
  bzla_assert_exp(state->bzla, lem);
  bzla_hashptr_table_add(state->lemma_cache, bzla_node_copy(state->bzla, lem));
  state->added_lemma = true;
}

// l_i => P[t]
static void
add_value_instantiation_lemma(QuantSolverState *state, BzlaNode *q)
{
  assert(bzla_node_is_regular(q));
  assert(!q->parameterized);

  Bzla *bzla;
  BzlaNode *cur, *ic, *inst, *lemma, *value;
  BzlaNodeIterator it;
  BzlaPtrHashTable *map;

  bzla = state->bzla;
  map  = bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);

  qlog("Add value instantiation: %s\n", bzla_util_node2string(q));
  /* Collect model values for instantiation constants of q. */
  bzla_iter_binder_init(&it, q);
  while (bzla_iter_binder_has_next(&it))
  {
    cur   = bzla_iter_binder_next(&it);
    ic    = get_inst_constant(state, cur);
    value = get_value(bzla, ic);
    bzla_hashptr_table_add(map, cur->e[0])->data.as_ptr = value;
    qlog("  %s -> %s\n",
         bzla_util_node2string(cur->e[0]),
         bzla_util_node2string(value));
  }

  // inst = substitute (bzla, body, map, true, 0);
  inst = instantiate(state, q, map);
  // TODO: release values?
  bzla_hashptr_table_delete(map);
  assert(!bzla_node_real_addr(inst)->parameterized);

  lemma = bzla_exp_implies(bzla, q, inst);
  bzla_node_release(bzla, inst);
  add_lemma(state, lemma);
}

static void
set_inactive(QuantSolverState *state, BzlaNode *q)
{
  assert(!bzla_hashptr_table_get(state->inactive_quantifiers, q));
  bzla_hashptr_table_add(state->inactive_quantifiers, q);
  qlog("Set inactive: %s\n", bzla_util_node2string(q));
}

static bool
is_inactive(QuantSolverState *state, BzlaNode *q)
{
  return bzla_hashptr_table_get(state->inactive_quantifiers, q) != 0;
}

void
get_model(QuantSolverState *state, BzlaNode *q)
{
  Bzla *bzla;
  BzlaNode *cur;
  BzlaPtrHashBucket *b;

  bzla              = state->bzla;
  BzlaNode *backref = find_backref(state, q);
  b                 = bzla_hashptr_table_get(state->skolems, backref);
  assert(b);
}

bool
check_active_quantifiers(QuantSolverState *state)
{
  bool done = false;
  Bzla *bzla;
  BzlaNode *q, *lit;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack to_check, to_synth;
  BzlaSolverResult res;

  bzla = state->bzla;
  BZLA_INIT_STACK(bzla->mm, to_synth);
  BZLA_INIT_STACK(bzla->mm, to_check);

  bzla_iter_hashptr_init(&it, state->active_quantifiers);
  while (bzla_iter_hashptr_has_next(&it))
  {
    q = bzla_iter_hashptr_next(&it);

    if (is_forall(state, q))
    {
      if (!is_inactive(state, q))
      {
        add_lemma(state, get_ce_lemma(state, q));
        BZLA_PUSH_STACK(to_check, q);
      }
    }
    else
    {
      assert(is_exists(state, q));
      BZLA_PUSH_STACK(to_synth, q);
      add_lemma(state, get_skolemization_lemma(state, q));
    }
  }

#if 1
  for (size_t i = 0, size = BZLA_COUNT_STACK(to_synth); i < size; ++i)
  {
    q = BZLA_PEEK_STACK(to_synth, i);
    get_model(state, q);
  }
#endif

  size_t num_inactive = 0;
  for (size_t i = 0, size = BZLA_COUNT_STACK(to_check); i < size; ++i)
  {
    q   = BZLA_PEEK_STACK(to_check, i);
    lit = get_ce_literal(state, q);

    bzla_reset_incremental_usage(bzla);
    bzla_assume_exp(bzla, lit);

    qlog("Check for counterexamples (%s): ", bzla_util_node2string(q));

    res = bzla->slv->api.sat(bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");
      add_value_instantiation_lemma(state, q);
      continue;
    }
    else
    {
      qlog("unsat\n");
      bzla->last_sat_result = BZLA_RESULT_UNSAT;  // hack
      if (bzla_failed_exp(bzla, lit))
      {
        ++num_inactive;
        set_inactive(state, q);
      }
    }
  }
  done = num_inactive == BZLA_COUNT_STACK(to_check);

  BZLA_RELEASE_STACK(to_synth);
  return done;
}

static void
compute_variable_dependencies_aux(Bzla *bzla,
                                  BzlaNode *q,
                                  BzlaNodePtrStack *free_vars)
{
  BzlaNode *cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;

  cache = bzla_hashint_table_new(bzla->mm);

  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_PUSH_STACK(visit, q);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (!cur->parameterized || bzla_hashint_table_contains(cache, cur->id))
    {
      continue;
    }
    bzla_hashint_table_add(cache, cur->id);

    if (bzla_node_is_quantifier(cur))
    {
      bzla_hashint_table_add(cache, cur->e[0]->id);
    }
    else if (bzla_node_is_param(cur) && bzla_node_param_is_forall_var(cur))
    {
      BZLA_PUSH_STACK(*free_vars, cur);
      qlog("  %s\n", bzla_util_node2string(cur));
    }

    for (uint32_t i = 0; i < cur->arity; ++i)
    {
      BZLA_PUSH_STACK(visit, cur->e[i]);
    }
  }
}

static void
compute_variable_dependencies(QuantSolverState *state)
{
  Bzla *bzla;
  BzlaNode *q;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack *free_vars;

  bzla = state->bzla;

  bzla_iter_hashptr_init(&it, bzla->quantifiers);
  while (bzla_iter_hashptr_has_next(&it))
  {
    q = bzla_iter_hashptr_next(&it);
    if (!q->parameterized)
    {
      qlog("skip: %s\n", bzla_util_node2string(q));
      continue;
    }
    if (bzla_hashptr_table_get(state->deps, q)) continue;

    qlog("Dependencies for %s:\n", bzla_util_node2string(q));

    BZLA_CNEW(bzla->mm, free_vars);
    BZLA_INIT_STACK(bzla->mm, *free_vars);
    compute_variable_dependencies_aux(bzla, q, free_vars);
    assert(!BZLA_EMPTY_STACK(*free_vars));
    bzla_hashptr_table_add(state->deps, q)->data.as_ptr = free_vars;
  }
}

static BzlaSolverResult
check_ground_formulas(QuantSolverState *state)
{
  Bzla *bzla;
  BzlaSolverResult res;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *assumptions;
  BzlaNode *q, *lit;
  size_t i;

  bzla = state->bzla;

  if (bzla->inconsistent)
  {
    qlog("Ground formulas inconsistent\n");
    return BZLA_RESULT_UNSAT;
  }

  assumptions = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);

  bzla_iter_hashptr_init(&it, state->ce_literals);
  while (bzla_iter_hashptr_has_next(&it))
  {
    lit = it.bucket->data.as_ptr;
    q   = bzla_iter_hashptr_next(&it);
    if (bzla_hashptr_table_get(state->inactive_quantifiers, q)) continue;
    bzla_hashptr_table_add(assumptions, lit)->data.as_ptr = q;
  }

  i = 0;
  while (true)
  {
    ++i;
    qlog("\nGround check: %zu (%u assumptions): ", i, assumptions->count);

    bzla_reset_incremental_usage(bzla);
    bzla_iter_hashptr_init(&it, assumptions);
    while (bzla_iter_hashptr_has_next(&it))
    {
      lit = bzla_iter_hashptr_next(&it);
      bzla_assume_exp(bzla, lit);
    }

    res = bzla->slv->api.sat(bzla->slv);

    if (res == BZLA_RESULT_SAT)
    {
      qlog("sat\n");
      break;
    }
    else
    {
      qlog("unsat\n");
      bzla->last_sat_result = BZLA_RESULT_UNSAT;  // hack

      bool failed = false;
      bzla_iter_hashptr_init(&it, assumptions);
      while (bzla_iter_hashptr_has_next(&it))
      {
        q   = it.bucket->data.as_ptr;
        lit = bzla_iter_hashptr_next(&it);
        if (bzla_failed_exp(bzla, lit))
        {
          qlog("  failed: %s (instance: %s)\n",
               bzla_util_node2string(q),
               bzla_util_node2string(find_backref(state, q)));
          bzla_hashptr_table_remove(assumptions, lit, 0, 0);
          failed = true;
        }
      }

#if 0
      failed = false;
      bzla_iter_hashptr_init (&it, assumptions);
      while (bzla_iter_hashptr_has_next (&it))
      {
        q   = it.bucket->data.as_ptr;
        lit = bzla_iter_hashptr_next (&it);

        bzla_reset_incremental_usage (bzla);
        bzla_assume_exp (bzla, lit);

        res = bzla->slv->api.sat (bzla->slv);
        if (res == BZLA_RESULT_UNSAT)
        {
          bzla->last_sat_result = BZLA_RESULT_UNSAT;  // hack
          if (bzla_failed_exp (bzla, lit))
          {
            log ("  failed: %s (instance: %s)\n",
                 bzla_util_node2string (q),
                 bzla_util_node2string (find_backref (state, q)));
            bzla_hashptr_table_remove (assumptions, lit, 0, 0);
            set_inactive (state, q);
            failed = true;
          }
        }
      }
#endif

      if (!failed)
      {
        break;
      }

#if 0
      bool failed = false;
      bzla_iter_hashptr_init(&it, assumptions);
      while (bzla_iter_hashptr_has_next(&it))
      {
        q = it.bucket->data.as_ptr;
        lit = bzla_iter_hashptr_next(&it);

        if (bzla_failed_exp(bzla, lit))
        {
          log("  failed: %s (instance: %s)\n", bzla_util_node2string(q), bzla_util_node2string(find_backref(state, q)));
          bzla_hashptr_table_remove(assumptions, lit, 0, 0);
          failed = true;
        }
      }

      /* No assumption failed, ground formulas are unsat. */
      if (!failed)
      {
        break;
      }
#endif
    }
  }

  bzla_hashptr_table_delete(assumptions);
  return res;
}

static BzlaSolverResult
check_quantifiers(BzlaQuantSolver *slv)
{
  bool done;
  BzlaSolverResult res;
  QuantSolverState *state = slv->state;

  if (!state)
  {
    slv->bzla->slv = 0;
    Bzla *solver   = bzla_clone(slv->bzla);
    bzla_set_msg_prefix(solver, "quant");
    bzla_opt_set(solver, BZLA_OPT_INCREMENTAL, 1);
    bzla_opt_set(solver, BZLA_OPT_MODEL_GEN, 1);
    slv->bzla->slv = (BzlaSolver *) slv;
    solver->slv    = bzla_new_fun_solver(solver);
    state          = new_quant_solver_state(solver);
    slv->state     = state;
  }

  compute_variable_dependencies(state);

  while (true)
  {
    // bzla_reset_incremental_usage (state->bzla);
    // res = state->bzla->slv->api.sat (state->bzla->slv);
    res = check_ground_formulas(state);
    if (res == BZLA_RESULT_SAT)
    {
      qlog("\n");
      get_active_quantifiers(state);
      state->added_lemma = false;

      done = check_active_quantifiers(state);

      if (done && !state->added_lemma)
      {
        res = BZLA_RESULT_SAT;
        break;
      }

      if (!state->added_lemma)
      {
        BZLA_MSG(state->bzla->msg, 1, "no new lemmas added");
        qlog("** No new lemmas added\n");
        res = BZLA_RESULT_UNKNOWN;
        break;
      }
    }
    else
    {
      res = BZLA_RESULT_UNSAT;
      break;
    }
  }

  return res;
}

///////////////////////////////////////////////////////////////////////////////

static BzlaSolverResult
check_sat_quant_solver(BzlaQuantSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_QUANT_SOLVER_KIND);
  assert(slv->bzla);
  assert(slv->bzla->slv == (BzlaSolver *) slv);

  BzlaSolverResult res;

  BZLA_ABORT(bzla_opt_get(slv->bzla, BZLA_OPT_INCREMENTAL),
             "incremental mode not supported for BV");

  res = check_quantifiers(slv);
  return res;
}

static BzlaQuantSolver *
clone_quant_solver(Bzla *clone, Bzla *bzla, BzlaNodeMap *exp_map)
{
  (void) clone;
  (void) bzla;
  (void) exp_map;
  return 0;
}

static void
delete_quant_solver(BzlaQuantSolver *slv)
{
  assert(slv);
  assert(slv->kind == BZLA_QUANT_SOLVER_KIND);
  assert(slv->bzla);

  Bzla *bzla;

  bzla = slv->bzla;
  delete_quant_solver_state(slv->state);
  BZLA_DELETE(bzla->mm, slv);
  bzla->slv = 0;
}

static void
generate_model_quant_solver(BzlaQuantSolver *slv,
                            bool model_for_all_nodes,
                            bool reset)
{
  (void) slv;
  (void) model_for_all_nodes;
  (void) reset;
}

static void
print_stats_quant_solver(BzlaQuantSolver *slv)
{
  (void) slv;
}

static void
print_time_stats_quant_solver(BzlaQuantSolver *slv)
{
  (void) slv;
}

static void
print_model_quant_solver(BzlaQuantSolver *slv, const char *format, FILE *file)
{
  (void) slv;
  (void) format;
  (void) file;
}

BzlaSolver *
bzla_new_quantifier_solver(Bzla *bzla)
{
  assert(bzla);

  BzlaQuantSolver *slv;

  BZLA_CNEW(bzla->mm, slv);

  slv->kind      = BZLA_QUANT_SOLVER_KIND;
  slv->bzla      = bzla;
  slv->api.clone = (BzlaSolverClone) clone_quant_solver;
  slv->api.delet = (BzlaSolverDelete) delete_quant_solver;
  slv->api.sat   = (BzlaSolverSat) check_sat_quant_solver;
  slv->api.generate_model =
      (BzlaSolverGenerateModel) generate_model_quant_solver;
  slv->api.print_stats = (BzlaSolverPrintStats) print_stats_quant_solver;
  slv->api.print_time_stats =
      (BzlaSolverPrintTimeStats) print_time_stats_quant_solver;
  slv->api.print_model = (BzlaSolverPrintModel) print_model_quant_solver;

  BZLA_MSG(bzla->msg, 1, "enabled quant engine");

  return (BzlaSolver *) slv;
}
