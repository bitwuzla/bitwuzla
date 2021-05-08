/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasynth.h"

#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlamodel.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlapartgen.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

BZLA_DECLARE_STACK(BzlaBitVectorTuplePtr, BzlaBitVectorTuple *);
BZLA_DECLARE_STACK(BzlaIntHashTablePtr, BzlaIntHashTable *);

typedef BzlaNode *(*BzlaUnOp)(Bzla *, BzlaNode *);
typedef BzlaNode *(*BzlaBinOp)(Bzla *, BzlaNode *, BzlaNode *);
typedef BzlaNode *(*BzlaTerOp)(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);

struct Op
{
  bool assoc;
  uint8_t arity;
  union
  {
    BzlaUnOp un;
    BzlaBinOp bin;
    BzlaTerOp ter;
    void *fun;
  };
  const char *name;
  uint32_t num_added;
};

typedef struct Op Op;

struct Candidates
{
  BzlaVoidPtrStack exps;
  BzlaIntStack nexps_level;
  uint32_t nnullary;
  uint32_t nunary;
  uint32_t nbinary;
  uint32_t nternary;
  uint32_t nexps;
};

typedef struct Candidates Candidates;

struct BzlaCartProdIterator
{
  BzlaSortId cur_sort;
  BzlaIntHashTable *e0_exps;
  BzlaIntHashTable *e1_exps;

  uint32_t e0_cur_pos;
  uint32_t e1_cur_pos;
  BzlaNodePtrStack *e0_stack;
  BzlaNodePtrStack *e1_stack;

  BzlaNode *tuple[2];
};

typedef struct BzlaCartProdIterator BzlaCartProdIterator;

static void
init_next_sort(BzlaCartProdIterator *it)
{
  uint32_t i, key;
  BzlaHashTableData *d;

  if (!it->cur_sort)
    i = 0;
  else
  {
    assert(bzla_hashint_table_contains(it->e0_exps, it->cur_sort));
    i = bzla_hashint_table_get_pos(it->e0_exps, it->cur_sort) + 1;
  }

  it->e0_cur_pos = 0;
  it->e1_cur_pos = 0;

  for (; i < it->e0_exps->size; i++)
  {
    key = it->e0_exps->keys[i];
    if (key)
    {
      it->cur_sort = key;

      /* set expression stacks */
      it->e0_stack = it->e0_exps->data[i].as_ptr;

      d = bzla_hashint_map_get(it->e1_exps, key);
      if (d)
        it->e1_stack = d->as_ptr;
      else
        break;
      return;
    }
  }
  it->cur_sort = 0;
}

void
bzla_init_cart_prod_iterator(BzlaCartProdIterator *it,
                             BzlaIntHashTable *e0_exps,
                             BzlaIntHashTable *e1_exps)
{
  assert(e0_exps);
  assert(e1_exps);

  it->e0_exps  = e0_exps;
  it->e1_exps  = e1_exps;
  it->cur_sort = 0;
  it->e0_stack = 0;
  it->e1_stack = 0;
  init_next_sort(it);
}

BzlaNode **
bzla_next_cart_prod_iterator(BzlaCartProdIterator *it)
{
  assert(it->e0_stack);
  assert(it->e1_stack);
  assert(it->e0_cur_pos < BZLA_COUNT_STACK(*it->e0_stack));
  assert(it->e1_cur_pos < BZLA_COUNT_STACK(*it->e1_stack));

  it->tuple[1] = BZLA_PEEK_STACK(*it->e1_stack, it->e1_cur_pos);
  it->tuple[0] = BZLA_PEEK_STACK(*it->e0_stack, it->e0_cur_pos);

  if (it->e1_cur_pos < BZLA_COUNT_STACK(*it->e1_stack)) it->e1_cur_pos++;

  if (it->e1_cur_pos >= BZLA_COUNT_STACK(*it->e1_stack))
  {
    it->e1_cur_pos = 0;
    it->e0_cur_pos++;
  }
  if (it->e0_cur_pos >= BZLA_COUNT_STACK(*it->e0_stack)) init_next_sort(it);
  return it->tuple;
}

bool
bzla_has_next_cart_prod_iterator(BzlaCartProdIterator *it)
{
  return it->cur_sort != 0;
}

/* ------------------------------------------------------------------------- */

static void
collect_exps_post_order(Bzla *bzla,
                        BzlaNode *roots[],
                        uint32_t nroots,
                        BzlaIntHashTable *value_in_map,
                        BzlaNodePtrStack *exps,
                        BzlaNodePtrStack *cone,
                        BzlaIntHashTable *cone_hash)
{
  assert(bzla);
  assert(roots);
  assert(nroots);
  assert(value_in_map);
  assert(exps);
  assert(cone);

  uint32_t i;
  int32_t j;
  BzlaNode *cur, *real_cur, *var = 0;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;
  BzlaNodeIterator it;

  mm    = bzla->mm;
  cache = bzla_hashint_map_new(mm);

  /* collect exps to evaluate in post-order */
  BZLA_INIT_STACK(mm, visit);
  for (i = 0; i < nroots; i++) BZLA_PUSH_STACK(visit, roots[i]);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(cache, real_cur->id);
    if (!d)
    {
      bzla_hashint_map_add(cache, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);

      /* found variable */
      if (bzla_node_is_param(real_cur)
          && (d = bzla_hashint_map_get(value_in_map, real_cur->id))
          && d->as_int == -1)
      {
        assert(!var);
        var = real_cur;
      }

      if (bzla_node_is_apply(real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BZLA_PUSH_STACK(visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert(!bzla_node_is_fun(real_cur));
      assert(!bzla_node_is_apply(real_cur));
      d->as_int = 1;
      BZLA_PUSH_STACK(*exps, cur);
    }
    else
    {
      BZLA_PUSH_STACK(*exps, cur);
    }
  }

  /* mark cone of variable */
  assert(var);
  BZLA_PUSH_STACK(visit, var);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = BZLA_POP_STACK(visit);
    assert(bzla_node_is_regular(cur));

    if (!bzla_hashint_map_contains(cache, cur->id)
        || bzla_hashint_table_contains(cone_hash, cur->id))
      continue;

    bzla_hashint_table_add(cone_hash, cur->id);
    bzla_iter_parent_init(&it, cur);
    while (bzla_iter_parent_has_next(&it))
      BZLA_PUSH_STACK(visit, bzla_iter_parent_next(&it));
  }

  /* collect exps in cone that need to be evaluated each check */
  for (i = 0; i < nroots; i++)
  {
    cur      = roots[i];
    real_cur = bzla_node_real_addr(cur);
    if (bzla_hashint_table_contains(cone_hash, real_cur->id))
      BZLA_PUSH_STACK(visit, cur);
  }

  bzla_hashint_map_delete(cache);
  cache = bzla_hashint_map_new(mm);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    if (!bzla_hashint_table_contains(cone_hash, real_cur->id))
    {
      BZLA_PUSH_STACK(*cone, cur);
      continue;
    }

    d = bzla_hashint_map_get(cache, real_cur->id);
    if (!d)
    {
      bzla_hashint_map_add(cache, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);

      if (bzla_node_is_apply(real_cur)) continue;

      for (j = real_cur->arity - 1; j >= 0; j--)
        BZLA_PUSH_STACK(visit, real_cur->e[j]);
    }
    else if (!d->as_int)
    {
      assert(!bzla_node_is_fun(real_cur));
      assert(!bzla_node_is_apply(real_cur));
      d->as_int = 1;
      BZLA_PUSH_STACK(*cone, cur);
    }
    else
    {
      BZLA_PUSH_STACK(*cone, cur);
    }
  }

  BZLA_RELEASE_STACK(visit);
  bzla_hashint_map_delete(cache);
}

static BzlaBitVector *
eval_candidate(Bzla *bzla,
               BzlaNode *candidate,
               BzlaBitVectorTuple *value_in,
               BzlaBitVector *value_out,
               BzlaIntHashTable *value_in_map)
{
  assert(bzla);
  assert(candidate);
  assert(value_in);
  assert(value_out);
  assert(value_in_map);

  size_t j;
  int32_t i, pos;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaBitVectorPtrStack arg_stack;
  BzlaMemMgr *mm;
  BzlaBitVector **bv, *result, *inv_result, *a;

  mm    = bzla->mm;
  cache = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, arg_stack);
  BZLA_INIT_STACK(mm, visit);
  BZLA_PUSH_STACK(visit, candidate);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    d = bzla_hashint_map_get(cache, real_cur->id);
    if (!d)
    {
      bzla_hashint_map_add(cache, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);

      if (bzla_node_is_apply(real_cur)) continue;

      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      assert(!bzla_node_is_fun(real_cur));
      //assert(!bzla_node_is_apply(real_cur));

      if (!bzla_node_is_apply(real_cur))
      {
        arg_stack.top -= real_cur->arity;
      }
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BZLA_BV_CONST_NODE:
          result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_cur));
          break;

        case BZLA_APPLY_NODE:
        case BZLA_PARAM_NODE:
        case BZLA_VAR_NODE:
          assert(bzla_hashint_map_get(value_in_map, real_cur->id));
          pos = bzla_hashint_map_get(value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            assert(value_out);
            assert(!candidate);
            result = bzla_bv_copy(mm, value_out);
            assert(bzla_node_bv_get_width(real_cur->bzla, real_cur)
                   == bzla_bv_get_width(value_out));
          }
          else
            result = bzla_bv_copy(mm, value_in->bv[pos]);
          break;

        case BZLA_BV_SLICE_NODE:
          result = bzla_bv_slice(mm,
                                 bv[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
          break;

        case BZLA_BV_AND_NODE: result = bzla_bv_and(mm, bv[0], bv[1]); break;

        case BZLA_BV_EQ_NODE: result = bzla_bv_eq(mm, bv[0], bv[1]); break;

        case BZLA_BV_ADD_NODE: result = bzla_bv_add(mm, bv[0], bv[1]); break;

        case BZLA_BV_MUL_NODE: result = bzla_bv_mul(mm, bv[0], bv[1]); break;

        case BZLA_BV_ULT_NODE: result = bzla_bv_ult(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLT_NODE: result = bzla_bv_slt(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLL_NODE: result = bzla_bv_sll(mm, bv[0], bv[1]); break;

        case BZLA_BV_SRL_NODE: result = bzla_bv_srl(mm, bv[0], bv[1]); break;

        case BZLA_BV_UDIV_NODE: result = bzla_bv_udiv(mm, bv[0], bv[1]); break;

        case BZLA_BV_UREM_NODE: result = bzla_bv_urem(mm, bv[0], bv[1]); break;

        case BZLA_BV_CONCAT_NODE:
          result = bzla_bv_concat(mm, bv[0], bv[1]);
          break;

        case BZLA_EXISTS_NODE:
        case BZLA_FORALL_NODE: result = bzla_bv_copy(mm, bv[1]); break;

        default:
          assert(real_cur->kind == BZLA_COND_NODE);
          if (bzla_bv_is_true(bv[0]))
            result = bzla_bv_copy(mm, bv[1]);
          else
            result = bzla_bv_copy(mm, bv[2]);
      }

      if (!bzla_node_is_apply(real_cur))
      {
        for (i = 0; i < real_cur->arity; i++) bzla_bv_free(mm, bv[i]);
      }

      d->as_ptr = bzla_bv_copy(mm, result);

    EVAL_EXP_PUSH_RESULT:
      if (bzla_node_is_inverted(cur))
      {
        inv_result = bzla_bv_not(mm, result);
        bzla_bv_free(mm, result);
        result = inv_result;
      }
      BZLA_PUSH_STACK(arg_stack, result);
    }
    else
    {
      result = bzla_bv_copy(mm, d->as_ptr);
      goto EVAL_EXP_PUSH_RESULT;
    }
  }

  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    bzla_bv_free(mm, a);
  }
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(arg_stack);
  bzla_hashint_map_delete(cache);

  return result;
}

static BzlaBitVector *
eval_exps(Bzla *bzla,
          BzlaNode *exps[],
          uint32_t nexps,
          BzlaIntHashTable *value_cache,
          BzlaIntHashTable *cone_hash,
          BzlaNode *candidate,
          BzlaBitVectorTuple *value_in,
          BzlaBitVector *value_out,
          BzlaIntHashTable *value_in_map)
{
  assert(bzla);
  assert(exps);
  assert(nexps);

  size_t j;
  uint32_t i, k;
  int32_t pos;
  BzlaNode *cur, *real_cur;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  BzlaBitVectorPtrStack arg_stack;
  BzlaMemMgr *mm;
  BzlaBitVector **bv, *result, *inv_result, *a;

  mm    = bzla->mm;
  cache = bzla_hashint_map_new(mm);

  BZLA_INIT_STACK(mm, arg_stack);
  for (i = 0; i < nexps; i++)
  {
    cur      = exps[i];
    real_cur = bzla_node_real_addr(cur);
    assert(!bzla_node_is_fun(real_cur));
    assert(!bzla_node_is_apply(real_cur));

    d = bzla_hashint_map_get(cache, real_cur->id);
    if (d)
    {
      result = bzla_bv_copy(mm, d->as_ptr);
    }
    else if (cone_hash && !bzla_hashint_table_contains(cone_hash, real_cur->id))
    {
      assert(value_cache);
      d = bzla_hashint_map_get(value_cache, real_cur->id);
      assert(d);
      result = bzla_bv_copy(mm, d->as_ptr);
    }
    else
    {
      assert(BZLA_COUNT_STACK(arg_stack) >= real_cur->arity);

      arg_stack.top -= real_cur->arity;
      bv = arg_stack.top;

      switch (real_cur->kind)
      {
        case BZLA_BV_CONST_NODE:
          result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_cur));
          break;

        case BZLA_PARAM_NODE:
        case BZLA_VAR_NODE:
          assert(bzla_hashint_map_get(value_in_map, real_cur->id));
          pos = bzla_hashint_map_get(value_in_map, real_cur->id)->as_int;
          /* initial signature computation */
          if (pos == -1)
          {
            if (candidate)
            {
              result = eval_candidate(
                  bzla, candidate, value_in, value_out, value_in_map);
            }
            else
            {
              assert(value_out);
              result = bzla_bv_copy(mm, value_out);
              assert(bzla_node_bv_get_width(real_cur->bzla, real_cur)
                     == bzla_bv_get_width(value_out));
            }
          }
          else
            result = bzla_bv_copy(mm, value_in->bv[pos]);
          break;

        case BZLA_BV_SLICE_NODE:
          result = bzla_bv_slice(mm,
                                 bv[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
          break;

        case BZLA_BV_AND_NODE: result = bzla_bv_and(mm, bv[0], bv[1]); break;

        case BZLA_BV_EQ_NODE: result = bzla_bv_eq(mm, bv[0], bv[1]); break;

        case BZLA_BV_ADD_NODE: result = bzla_bv_add(mm, bv[0], bv[1]); break;

        case BZLA_BV_MUL_NODE: result = bzla_bv_mul(mm, bv[0], bv[1]); break;

        case BZLA_BV_ULT_NODE: result = bzla_bv_ult(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLT_NODE: result = bzla_bv_slt(mm, bv[0], bv[1]); break;

        case BZLA_BV_SLL_NODE: result = bzla_bv_sll(mm, bv[0], bv[1]); break;

        case BZLA_BV_SRL_NODE: result = bzla_bv_srl(mm, bv[0], bv[1]); break;

        case BZLA_BV_UDIV_NODE: result = bzla_bv_udiv(mm, bv[0], bv[1]); break;

        case BZLA_BV_UREM_NODE: result = bzla_bv_urem(mm, bv[0], bv[1]); break;

        case BZLA_BV_CONCAT_NODE:
          result = bzla_bv_concat(mm, bv[0], bv[1]);
          break;

        case BZLA_EXISTS_NODE:
        case BZLA_FORALL_NODE: result = bzla_bv_copy(mm, bv[1]); break;

        default:
          assert(real_cur->kind == BZLA_COND_NODE);
          if (bzla_bv_is_true(bv[0]))
            result = bzla_bv_copy(mm, bv[1]);
          else
            result = bzla_bv_copy(mm, bv[2]);
      }

      for (k = 0; k < real_cur->arity; k++) bzla_bv_free(mm, bv[k]);

      d         = bzla_hashint_map_add(cache, real_cur->id);
      d->as_ptr = bzla_bv_copy(mm, result);
      if (!cone_hash)
      {
        assert(value_cache);
        bzla_hashint_map_add(value_cache, real_cur->id)->as_ptr =
            bzla_bv_copy(mm, result);
      }
    }
    if (bzla_node_is_inverted(cur))
    {
      inv_result = bzla_bv_not(mm, result);
      bzla_bv_free(mm, result);
      result = inv_result;
    }
    BZLA_PUSH_STACK(arg_stack, result);
  }

  /* merge results of multiple roots */
  result = BZLA_PEEK_STACK(arg_stack, 0);
  for (i = 1; i < BZLA_COUNT_STACK(arg_stack); i++)
  {
    a      = result;
    result = bzla_bv_concat(mm, a, BZLA_PEEK_STACK(arg_stack, i));
    bzla_bv_free(mm, a);
    bzla_bv_free(mm, BZLA_PEEK_STACK(arg_stack, i));
  }

  for (j = 0; j < cache->size; j++)
  {
    a = cache->data[j].as_ptr;
    if (!a) continue;
    bzla_bv_free(mm, a);
  }
  bzla_hashint_map_delete(cache);
  BZLA_RELEASE_STACK(arg_stack);

  return result;
}

/* Add expression 'exp' to expression candidates 'candidates' at level
 * 'exp_size'. */
static void
add_exp(Bzla *bzla, uint32_t exp_size, Candidates *candidates, BzlaNode *exp)
{
  assert(exp_size > 0);
  assert(candidates);

  BzlaIntHashTable *sorted_exps;
  BzlaHashTableData *d;
  BzlaSortId sort;
  BzlaNodePtrStack *exps;
  BzlaMemMgr *mm;

  mm   = bzla->mm;
  sort = bzla_node_real_addr(exp)->sort_id;

  if (exp_size >= BZLA_COUNT_STACK(candidates->exps))
  {
    sorted_exps = bzla_hashint_map_new(mm);
    BZLA_PUSH_STACK(candidates->exps, sorted_exps);
    assert(exp_size == BZLA_COUNT_STACK(candidates->exps) - 1);
  }
  else
    sorted_exps = BZLA_PEEK_STACK(candidates->exps, exp_size);

  d = bzla_hashint_map_get(sorted_exps, sort);
  if (d)
    exps = d->as_ptr;
  else
  {
    BZLA_CNEW(mm, exps);
    BZLA_INIT_STACK(mm, *exps);
    bzla_hashint_map_add(sorted_exps, sort)->as_ptr = exps;
  }
  BZLA_PUSH_STACK(*exps, exp);
  candidates->nexps++;
  switch (bzla_node_real_addr(exp)->arity)
  {
    case 0: candidates->nnullary++; break;
    case 1: candidates->nunary++; break;
    case 2: candidates->nbinary++; break;
    default:
      assert(bzla_node_real_addr(exp)->arity == 3);
      candidates->nternary++;
      break;
  }
  if (exp_size >= BZLA_COUNT_STACK(candidates->nexps_level))
    BZLA_PUSH_STACK(candidates->nexps_level, 0);
  candidates->nexps_level.start[exp_size]++;
}

static BzlaBitVectorTuple *
create_signature_exp(Bzla *bzla,
                     BzlaNode *exp,
                     BzlaBitVectorTuple *value_in[],
                     BzlaBitVector *value_out[],
                     uint32_t nvalues,
                     BzlaIntHashTable *value_in_map)
{
  uint32_t i;
  BzlaBitVectorTuple *inputs, *sig;
  BzlaBitVector *output, *res;
  BzlaMemMgr *mm;

  mm  = bzla->mm;
  sig = bzla_bv_new_tuple(bzla->mm, nvalues);

  for (i = 0; i < nvalues; i++)
  {
    inputs = value_in[i];
    output = value_out[i];
    res    = eval_candidate(bzla, exp, inputs, output, value_in_map);
    bzla_bv_add_to_tuple(mm, sig, res, i);
    bzla_bv_free(mm, res);
  }
  return sig;
}

static bool
check_signature_exps(Bzla *bzla,
                     BzlaNode *exps[],
                     uint32_t nexps,
                     BzlaIntHashTable *value_caches[],
                     BzlaIntHashTable *cone_hash,
                     BzlaNode *exp,
                     BzlaBitVectorTuple *value_in[],
                     BzlaBitVector *value_out[],
                     uint32_t nvalues,
                     BzlaIntHashTable *value_in_map,
                     BzlaBitVectorTuple **sig,
                     uint32_t *num_matches,
                     BzlaBitVector **matchbv)
{
  bool is_equal = true;
  uint32_t i = 0, nmatches = 0;
  BzlaBitVectorTuple *inputs;
  BzlaBitVector *output, *res, *bv;
  BzlaMemMgr *mm;

  mm = bzla->mm;

  if (sig) *sig = bzla_bv_new_tuple(mm, nvalues);

  if (matchbv) bv = bzla_bv_new(mm, nvalues);

  for (i = 0; i < nvalues; i++)
  {
    inputs = value_in[i];
    output = value_out[i];

    if (nexps)
      res = eval_exps(bzla,
                      exps,
                      nexps,
                      value_caches[i],
                      cone_hash,
                      exp,
                      inputs,
                      output,
                      value_in_map);
    else
      res = eval_candidate(bzla, exp, inputs, output, value_in_map);

    if (bzla_bv_compare(res, output) == 0)
    {
      nmatches++;
      if (matchbv) bzla_bv_set_bit(bv, i, 1);
    }
    else if (is_equal)
      is_equal = false;

    if (sig) bzla_bv_add_to_tuple(mm, *sig, res, i);
    bzla_bv_free(mm, res);
  }
  if (num_matches) *num_matches = nmatches;
  if (matchbv) *matchbv = bv;
  return is_equal;
}

static bool
check_candidate_exps(Bzla *bzla,
                     BzlaNode *exps[],
                     uint32_t nexps,
                     BzlaIntHashTable *value_caches[],
                     BzlaIntHashTable *cone_hash,
                     uint32_t cur_level,
                     BzlaNode *exp,
                     BzlaSortId target_sort,
                     BzlaBitVectorTuple *value_in[],
                     BzlaBitVector *value_out[],
                     uint32_t nvalues,
                     BzlaIntHashTable *value_in_map,
                     Candidates *candidates,
                     BzlaIntHashTable *cache,
                     BzlaPtrHashTable *sigs,
                     BzlaPtrHashTable *sigs_exp,
                     Op *op)
{
  bool found_candidate = false;
  int32_t id;
  BzlaBitVectorTuple *sig = 0, *sig_exp;
  BzlaBitVector *matchbv  = 0;
  BzlaMemMgr *mm;

  id = bzla_node_get_id(exp);
  mm = bzla->mm;

  if (bzla_node_is_bv_const(exp) || bzla_hashint_table_contains(cache, id))
  {
    bzla_node_release(bzla, exp);
    return false;
  }

  if (nexps == 0 || bzla_node_real_addr(exp)->sort_id == target_sort)
  {
    /* check signature for candidate expression (in/out values) */
    sig_exp = create_signature_exp(
        bzla, exp, value_in, value_out, nvalues, value_in_map);

    if (bzla_hashptr_table_get(sigs_exp, sig_exp))
    {
      bzla_bv_free_tuple(mm, sig_exp);
      bzla_node_release(bzla, exp);
      return false;
    }
    bzla_hashptr_table_add(sigs_exp, sig_exp);

    /* check signature for candidate expression w.r.t. formula */
    found_candidate = check_signature_exps(bzla,
                                           exps,
                                           nexps,
                                           value_caches,
                                           cone_hash,
                                           exp,
                                           value_in,
                                           value_out,
                                           nvalues,
                                           value_in_map,
                                           &sig,
                                           0,
                                           &matchbv);
  }

  if (sig && bzla_hashptr_table_get(sigs, sig))
  {
    assert(!found_candidate);
    bzla_bv_free_tuple(mm, sig);
    bzla_bv_free(mm, matchbv);
    bzla_node_release(bzla, exp);
    return false;
  }

  if (matchbv) bzla_bv_free(mm, matchbv);

  if (sig) bzla_hashptr_table_add(sigs, sig);
  bzla_hashint_table_add(cache, id);
  if (op) op->num_added++;
  add_exp(bzla, cur_level, candidates, exp);
  return found_candidate;
}

static inline void
report_stats(Bzla *bzla,
             double start,
             uint32_t cur_level,
             uint32_t num_checks,
             Candidates *candidates)
{
  double delta;
  delta = bzla_util_time_stamp() - start;
  BZLA_MSG(bzla->msg,
           1,
           "level: %u|%u(%u,%u,%u)|%u, %.2f/s, %.2fs, %.2f MiB",
           cur_level,
           candidates->nexps,
           candidates->nnullary,
           candidates->nbinary,
           candidates->nternary,
           num_checks,
           num_checks / delta,
           delta,
           (float) bzla->mm->allocated / 1024 / 1024);
}

static void
report_op_stats(Bzla *bzla, Op ops[], uint32_t nops)
{
  uint32_t i;
  for (i = 0; i < nops; i++)
    BZLA_MSG(bzla->msg, 1, "%s: %u", ops[i].name, ops[i].num_added);
}

#define CHECK_CANDIDATE(exp)                                            \
  {                                                                     \
    found_candidate = check_candidate_exps(bzla,                        \
                                           trav_cone.start,             \
                                           BZLA_COUNT_STACK(trav_cone), \
                                           value_caches.start,          \
                                           cone_hash,                   \
                                           cur_level,                   \
                                           exp,                         \
                                           target_sort,                 \
                                           value_in,                    \
                                           value_out,                   \
                                           nvalues,                     \
                                           value_in_map,                \
                                           &candidates,                 \
                                           cache,                       \
                                           sigs,                        \
                                           sigs_exp,                    \
                                           &ops[i]);                    \
    num_checks++;                                                       \
    if (num_checks % 10000 == 0)                                        \
      report_stats(bzla, start, cur_level, num_checks, &candidates);    \
    if (num_checks % 1000 == 0 && bzla_terminate(bzla))                 \
    {                                                                   \
      BZLA_MSG(bzla->msg, 1, "terminate");                              \
      goto DONE;                                                        \
    }                                                                   \
    if (found_candidate || num_checks >= max_checks) goto DONE;         \
  }

static BzlaNode *
synthesize(Bzla *bzla,
           BzlaNode *inputs[],
           uint32_t ninputs,
           BzlaBitVectorTuple *value_in[],
           BzlaBitVector *value_out[],
           uint32_t nvalues,
           Op ops[],
           uint32_t nops,
           BzlaNode *consts[],
           uint32_t nconsts,
           BzlaNode *constraints[],
           uint32_t nconstraints,
           BzlaIntHashTable *value_in_map,
           uint32_t max_checks,
           uint32_t max_level,
           BzlaNode *prev_synth)
{
  assert(bzla);
  assert(inputs);
  assert(ninputs > 0);
  assert(value_in);
  assert(value_out);
  assert(nvalues > 0);
  assert(ops);
  assert(nops > 0);
  assert(!nconsts || consts);

  double start;
  bool found_candidate = false, equal;
  uint32_t i, j, k, *tuple, cur_level = 1, num_checks = 0, num_added;
  BzlaNode *exp, **exp_tuple, *result = 0;
  BzlaNodePtrStack *exps, trav_exps, trav_cone;
  Candidates candidates;
  BzlaIntHashTable *cache, *e0_exps, *e1_exps, *e2_exps;
  BzlaPtrHashTable *sigs, *sigs_exp;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;
  BzlaPartitionGenerator pg;
  BzlaCartProdIterator cpit;
  BzlaPtrHashTableIterator it;
  BzlaSortId bool_sort, target_sort;
  BzlaBitVectorPtrStack sig_constraints;
  BzlaBitVector *bv, **tmp_value_out;
  BzlaIntHashTable *value_cache, *cone_hash;
  BzlaIntHashTablePtrStack value_caches;

  start     = bzla_util_time_stamp();
  mm        = bzla->mm;
  bool_sort = bzla_sort_bool(bzla);
  cache     = bzla_hashint_table_new(mm);
  cone_hash = bzla_hashint_table_new(mm);
  sigs      = bzla_hashptr_table_new(
      mm, (BzlaHashPtr) bzla_bv_hash_tuple, (BzlaCmpPtr) bzla_bv_compare_tuple);
  sigs_exp = bzla_hashptr_table_new(
      mm, (BzlaHashPtr) bzla_bv_hash_tuple, (BzlaCmpPtr) bzla_bv_compare_tuple);

  BZLA_INIT_STACK(mm, sig_constraints);
  BZLA_INIT_STACK(mm, trav_exps);
  BZLA_INIT_STACK(mm, trav_cone);
  BZLA_INIT_STACK(mm, value_caches);

  memset(&candidates, 0, sizeof(Candidates));
  BZLA_INIT_STACK(mm, candidates.exps);
  BZLA_PUSH_STACK(candidates.exps, 0);
  BZLA_INIT_STACK(mm, candidates.nexps_level);
  BZLA_PUSH_STACK(candidates.nexps_level, 0);

  target_sort = bzla_sort_bv(bzla, bzla_bv_get_width(value_out[0]));

  /* generate target signature */
  tmp_value_out = value_out;
  if (nconstraints > 0)
  {
    /* collect expressions in constraints in post-order for faster
     * evaluations */
    collect_exps_post_order(bzla,
                            constraints,
                            nconstraints,
                            value_in_map,
                            &trav_exps,
                            &trav_cone,
                            cone_hash);

    for (i = 0; i < nvalues; i++)
    {
      value_cache = bzla_hashint_map_new(mm);
      bv          = eval_exps(bzla,
                     trav_exps.start,
                     BZLA_COUNT_STACK(trav_exps),
                     value_cache,
                     0,
                     0,
                     value_in[i],
                     value_out[i],
                     value_in_map);
      assert(bzla_opt_get(bzla, BZLA_OPT_QUANT_SYNTH) != BZLA_QUANT_SYNTH_ELMR
             || bzla_bv_is_ones(bv));
      BZLA_PUSH_STACK(sig_constraints, bv);
      BZLA_PUSH_STACK(value_caches, value_cache);
    }
    value_out = sig_constraints.start;
    assert(nvalues == BZLA_COUNT_STACK(sig_constraints));
    assert(nvalues == BZLA_COUNT_STACK(value_caches));
  }

  if (prev_synth)
  {
    exp             = bzla_node_copy(bzla, prev_synth);
    found_candidate = check_candidate_exps(bzla,
                                           trav_cone.start,
                                           BZLA_COUNT_STACK(trav_cone),
                                           value_caches.start,
                                           cone_hash,
                                           cur_level,
                                           exp,
                                           target_sort,
                                           value_in,
                                           value_out,
                                           nvalues,
                                           value_in_map,
                                           &candidates,
                                           cache,
                                           sigs,
                                           sigs_exp,
                                           0);
    num_checks++;
    if (num_checks % 10000 == 0)
      report_stats(bzla, start, cur_level, num_checks, &candidates);
    if (found_candidate)
    {
      BZLA_MSG(bzla->msg, 1, "previously synthesized term matches");
      goto DONE;
    }
  }

  /* level 1 checks (inputs) */
  for (i = 0; i < ninputs; i++)
  {
    exp             = bzla_node_copy(bzla, inputs[i]);
    found_candidate = check_candidate_exps(bzla,
                                           trav_cone.start,
                                           BZLA_COUNT_STACK(trav_cone),
                                           value_caches.start,
                                           cone_hash,
                                           cur_level,
                                           exp,
                                           target_sort,
                                           value_in,
                                           value_out,
                                           nvalues,
                                           value_in_map,
                                           &candidates,
                                           cache,
                                           sigs,
                                           sigs_exp,
                                           0);
    num_checks++;
    if (num_checks % 10000 == 0)
      report_stats(bzla, start, cur_level, num_checks, &candidates);
    if (found_candidate) goto DONE;
  }

  /* check for constant function */
  equal = true;
  for (i = 1; i < nvalues; i++)
  {
    if (bzla_bv_compare(tmp_value_out[i - 1], tmp_value_out[i]))
    {
      equal = false;
      break;
    }
  }
  if (equal)
  {
    found_candidate = true;
    exp             = bzla_exp_bv_const(bzla, tmp_value_out[0]);
    add_exp(bzla, 1, &candidates, exp);
    goto DONE;
  }

  /* add constants to level 1 */
  for (i = 0; i < nconsts; i++)
    add_exp(bzla, 1, &candidates, bzla_node_copy(bzla, consts[i]));

#if 0
  /* add the desired outputs as constants to level 1 */
  for (i = 0; i < nvalues; i++)
    {
      exp = bzla_exp_bv_const (bzla, tmp_value_out[i]);
      add_exp (bzla, 1, &candidates, exp);
    }
#endif

  /* level 2+ checks */
  for (cur_level = 2; !max_level || cur_level < max_level; cur_level++)
  {
    /* initialize current level */
    BZLA_PUSH_STACK(candidates.exps, bzla_hashint_map_new(mm));
    assert(cur_level == BZLA_COUNT_STACK(candidates.exps) - 1);
    report_stats(bzla, start, cur_level, num_checks, &candidates);

    num_added = candidates.nexps;
    for (i = 0; i < nops; i++)
    {
      if (ops[i].arity == 1)
      {
        /* use all expressions from previous level and apply unary
         * operators */
        e0_exps = BZLA_PEEK_STACK(candidates.exps, cur_level - 1);
        for (j = 0; j < e0_exps->size; j++)
        {
          if (!e0_exps->keys[j]) continue;
          exps = e0_exps->data[j].as_ptr;
          for (k = 0; k < BZLA_COUNT_STACK(*exps); k++)
          {
            exp = ops[i].un(bzla, BZLA_PEEK_STACK(*exps, k));
            CHECK_CANDIDATE(exp);
          }
        }
      }
      else if (ops[i].arity == 2)
      {
        bzla_init_part_gen(&pg, cur_level, 2, !ops[i].assoc);
        while (bzla_has_next_part_gen(&pg))
        {
          tuple   = bzla_next_part_gen(&pg);
          e0_exps = BZLA_PEEK_STACK(candidates.exps, tuple[0]);
          e1_exps = BZLA_PEEK_STACK(candidates.exps, tuple[1]);

          bzla_init_cart_prod_iterator(&cpit, e0_exps, e1_exps);
          while (bzla_has_next_cart_prod_iterator(&cpit))
          {
            exp_tuple = bzla_next_cart_prod_iterator(&cpit);
            exp       = ops[i].bin(bzla, exp_tuple[0], exp_tuple[1]);
            CHECK_CANDIDATE(exp);
          }
        }
      }
      else if (cur_level > 2)
      {
        assert(ops[i].arity == 3);

        bzla_init_part_gen(&pg, cur_level, 3, true);
        while (bzla_has_next_part_gen(&pg))
        {
          tuple   = bzla_next_part_gen(&pg);
          e0_exps = BZLA_PEEK_STACK(candidates.exps, tuple[0]);
          e1_exps = BZLA_PEEK_STACK(candidates.exps, tuple[1]);
          e2_exps = BZLA_PEEK_STACK(candidates.exps, tuple[2]);

          /* no bool expression in level 'tuple[0]' */
          d = bzla_hashint_map_get(e0_exps, bool_sort);
          if (!d) continue;

          exps = d->as_ptr;
          bzla_init_cart_prod_iterator(&cpit, e1_exps, e2_exps);
          while (bzla_has_next_cart_prod_iterator(&cpit))
          {
            exp_tuple = bzla_next_cart_prod_iterator(&cpit);

            for (j = 0; j < BZLA_COUNT_STACK(*exps); j++)
            {
              exp = ops[i].ter(
                  bzla, BZLA_PEEK_STACK(*exps, j), exp_tuple[0], exp_tuple[1]);
              CHECK_CANDIDATE(exp);
            }
          }
        }
      }
    }
    report_op_stats(bzla, ops, nops);
    /* no more expressions generated */
    if (num_added == candidates.nexps) break;
  }
DONE:
  report_stats(bzla, start, cur_level, num_checks, &candidates);
  report_op_stats(bzla, ops, nops);

  if (found_candidate)
    result = bzla_node_copy(bzla, exp);
  else
  {
    equal = true;
    for (i = 1; i < nvalues; i++)
    {
      if (bzla_bv_compare(tmp_value_out[i - 1], tmp_value_out[i]))
      {
        equal = false;
        break;
      }
    }
    if (equal)
    {
      found_candidate = true;
      result          = bzla_exp_bv_const(bzla, tmp_value_out[0]);
    }
  }

  if (found_candidate)
    BZLA_MSG(bzla->msg,
             1,
             "found candidate after enumerating %u expressions",
             num_checks);
  else
    BZLA_MSG(bzla->msg, 1, "no candidate found");

  /* cleanup */
  for (i = 1; i < BZLA_COUNT_STACK(candidates.exps); i++)
  {
    e0_exps = BZLA_PEEK_STACK(candidates.exps, i);
    for (j = 0; j < e0_exps->size; j++)
    {
      if (!e0_exps->data[j].as_ptr) continue;
      exps = e0_exps->data[j].as_ptr;
      while (!BZLA_EMPTY_STACK(*exps))
        bzla_node_release(bzla, BZLA_POP_STACK(*exps));
      BZLA_RELEASE_STACK(*exps);
      BZLA_DELETE(mm, exps);
    }
    bzla_hashint_map_delete(e0_exps);
  }
  BZLA_RELEASE_STACK(candidates.exps);
  BZLA_RELEASE_STACK(candidates.nexps_level);

  while (!BZLA_EMPTY_STACK(value_caches))
  {
    value_cache = BZLA_POP_STACK(value_caches);
    for (j = 0; j < value_cache->size; j++)
    {
      if (!value_cache->data[j].as_ptr) continue;
      bzla_bv_free(mm, value_cache->data[j].as_ptr);
    }
    bzla_hashint_map_delete(value_cache);
  }
  BZLA_RELEASE_STACK(value_caches);

  while (!BZLA_EMPTY_STACK(sig_constraints))
    bzla_bv_free(mm, BZLA_POP_STACK(sig_constraints));
  BZLA_RELEASE_STACK(sig_constraints);

  bzla_iter_hashptr_init(&it, sigs);
  bzla_iter_hashptr_queue(&it, sigs_exp);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_bv_free_tuple(mm, bzla_iter_hashptr_next(&it));

  bzla_hashptr_table_delete(sigs);
  bzla_hashptr_table_delete(sigs_exp);
  bzla_hashint_table_delete(cache);
  bzla_hashint_table_delete(cone_hash);
  BZLA_RELEASE_STACK(trav_exps);
  BZLA_RELEASE_STACK(trav_cone);

  assert(!result || bzla_node_real_addr(result)->sort_id == target_sort);
  bzla_sort_release(bzla, bool_sort);
  bzla_sort_release(bzla, target_sort);
  return result;
}

#define INIT_OP(ARITY, ASSOC, FPTR) \
  {                                 \
    ops[i].arity     = ARITY;       \
    ops[i].assoc     = ASSOC;       \
    ops[i].fun       = FPTR;        \
    ops[i].num_added = 0;           \
    ops[i].name      = #FPTR;       \
    i += 1;                         \
  }

static uint32_t
init_ops(Bzla *bzla, Op *ops)
{
  uint32_t i = 0;

  INIT_OP(1, false, bzla_exp_bv_not);
  //  INIT_OP (1, false, bzla_neg_exp);
  //  INIT_OP (1, false, bzla_redor_exp);
  //  INIT_OP (1, false, bzla_redxor_exp);
  //  INIT_OP (1, false, bzla_redand_exp);
  //  INIT_OP (1, false, bzla_inc_exp);
  //  INIT_OP (1, false, bzla_dec_exp);

  /* boolean ops */
  INIT_OP(2, false, bzla_exp_bv_ult);
  INIT_OP(2, false, bzla_exp_bv_slt);
  INIT_OP(2, true, bzla_exp_eq);

  /* bv ops */
  if (bzla->ops[BZLA_BV_AND_NODE].cur > 0) INIT_OP(2, true, bzla_exp_bv_and);
  if (bzla->ops[BZLA_BV_ADD_NODE].cur > 0)
  {
    INIT_OP(2, true, bzla_exp_bv_add);
    INIT_OP(2, false, bzla_exp_bv_sub);
  }
  if (bzla->ops[BZLA_BV_MUL_NODE].cur > 0) INIT_OP(2, true, bzla_exp_bv_mul);
  if (bzla->ops[BZLA_BV_UDIV_NODE].cur > 0)
  {
    INIT_OP(2, false, bzla_exp_bv_udiv);
    INIT_OP(2, false, bzla_exp_bv_sdiv);
  }
  if (bzla->ops[BZLA_BV_UREM_NODE].cur > 0)
  {
    INIT_OP(2, false, bzla_exp_bv_urem);
    INIT_OP(2, false, bzla_exp_bv_srem);
    INIT_OP(2, false, bzla_exp_bv_smod);
  }
#if 0
  INIT_OP (2, true,  bzla_ne_exp);
  INIT_OP (2, true,  bzla_xor_exp);
  INIT_OP (2, true,  bzla_xnor_exp);
  INIT_OP (2, true,  bzla_nand_exp);
  INIT_OP (2, true,  bzla_or_exp);
  INIT_OP (2, true,  bzla_nor_exp);
  /* additonal operations */
  INIT_OP (2, true, bzla_uaddo_exp);
  INIT_OP (2, true, bzla_saddo_exp);
  INIT_OP (2, true, bzla_umulo_exp);
  INIT_OP (2, true, bzla_smulo_exp);
  INIT_OP (2, false, bzla_exp_bv_slt);
  INIT_OP (2, false, bzla_ugt_exp);
  INIT_OP (2, false, bzla_sgt_exp);
  INIT_OP (2, false, bzla_ugte_exp);
  INIT_OP (2, false, bzla_sgte_exp);
  INIT_OP (2, false, bzla_exp_bv_sub);
  INIT_OP (2, false, bzla_usubo_exp);
  INIT_OP (2, false, bzla_ssubo_exp);
  INIT_OP (2, false, bzla_exp_bv_udiv);
  INIT_OP (2, false, bzla_exp_bv_sdiv);
  INIT_OP (2, false, bzla_sdivo_exp);
  INIT_OP (2, false, bzla_exp_bv_urem);
  INIT_OP (2, false, bzla_exp_bv_srem);
  INIT_OP (2, false, bzla_exp_bv_smod);
  INIT_OP (2, false, bzla_concat_exp);
#endif
  INIT_OP(3, false, bzla_exp_cond);
  return i;
}

BzlaNode *
bzla_synthesize_term(Bzla *bzla,
                     BzlaNode *params[],
                     uint32_t nparams,
                     BzlaBitVectorTuple *value_in[],
                     BzlaBitVector *value_out[],
                     uint32_t nvalues,
                     BzlaIntHashTable *value_in_map,
                     BzlaNode *constraints[],
                     uint32_t nconstraints,
                     BzlaNode *consts[],
                     uint32_t nconsts,
                     uint32_t max_checks,
                     uint32_t max_level,
                     BzlaNode *prev_synth)
{
  uint32_t nops;
  Op ops[64];
  BzlaNode *result;

  nops = init_ops(bzla, ops);
  assert(nops);

  result = synthesize(bzla,
                      params,
                      nparams,
                      value_in,
                      value_out,
                      nvalues,
                      ops,
                      nops,
                      consts,
                      nconsts,
                      constraints,
                      nconstraints,
                      value_in_map,
                      max_checks,
                      max_level,
                      prev_synth);

  return result;
}
