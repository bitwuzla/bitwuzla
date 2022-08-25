/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlamodel.h"

#include "bzlabeta.h"
#include "bzlaclone.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlarm.h"
#include "utils/bzlahash.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/
/* BV model                                                               */
/*------------------------------------------------------------------------*/

void
bzla_model_delete_bv(Bzla *bzla, BzlaIntHashTable **bv_model)
{
  assert(bzla);
  assert(bv_model);

  BzlaBitVector *bv;
  BzlaNode *cur;
  BzlaIntHashTableIterator it;

  if (!*bv_model) return;

  bzla_iter_hashint_init(&it, *bv_model);
  while (bzla_iter_hashint_has_next(&it))
  {
    bv  = (BzlaBitVector *) (*bv_model)->data[it.cur_pos].as_ptr;
    cur = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));
    bzla_bv_free(bzla->mm, bv);
    bzla_node_release(bzla, cur);
  }
  bzla_hashint_map_delete(*bv_model);
  *bv_model = 0;
}

/*------------------------------------------------------------------------*/

void
bzla_model_init_bv(Bzla *bzla, BzlaIntHashTable **bv_model)
{
  assert(bzla);
  assert(bv_model);

  if (*bv_model) bzla_model_delete_bv(bzla, bv_model);

  *bv_model = bzla_hashint_map_new(bzla->mm);
}

/*------------------------------------------------------------------------*/

BzlaIntHashTable *
bzla_model_clone_bv(Bzla *bzla, BzlaIntHashTable *bv_model, bool inc_ref_cnt)
{
  assert(bzla);
  assert(bv_model);

  BzlaIntHashTable *res;
  BzlaIntHashTableIterator it;
  BzlaNode *exp;

  res =
      bzla_hashint_map_clone(bzla->mm, bv_model, bzla_clone_data_as_bv_ptr, 0);

  bzla_iter_hashint_init(&it, res);
  while (bzla_iter_hashint_has_next(&it))
  {
    exp = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));
    assert(exp);
    if (inc_ref_cnt) bzla_node_copy(bzla, exp);
  }
  return res;
}

/*------------------------------------------------------------------------*/

void
bzla_model_add_to_bv(Bzla *bzla,
                     BzlaIntHashTable *bv_model,
                     BzlaNode *exp,
                     const BzlaBitVector *assignment)
{
  assert(bzla);
  assert(bv_model);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(assignment);

  assert(!bzla_hashint_map_contains(bv_model, bzla_node_real_addr(exp)->id));
  bzla_node_copy(bzla, exp);
  bzla_hashint_map_add(bv_model, bzla_node_real_addr(exp)->id)->as_ptr =
      bzla_bv_copy(bzla->mm, assignment);
}

/*------------------------------------------------------------------------*/

void
bzla_model_remove_from_bv(Bzla *bzla, BzlaIntHashTable *bv_model, BzlaNode *exp)
{
  assert(bzla);
  assert(bv_model);
  assert(exp);

  BzlaHashTableData d;
  uint32_t id;

  id = bzla_node_get_id(exp);
  assert(bzla_hashint_map_contains(bv_model, id));
  bzla_hashint_map_remove(bv_model, id, &d);
  bzla_bv_free(bzla->mm, d.as_ptr);
  bzla_node_release(bzla, exp);
  if (bzla_hashint_map_contains(bv_model, -id))
  {
    bzla_hashint_map_remove(bv_model, id, &d);
    bzla_bv_free(bzla->mm, d.as_ptr);
    bzla_node_release(bzla, exp);
  }
}

/*------------------------------------------------------------------------*/

static void
add_to_fun_model(Bzla *bzla,
                 BzlaIntHashTable *fun_model,
                 BzlaNode *exp,
                 BzlaBitVectorTuple *t,
                 BzlaBitVector *value)
{
  assert(bzla);
  assert(fun_model);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(t);
  assert(value);

  BzlaPtrHashTable *model;
  BzlaPtrHashBucket *b;

  if (bzla_hashint_map_contains(fun_model, exp->id))
    model = bzla_hashint_map_get(fun_model, exp->id)->as_ptr;
  else
  {
    model = bzla_hashptr_table_new(bzla->mm,
                                   (BzlaHashPtr) bzla_bv_hash_tuple,
                                   (BzlaCmpPtr) bzla_bv_compare_tuple);
    bzla_node_copy(bzla, exp);
    bzla_hashint_map_add(fun_model, exp->id)->as_ptr = model;
  }
  /* do not overwrite model if already present (model is computed top-down)
   * and therefore only the top-most 't' with the same assignment
   * needs to be considered */
  if (bzla_hashptr_table_get(model, t)) return;
  b = bzla_hashptr_table_add(model, bzla_bv_copy_tuple(bzla->mm, t));
  b->data.as_ptr = bzla_bv_copy(bzla->mm, value);
}

/*------------------------------------------------------------------------*/

static BzlaBitVector *
get_value_from_fun_model(Bzla *bzla,
                         BzlaIntHashTable *fun_model,
                         BzlaNode *exp,
                         BzlaBitVectorTuple *t)
{
  assert(bzla);
  assert(fun_model);
  assert(exp);
  assert(t);
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_fun(exp));

  BzlaPtrHashTable *model;
  BzlaHashTableData *d;
  BzlaPtrHashBucket *b;

  d = bzla_hashint_map_get(fun_model, exp->id);
  if (!d) return 0;
  model = (BzlaPtrHashTable *) d->as_ptr;
  b     = bzla_hashptr_table_get(model, t);
  if (!b) return 0;
  return bzla_bv_copy(bzla->mm, (BzlaBitVector *) b->data.as_ptr);
}

/*------------------------------------------------------------------------*/

static BzlaBitVectorTuple *
mk_bv_tuple_from_args(Bzla *bzla,
                      BzlaNode *args,
                      BzlaIntHashTable *bv_model,
                      BzlaIntHashTable *fun_model)
{
  uint32_t pos;
  BzlaBitVectorTuple *t;
  BzlaMemMgr *mm;
  BzlaArgsIterator it;
  BzlaNode *arg;
  BzlaBitVector *bv;

  mm = bzla->mm;

  pos = 0;
  t   = bzla_bv_new_tuple(mm, bzla_node_args_get_arity(bzla, args));

  bzla_iter_args_init(&it, args);
  while (bzla_iter_args_has_next(&it))
  {
    arg = bzla_iter_args_next(&it);
    bv  = bzla_model_recursively_compute_assignment(
        bzla, bv_model, fun_model, arg);
    bzla_bv_add_to_tuple(mm, t, bv, pos++);
    bzla_bv_free(mm, bv);
  }

  return t;
}

static void
add_rho_to_model(Bzla *bzla,
                 BzlaNode *fun,
                 BzlaPtrHashTable *rho,
                 BzlaIntHashTable *bv_model,
                 BzlaIntHashTable *fun_model)
{
  BzlaNode *value, *args;
  BzlaBitVectorTuple *t;
  BzlaBitVector *bv_value;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, rho);
  while (bzla_iter_hashptr_has_next(&it))
  {
    value = (BzlaNode *) it.bucket->data.as_ptr;
    args  = bzla_iter_hashptr_next(&it);
    assert(!bzla_node_real_addr(value)->parameterized);
    assert(bzla_node_is_regular(args));
    assert(bzla_node_is_args(args));
    assert(!args->parameterized);

    t        = mk_bv_tuple_from_args(bzla, args, bv_model, fun_model);
    bv_value = bzla_model_recursively_compute_assignment(
        bzla, bv_model, fun_model, value);

    add_to_fun_model(bzla, fun_model, fun, t, bv_value);
    bzla_bv_free(bzla->mm, bv_value);
    bzla_bv_free_tuple(bzla->mm, t);
  }
}

/**
 * Copy model of `fun_with_model` to the model of `fun.
 */
static void
merge_fun_models(Bzla *bzla,
                 BzlaNode *fun,
                 BzlaNode *fun_with_model,
                 BzlaIntHashTable *fun_model)
{
  BzlaBitVectorTuple *t;
  BzlaBitVector *bv_value;
  BzlaPtrHashTableIterator it;
  BzlaHashTableData *d;

  d = bzla_hashint_map_get(fun_model, fun_with_model->id);
  assert(d);
  const BzlaPtrHashTable *model = d->as_ptr;
  bzla_iter_hashptr_init(&it, model);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bv_value = it.bucket->data.as_ptr;
    t        = bzla_iter_hashptr_next(&it);
    add_to_fun_model(bzla, fun_model, fun, t, bv_value);
  }
}

static void
recursively_compute_function_model(Bzla *bzla,
                                   BzlaIntHashTable *bv_model,
                                   BzlaIntHashTable *fun_model,
                                   BzlaNode *fun)
{
  assert(bzla);
  assert(fun_model);
  assert(fun);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_fun(fun));

  bool has_default_value = false;
  int32_t i;
  BzlaNode *value, *cur_fun, *cur;
  BzlaPtrHashTable *static_rho;
  BzlaBitVectorTuple *t;
  BzlaBitVector *bv_value;
  BzlaMemMgr *mm;
  BzlaNodePtrStack stack;

  mm      = bzla->mm;
  cur_fun = fun;
  while (cur_fun)
  {
    assert(bzla_node_is_fun(cur_fun));

    if (bzla_hashint_map_contains(fun_model, cur_fun->id))
    {
      merge_fun_models(bzla, fun, cur_fun, fun_model);
      break;
    }

    if (cur_fun->rho)
    {
      add_rho_to_model(bzla, fun, cur_fun->rho, bv_model, fun_model);
    }

    if (bzla_node_is_lambda(cur_fun)
        && (static_rho = bzla_node_lambda_get_static_rho(cur_fun)))
    {
      add_rho_to_model(bzla, fun, static_rho, bv_model, fun_model);
    }

    if (bzla_node_is_lambda(cur_fun))
    {
      if (bzla_node_lambda_get_static_rho(cur_fun))
      {
        BZLA_INIT_STACK(mm, stack);
        BZLA_PUSH_STACK(stack, bzla_node_binder_get_body(cur_fun));
        cur_fun = 0;
        while (!BZLA_EMPTY_STACK(stack))
        {
          cur = bzla_node_real_addr(BZLA_POP_STACK(stack));

          if (bzla_node_is_fun(cur))
          {
            cur_fun = cur;
            break;
          }

          if (!cur->parameterized || !cur->apply_below) continue;

          for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(stack, cur->e[i]);
        }
        BZLA_RELEASE_STACK(stack);
      }
      else if (bzla_node_is_const_array(cur_fun))
      {
        /* Default value for model. Note, we add a 0-arity tuple to the
         * function model to indicate a default value for all indices. */
        t        = bzla_bv_new_tuple(bzla->mm, 0);
        bv_value = bzla_model_recursively_compute_assignment(
            bzla, bv_model, fun_model, cur_fun->e[1]);
        add_to_fun_model(bzla, fun_model, fun, t, bv_value);
        bzla_bv_free(mm, bv_value);
        bzla_bv_free_tuple(mm, t);
        has_default_value = true;
        cur_fun           = 0;
      }
      else
      {
        /* only compute models for array lambdas */
        cur_fun = 0;
      }
    }
    else if (bzla_node_is_update(cur_fun))
    {
      t = mk_bv_tuple_from_args(bzla, cur_fun->e[1], bv_model, fun_model);
      bv_value = bzla_model_recursively_compute_assignment(
          bzla, bv_model, fun_model, cur_fun->e[2]);

      add_to_fun_model(bzla, fun_model, fun, t, bv_value);
      bzla_bv_free(bzla->mm, bv_value);
      bzla_bv_free_tuple(bzla->mm, t);
      cur_fun = cur_fun->e[0];
    }
    else if (bzla_node_is_fun_cond(cur_fun))
    {
      if (cur_fun->parameterized)
      {
        cur_fun = 0;
        // TODO: print warning that branch cannot be selected
      }
      else
      {
        assert(!bzla_node_real_addr(cur_fun->e[0])->parameterized);
        value    = cur_fun->e[0];
        bv_value = bzla_model_recursively_compute_assignment(
            bzla, bv_model, fun_model, value);

        if (bzla_bv_is_true(bv_value))
          cur_fun = cur_fun->e[1];
        else
        {
          assert(bzla_bv_is_false(bv_value));
          cur_fun = cur_fun->e[2];
        }
        bzla_bv_free(mm, bv_value);
      }
    }
    else
    {
      assert(bzla_node_is_uf(cur_fun));
      cur_fun = 0;
    }
  }

  /* Remove all model entries that are the same as the default value. */
  if (has_default_value)
  {
    BzlaBitVector *default_value;
    BzlaBitVectorTuple *args;
    BzlaPtrHashBucket *b;
    BzlaPtrHashTable *cur_model, *new_model;
    BzlaPtrHashTableIterator it;

    t = bzla_bv_new_tuple(mm, 0);
    assert(bzla_hashint_map_contains(fun_model, fun->id));
    cur_model = bzla_hashint_map_get(fun_model, fun->id)->as_ptr;
    assert(cur_model);
    b = bzla_hashptr_table_get(cur_model, t);
    assert(b);
    default_value = b->data.as_ptr;

    new_model = bzla_hashptr_table_new(mm, cur_model->hash, cur_model->cmp);
    bzla_iter_hashptr_init(&it, cur_model);
    while (bzla_iter_hashptr_has_next(&it))
    {
      bv_value = it.bucket->data.as_ptr;
      args     = bzla_iter_hashptr_next(&it);

      if (bzla_bv_compare(bv_value, default_value) || args->arity == 0)
      {
        bzla_hashptr_table_add(new_model, args)->data.as_ptr = bv_value;
      }
      /* Skip values that are same as 'default_value'. */
      else
      {
        bzla_bv_free(mm, bv_value);
        bzla_bv_free_tuple(mm, args);
      }
    }
    /* Replace model of 'fun' with new cleaned up model. */
    bzla_hashptr_table_delete(cur_model);
    bzla_hashint_map_remove(fun_model, fun->id, 0);
    bzla_hashint_map_add(fun_model, fun->id)->as_ptr = new_model;

    bzla_bv_free_tuple(mm, t);
  }
}

const BzlaPtrHashTable *
bzla_model_get_fun_aux(Bzla *bzla,
                       BzlaIntHashTable *bv_model,
                       BzlaIntHashTable *fun_model,
                       BzlaNode *exp)
{
  assert(bzla);
  assert(fun_model);
  assert(bzla_node_is_regular(exp));

  BzlaHashTableData *d;

  /* Do not use bzla_simplify_exp here! bzla_simplify_exp always simplifies
   * constraints to true (regardless of the actual input assignments).
   * However, when querying assignments, we want to get the actual assignments,
   * depending on the current input assignments. In particular during local
   * search (engines PROP, AIGPROP, SLS), assignment queries may be issued
   * when the current model is non satisfying (all intermediate models during
   * local search are non-satisfying). */
  exp = bzla_node_get_simplified(bzla, exp);

  assert(bzla_node_is_fun(exp));
  d = bzla_hashint_map_get(fun_model, exp->id);

  /* if exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is now
   * a proxy and was therefore regenerated when querying it's assignment via
   * get-value in SMT-LIB v2) */
  if (!d) recursively_compute_function_model(bzla, bv_model, fun_model, exp);
  d = bzla_hashint_map_get(fun_model, exp->id);
  if (!d) return 0;

  return (BzlaPtrHashTable *) d->as_ptr;
}

const BzlaPtrHashTable *
bzla_model_get_fun(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return bzla_model_get_fun_aux(bzla, bzla->bv_model, bzla->fun_model, exp);
}

void
bzla_model_get_array_model(Bzla *bzla,
                           BzlaNode *exp,
                           BzlaNodePtrStack *indices,
                           BzlaNodePtrStack *values,
                           BzlaNode **default_value)
{
  assert(bzla_node_is_array(exp));
  assert(indices);
  assert(values);
  assert(default_value);

  const BzlaPtrHashTable *model = bzla_model_get_fun(bzla, exp);

  if (!model)
  {
    return;
  }

  BzlaBitVectorTuple *tup;
  BzlaBitVector *bv;
  BzlaPtrHashTableIterator it;

  BzlaSortId array_sort = bzla_node_get_sort_id(exp);
  BzlaSortId index_sort = bzla_sort_array_get_index(bzla, array_sort);
  BzlaSortId value_sort = bzla_sort_array_get_element(bzla, array_sort);

  *default_value = 0;

  bzla_iter_hashptr_init(&it, model);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bv  = it.bucket->data.as_ptr;
    tup = bzla_iter_hashptr_next(&it);
    if (tup->arity == 0)
    {
      assert(!*default_value);
      *default_value = bzla_node_mk_value(bzla, value_sort, bv);
    }
    else
    {
      assert(tup->arity == 1);
      BZLA_PUSH_STACK(*indices,
                      bzla_node_mk_value(bzla, index_sort, tup->bv[0]));
      BZLA_PUSH_STACK(*values, bzla_node_mk_value(bzla, value_sort, bv));
    }
  }
}

void
bzla_model_get_fun_model(Bzla *bzla,
                         BzlaNode *exp,
                         BzlaNodePtrStack *args,
                         BzlaNodePtrStack *values)
{
  assert(bzla_sort_is_fun(bzla, bzla_node_get_sort_id(exp)));
  assert(args);
  assert(values);

  const BzlaPtrHashTable *model = bzla_model_get_fun(bzla, exp);

  if (!model)
  {
    return;
  }

  BzlaBitVectorTuple *tup;
  BzlaBitVector *bv;
  BzlaPtrHashTableIterator it;

  BzlaSortId fun_sort      = bzla_node_get_sort_id(exp);
  BzlaSortId domain_sort   = bzla_sort_fun_get_domain(bzla, fun_sort);
  BzlaSortId codomain_sort = bzla_sort_fun_get_codomain(bzla, fun_sort);

  BzlaSort *domain = bzla_sort_get_by_id(bzla, domain_sort);
  bzla_iter_hashptr_init(&it, model);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bv  = it.bucket->data.as_ptr;
    tup = bzla_iter_hashptr_next(&it);
    assert(tup->arity > 0);

    for (size_t i = 0; i < tup->arity; ++i)
    {
      BZLA_PUSH_STACK(
          *args,
          bzla_node_mk_value(bzla, domain->tuple.elements[i]->id, tup->bv[i]));
    }

    BZLA_PUSH_STACK(*values, bzla_node_mk_value(bzla, codomain_sort, bv));
  }
}

/*------------------------------------------------------------------------*/

/**
 * Compute the bit-vector value for `exp`.
 *
 * Requires that the model values of the childen of `exp` already have been
 * computed (no traversal).
 */
static void
compute_bv_value(Bzla *bzla, BzlaIntHashTable *bv_model, BzlaNode *exp)
{
  assert(!bzla_node_is_apply(exp));
  assert(!bzla_node_is_lambda(exp));
  assert(!bzla_node_is_uf(exp));
  assert(!bzla_node_is_update(exp));

  BzlaMemMgr *mm;
  BzlaNode *real_exp, *child;
  BzlaBitVector *bv[3], *result = 0;
  BzlaHashTableData *d;

  mm       = bzla->mm;
  real_exp = bzla_node_real_addr(exp);

  d = bzla_hashint_map_get(bv_model, real_exp->id);
  if (d)
  {
    return;
  }

  if (bzla_node_is_bv_var(real_exp) || bzla_node_is_fun_eq(real_exp))
  {
    result = bzla_model_get_bv_assignment(
        bzla, bzla_node_get_simplified(bzla, real_exp));
  }
  /* if fp var is not synthesized (i.e., does not occur in the formula and
   * is thus not word-blasted), add default bit-vector assignment 0 */
  else if (bzla_node_is_fp_var(real_exp) && !real_exp->av)
  {
    result = bzla_bv_new(
        bzla->mm,
        bzla_sort_fp_get_bv_width(bzla, bzla_node_get_sort_id(real_exp)));
  }
  else if (bzla_node_is_bv_const(real_exp))
  {
    result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_exp));
  }
  else
  {
    for (size_t i = 0; i < real_exp->arity; ++i)
    {
      child = real_exp->e[i];
      d     = bzla_hashint_map_get(bv_model, bzla_node_real_addr(child)->id);
      assert(d);
      bv[i] = bzla_node_is_inverted(child) ? bzla_bv_not(mm, d->as_ptr)
                                           : bzla_bv_copy(mm, d->as_ptr);
    }

    switch (real_exp->kind)
    {
      case BZLA_BV_SLICE_NODE:
        result = bzla_bv_slice(mm,
                               bv[0],
                               bzla_node_bv_slice_get_upper(real_exp),
                               bzla_node_bv_slice_get_lower(real_exp));
        break;
      case BZLA_BV_AND_NODE: result = bzla_bv_and(mm, bv[0], bv[1]); break;
      case BZLA_BV_EQ_NODE: result = bzla_bv_eq(mm, bv[0], bv[1]); break;
      case BZLA_BV_ADD_NODE: result = bzla_bv_add(mm, bv[0], bv[1]); break;
      case BZLA_BV_MUL_NODE: result = bzla_bv_mul(mm, bv[0], bv[1]); break;
      case BZLA_BV_ULT_NODE: result = bzla_bv_ult(mm, bv[0], bv[1]); break;
      case BZLA_BV_SLL_NODE: result = bzla_bv_sll(mm, bv[0], bv[1]); break;
      case BZLA_BV_SLT_NODE: result = bzla_bv_slt(mm, bv[0], bv[1]); break;
      case BZLA_BV_SRL_NODE: result = bzla_bv_srl(mm, bv[0], bv[1]); break;
      case BZLA_BV_UDIV_NODE: result = bzla_bv_udiv(mm, bv[0], bv[1]); break;
      case BZLA_BV_UREM_NODE: result = bzla_bv_urem(mm, bv[0], bv[1]); break;
      case BZLA_BV_CONCAT_NODE:
        result = bzla_bv_concat(mm, bv[0], bv[1]);
        break;
      default:
        assert(bzla_node_is_cond(real_exp));
        result = bzla_bv_is_true(bv[0]) ? bzla_bv_copy(mm, bv[1])
                                        : bzla_bv_copy(mm, bv[2]);
    }

    for (size_t i = 0; i < real_exp->arity; ++i)
    {
      bzla_bv_free(mm, bv[i]);
    }
  }
  assert(result);

  bzla_model_add_to_bv(bzla, bv_model, real_exp, result);
  bzla_bv_free(mm, result);
}

static void
compute_model_values(Bzla *bzla,
                     BzlaIntHashTable *bv_model,
                     BzlaIntHashTable *fun_model,
                     BzlaNode *nodes[],
                     size_t num_nodes)
{
  size_t i;
  BzlaNode *cur;
  BzlaBitVector *bv;

  if (num_nodes == 0) return;

  qsort(
      nodes, num_nodes, sizeof(BzlaNode *), bzla_node_compare_by_id_qsort_asc);

  for (i = 0; i < num_nodes; i++)
  {
    cur = bzla_node_real_addr(nodes[i]);
    assert(!cur->parameterized);
    BZLALOG(3, "generate model for %s", bzla_util_node2string(cur));
    // Skip intermediate update nodes
    if (bzla_node_is_update(cur))
    {
      continue;
    }
    if (bzla_node_is_fun(cur))
    {
      recursively_compute_function_model(bzla, bv_model, fun_model, cur);
    }
    else if (bzla_node_is_apply(cur) || bzla_node_fp_needs_word_blast(bzla, cur)
             || bzla_node_is_quantifier(cur))
    {
      // Generate model for top-level update nodes only
      if (bzla_node_is_apply(cur) && bzla_node_is_update(cur->e[0]))
      {
        recursively_compute_function_model(
            bzla, bv_model, fun_model, cur->e[0]);
      }
      bv = bzla_model_recursively_compute_assignment(
          bzla, bv_model, fun_model, cur);
      bzla_bv_free(bzla->mm, bv);
    }
    else
    {
      compute_bv_value(bzla, bv_model, cur);
    }
  }
}

/* Ensure that all terms in 'exp' have a model value. Collect all terms in
 * 'exp' that don't have a model value and call corresponding
 * recursively_compute_* functions. */
static void
ensure_model(Bzla *bzla,
             BzlaIntHashTable *bv_model,
             BzlaIntHashTable *fun_model,
             BzlaNode *exp)
{
  assert(exp);
  assert(!bzla_node_is_proxy(exp));

  double start;
  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack visit, nodes;
  BzlaIntHashTable *cache;

  start = bzla_util_time_stamp();
  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, nodes);

  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_PUSH_STACK(visit, exp);
  do
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)
        || bzla_hashint_map_contains(bv_model, cur->id)
        || bzla_hashint_map_contains(fun_model, cur->id))
      continue;

    bzla_hashint_table_add(cache, cur->id);

    if (!cur->parameterized && !bzla_node_is_args(cur))
    {
      BZLA_PUSH_STACK(nodes, cur);
    }

    for (i = 0; i < cur->arity; i++)
    {
      BZLA_PUSH_STACK(visit, cur->e[i]);
    }
  } while (!BZLA_EMPTY_STACK(visit));
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);

  compute_model_values(
      bzla, bv_model, fun_model, nodes.start, BZLA_COUNT_STACK(nodes));

  BZLA_RELEASE_STACK(nodes);
  bzla->time.model_gen += bzla_util_time_stamp() - start;
}

/* Note: no need to free returned bit vector,
 *       all bit vectors are maintained via bzla->bv_model */
const BzlaBitVector *
bzla_model_get_bv_aux(Bzla *bzla,
                      BzlaIntHashTable *bv_model,
                      BzlaIntHashTable *fun_model,
                      BzlaNode *exp)
{
  assert(bzla);
  assert(bv_model);
  assert(fun_model);
  assert(exp);

  BzlaBitVector *result;
  BzlaHashTableData *d;

  /* Note: bzla_model_generate generates assignments for all nodes
   *       as non-inverted nodes. Their inverted assignments, however,
   *       are cached (when requested) on demand (see below)! */

  /* Do not use bzla_simplify_exp here! bzla_simplify_exp always simplifies
   * constraints to true (regardless of the actual input assignments).
   * However, when querying assignments, we want to get the actual assignments,
   * depending on the current input assignments. In particular during local
   * search (engines PROP, AIGPROP, SLS), assignment queries may be issued
   * when the current model is non satisfying (all intermediate models during
   * local search are non-satisfying). */
  exp = bzla_node_get_simplified(bzla, exp);

  /* Check if we already generated the assignment of exp
   * -> inverted if exp is inverted */
  if ((d = bzla_hashint_map_get(bv_model, bzla_node_get_id(exp))))
    return d->as_ptr;

  /* If not, check if we already generated the assignment of non-inverted exp
   * (i.e., check if we generated it at all) */
  if (bzla_node_is_inverted(exp))
    d = bzla_hashint_map_get(bv_model, bzla_node_real_addr(exp)->id);

  /* If exp has no assignment, regenerate model in case that it is an exp
   * that previously existed but was simplified (i.e. the original exp is
   * now a proxy and was therefore regenerated when querying it's
   * assignment via get-value in SMT-LIB v2) */
  if (!d)
  {
    ensure_model(bzla, bv_model, fun_model, exp);
    d = bzla_hashint_map_get(bv_model, bzla_node_real_addr(exp)->id);
  }
  if (!d) return 0;

  result = (BzlaBitVector *) d->as_ptr;

  /* Cache assignments of inverted expressions on demand */
  if (bzla_node_is_inverted(exp))
  {
    /* we don't use add_to_bv_model in order to avoid redundant
     * hash table queries and copying/freeing of the resulting bv */
    result = bzla_bv_not(bzla->mm, result);
    bzla_node_copy(bzla, exp);
    bzla_hashint_map_add(bv_model, bzla_node_get_id(exp))->as_ptr = result;
  }

  return result;
}

const BzlaBitVector *
bzla_model_get_bv(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return bzla_model_get_bv_aux(bzla, bzla->bv_model, bzla->fun_model, exp);
}

/*------------------------------------------------------------------------*/
/* Fun model                                                              */
/*------------------------------------------------------------------------*/

static void
delete_fun_model(Bzla *bzla, BzlaIntHashTable **fun_model)
{
  assert(bzla);
  assert(fun_model);

  BzlaBitVectorTuple *tup;
  BzlaBitVector *value;
  BzlaNode *cur;
  BzlaIntHashTableIterator it1;
  BzlaPtrHashTable *t;
  BzlaPtrHashTableIterator it2;

  if (!*fun_model) return;

  bzla_iter_hashint_init(&it1, *fun_model);
  while (bzla_iter_hashint_has_next(&it1))
  {
    t   = (BzlaPtrHashTable *) (*fun_model)->data[it1.cur_pos].as_ptr;
    cur = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it1));
    bzla_iter_hashptr_init(&it2, t);
    while (bzla_iter_hashptr_has_next(&it2))
    {
      value = (BzlaBitVector *) it2.bucket->data.as_ptr;
      tup   = (BzlaBitVectorTuple *) bzla_iter_hashptr_next(&it2);
      bzla_bv_free_tuple(bzla->mm, tup);
      bzla_bv_free(bzla->mm, value);
    }
    bzla_node_release(bzla, cur);
    bzla_hashptr_table_delete(t);
  }
  bzla_hashint_map_delete(*fun_model);
  *fun_model = 0;
}

/*------------------------------------------------------------------------*/

void
bzla_model_init_fun(Bzla *bzla, BzlaIntHashTable **fun_model)
{
  assert(bzla);
  assert(fun_model);

  if (*fun_model) delete_fun_model(bzla, fun_model);

  *fun_model = bzla_hashint_map_new(bzla->mm);
}

/*------------------------------------------------------------------------*/

BzlaIntHashTable *
bzla_model_clone_fun(Bzla *bzla, BzlaIntHashTable *fun_model, bool inc_ref_cnt)
{
  assert(bzla);
  assert(fun_model);

  BzlaIntHashTable *res;
  BzlaIntHashTableIterator it;
  BzlaNode *exp;

  res = bzla_hashint_map_clone(
      bzla->mm, fun_model, bzla_clone_data_as_bv_ptr_htable, 0);

  bzla_iter_hashint_init(&it, res);
  while (bzla_iter_hashint_has_next(&it))
  {
    exp = bzla_node_get_by_id(bzla, bzla_iter_hashint_next(&it));
    assert(exp);
    if (inc_ref_cnt) bzla_node_copy(bzla, exp);
  }
  return res;
}

/*------------------------------------------------------------------------*/
/* Model                                                                  */
/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_model_get_bv_assignment(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(!bzla_node_is_proxy(exp));

  BzlaBitVector *res;

  uint32_t i, j, width;
  int32_t bit;
  bool inv;
  BzlaNode *real_exp;
  BzlaAIGVec *av;
  BzlaAIGMgr *amgr;
  BzlaMemMgr *mm;

  exp      = bzla_node_get_simplified(bzla_node_real_addr(exp)->bzla, exp);
  real_exp = bzla_node_real_addr(exp);
  mm       = bzla->mm;

  if (!real_exp->av)
  {
    if (bzla_node_is_rm(bzla, real_exp))
    {
      return bzla_bv_new(mm, BZLA_RM_BW);
    }
    else if (bzla_node_is_fp(bzla, real_exp))
    {
      return bzla_bv_new(
          mm, bzla_sort_fp_get_bv_width(bzla, bzla_node_get_sort_id(real_exp)));
    }
    return bzla_bv_new(mm, bzla_node_bv_get_width(real_exp->bzla, real_exp));
  }

  amgr  = bzla_get_aig_mgr(real_exp->bzla);
  av    = real_exp->av;
  width = av->width;
  res   = bzla_bv_new(mm, width);
  inv   = bzla_node_is_inverted(exp);

  for (i = 0, j = width - 1; i < width; i++, j--)
  {
    bit = bzla_aig_get_assignment(amgr, av->aigs[j]);
    if (inv) bit *= -1;
    assert(bit == -1 || bit == 1);
    bzla_bv_set_bit(res, i, bit == 1 ? 1 : 0);
  }
  return res;
}

static BzlaBitVector *
get_apply_value(Bzla *bzla,
                BzlaNode *app,
                BzlaNode *fun,
                BzlaIntHashTable *bv_model,
                BzlaIntHashTable *fun_model)
{
  assert(bzla_node_is_apply(app));

  uint32_t i;
  BzlaArgsIterator it;
  BzlaBitVectorTuple *t;
  BzlaNode *arg, *real_arg, *tmp;
  BzlaHashTableData *d;
  BzlaBitVector *bv, *bv_inv, *result;
  BzlaMemMgr *mm;

  mm = bzla->mm;
  t  = bzla_bv_new_tuple(mm, bzla_node_args_get_arity(bzla, app->e[1]));

  i = 0;
  bzla_iter_args_init(&it, app->e[1]);
  while (bzla_iter_args_has_next(&it))
  {
    arg      = bzla_iter_args_next(&it);
    real_arg = bzla_node_real_addr(arg);

    if (bzla_node_is_param(real_arg))
    {
      tmp      = bzla_node_param_get_assigned_exp(real_arg);
      arg      = bzla_node_cond_invert(arg, tmp);
      real_arg = bzla_node_real_addr(arg);
      assert(real_arg);
    }
    assert(bzla_node_is_regular(real_arg));
    assert(!real_arg->parameterized);
    d = bzla_hashint_map_get(bv_model, real_arg->id);

    if (bzla_node_is_apply(real_arg) && !d)
    {
      bv = get_apply_value(bzla, real_arg, real_arg->e[0], bv_model, fun_model);
    }
    else
    {
      assert(d);
      bv = bzla_bv_copy(mm, d->as_ptr);
    }

    if (bzla_node_is_inverted(arg))
    {
      bv_inv = bzla_bv_not(mm, bv);
      bzla_bv_add_to_tuple(mm, t, bv_inv, i);
      bzla_bv_free(mm, bv_inv);
    }
    else
      bzla_bv_add_to_tuple(mm, t, bv, i);
    bzla_bv_free(mm, bv);
    i++;
  }
  /* check if there is already a value for given arguments */
  result = get_value_from_fun_model(bzla, fun_model, fun, t);
  bzla_bv_free_tuple(mm, t);
  return result;
}

/* Note: don't forget to free resulting bit vector! */
BzlaBitVector *
bzla_model_recursively_compute_assignment(Bzla *bzla,
                                          BzlaIntHashTable *bv_model,
                                          BzlaIntHashTable *fun_model,
                                          BzlaNode *exp)
{
  assert(bzla);
  assert(bv_model);
  assert(fun_model);
  assert(exp);

  uint32_t i, num_args;
  BzlaMemMgr *mm;
  BzlaNodePtrStack work_stack, reset, cleanup_expanded;
  BzlaVoidPtrStack arg_stack;
  BzlaNode *cur, *real_cur, *next, *cur_parent;
  BzlaHashTableData *d;
  BzlaIntHashTable *assigned, *expanded;
  BzlaIntHashTable *wblasted;
  BzlaBitVector *result = 0, *inv_result, **e;
  BzlaBitVectorTuple *t;
  BzlaIntHashTable *mark;
  BzlaHashTableData *md;

  mm = bzla->mm;

  /* Return model value if already computed. */
  d = bzla_hashint_map_get(bv_model, bzla_node_real_addr(exp)->id);
  if (d)
  {
    if (bzla_node_is_inverted(exp))
    {
      return bzla_bv_not(mm, d->as_ptr);
    }
    return bzla_bv_copy(mm, d->as_ptr);
  }

  assigned = bzla_hashint_map_new(mm);
  expanded = bzla_hashint_table_new(mm);
  wblasted = bzla_hashint_table_new(mm);

  mark = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, work_stack);
  BZLA_INIT_STACK(mm, arg_stack);
  BZLA_INIT_STACK(mm, reset);
  BZLA_INIT_STACK(mm, cleanup_expanded);

  BZLA_PUSH_STACK(work_stack, exp);
  BZLA_PUSH_STACK(work_stack, 0);

  while (!BZLA_EMPTY_STACK(work_stack))
  {
    cur_parent = BZLA_POP_STACK(work_stack);
    cur        = BZLA_POP_STACK(work_stack);
    real_cur   = bzla_node_real_addr(cur);
    assert(!real_cur->parameterized);

    if (bzla_hashint_map_contains(bv_model, real_cur->id)) goto PUSH_CACHED;

    /* check if we already have an assignment for this function application */
    if (bzla_node_is_lambda(real_cur) && cur_parent
        && bzla_node_is_apply(cur_parent)
        /* if real_cur was assigned by cur_parent, we are not allowed to use
         * a cached result, but instead rebuild cur_parent */
        && (!(d = bzla_hashint_map_get(assigned, real_cur->id))
            || d->as_ptr != cur_parent))
    {
      num_args = bzla_node_args_get_arity(bzla, cur_parent->e[1]);
      e        = (BzlaBitVector **) arg_stack.top - num_args;

      t = bzla_bv_new_tuple(mm, num_args);
      for (i = 0; i < num_args; i++)
        bzla_bv_add_to_tuple(mm, t, e[i], num_args - 1 - i);

      /* check if there is already a value for given arguments */
      result = get_value_from_fun_model(bzla, fun_model, cur_parent->e[0], t);
      bzla_bv_free_tuple(mm, t);

      if (result) goto PUSH_RESULT;
    }

    md = bzla_hashint_map_get(mark, real_cur->id);
    if (!md)
    {
      /* add assignment of bv var to model (creates new assignment, if
       * it doesn't have one) */
      if (bzla_node_is_bv_var(real_cur) || bzla_node_is_fun_eq(real_cur)
          || bzla_node_is_quantifier(real_cur))
      {
        result = bzla_model_get_bv_assignment(
            bzla, bzla_node_get_simplified(bzla, real_cur));
        goto CACHE_AND_PUSH_RESULT;
      }
      /* if fp var is not synthesized (i.e., does not occur in the formula and
       * is thus not word-blasted), add default bit-vector assignment 0 */
      else if (bzla_node_is_fp_var(real_cur) && !real_cur->av)
      {
        result = bzla_bv_new(
            bzla->mm,
            bzla_sort_fp_get_bv_width(bzla, bzla_node_get_sort_id(real_cur)));
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (bzla_node_is_bv_const(real_cur))
      {
        result = bzla_bv_copy(mm, bzla_node_bv_const_get_bits(real_cur));
        goto CACHE_AND_PUSH_RESULT;
      }
      /* substitute param with its assignment */
      else if (bzla_node_is_param(real_cur))
      {
        assert(0);
        next = bzla_node_param_get_assigned_exp(real_cur);
        assert(next);
        next = bzla_node_cond_invert(cur, next);
        BZLA_PUSH_STACK(work_stack, next);
        BZLA_PUSH_STACK(work_stack, cur_parent);
        continue;
      }

      BZLA_PUSH_STACK(work_stack, cur);
      BZLA_PUSH_STACK(work_stack, cur_parent);
      md = bzla_hashint_map_add(mark, real_cur->id);

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (bzla_node_is_cond(real_cur))
      {
        md->as_int = 2;
        BZLA_PUSH_STACK(work_stack, real_cur->e[0]);
        BZLA_PUSH_STACK(work_stack, real_cur);
      }
      else if (bzla_node_is_update(real_cur))
      {
        BZLA_PUSH_STACK(work_stack, real_cur->e[0]);
        BZLA_PUSH_STACK(work_stack, cur_parent);
        BZLA_PUSH_STACK(work_stack, real_cur->e[1]);
        BZLA_PUSH_STACK(work_stack, real_cur);
        BZLA_PUSH_STACK(work_stack, real_cur->e[2]);
        BZLA_PUSH_STACK(work_stack, real_cur);
      }
      else if (bzla_node_is_apply(real_cur)
               && bzla_node_is_lambda(real_cur->e[0]))
      {
        next = bzla_beta_reduce_full(bzla, real_cur, 0);
        assert(!bzla_node_real_addr(next)->parameterized);
        next = bzla_node_cond_invert(cur, next);
        BZLA_PUSH_STACK(work_stack, next);
        BZLA_PUSH_STACK(work_stack, cur_parent);
        BZLA_PUSH_STACK(cleanup_expanded, next);
        bzla_hashint_table_add(expanded, real_cur->id);
      }
      /* For FP terms we need to ensure that we have word blasted them. */
      else if (!bzla_node_is_apply(real_cur)
               && bzla_node_fp_needs_word_blast(bzla, real_cur))
      {
        next = bzla_fp_word_blast(bzla, real_cur);
        assert(next);
        BZLA_PUSH_STACK(work_stack, next);
        BZLA_PUSH_STACK(work_stack, cur_parent);
        bzla_hashint_table_add(wblasted, real_cur->id);
      }
      else
      {
        for (i = 0; i < real_cur->arity; i++)
        {
          BZLA_PUSH_STACK(work_stack, real_cur->e[i]);
          BZLA_PUSH_STACK(work_stack, real_cur);
        }
      }
    }
    else if (md->as_int == 0 || md->as_int == 2)
    {
      assert(!bzla_node_is_param(real_cur));
      assert(real_cur->arity <= BZLA_NODE_MAX_CHILDREN);
      assert(!bzla_node_is_lambda(real_cur));

      /* Check if real_cur is an expanded FP fucntion application. */
      if (bzla_hashint_table_contains(expanded, real_cur->id))
      {
        result = BZLA_POP_STACK(arg_stack);
        goto CACHE_AND_PUSH_RESULT;
      }
      else if (bzla_hashint_table_contains(wblasted, real_cur->id))
      {
        assert(BZLA_COUNT_STACK(arg_stack));
        result = BZLA_POP_STACK(arg_stack);
#ifndef NDEBUG
        BzlaNode *bv_node       = bzla_fp_word_blast(bzla, real_cur);
        const BzlaBitVector *bv = bzla_model_get_bv(bzla, bv_node);
        assert(bv);
        assert(bzla_bv_compare(result, bv) == 0);
#endif
        goto CACHE_AND_PUSH_RESULT;
      }

      num_args = 0;

      /* special handling for conditionals:
       *  1) push condition
       *  2) evaluate condition
       *  3) push branch w.r.t. value of evaluated condition */
      if (bzla_node_is_cond(real_cur))
      {
        /* only the condition is on the stack */
        assert(BZLA_COUNT_STACK(arg_stack) >= 1);
        arg_stack.top -= 1;
      }
      else if (bzla_node_is_apply(real_cur))
      {
        num_args = bzla_node_args_get_arity(bzla, real_cur->e[1]);
        arg_stack.top -= 1;        /* value of apply */
        arg_stack.top -= num_args; /* arguments of apply */
        md->as_int = 1;
      }
      /* leave arguments on stack, we need them later for apply */
      else if (bzla_node_is_args(real_cur))
      {
        assert(md->as_int == 0);
        bzla_hashint_map_remove(mark, real_cur->id, 0);
        continue;
      }
      else
      {
        assert(BZLA_COUNT_STACK(arg_stack) >= real_cur->arity);
        arg_stack.top -= real_cur->arity;
        md->as_int = 1;
      }

      e = (BzlaBitVector **) arg_stack.top; /* arguments in reverse order */

      switch (real_cur->kind)
      {
        case BZLA_BV_SLICE_NODE:
          result = bzla_bv_slice(mm,
                                 e[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
          bzla_bv_free(mm, e[0]);
          break;
        case BZLA_BV_AND_NODE:
          result = bzla_bv_and(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_EQ_NODE:
          result = bzla_bv_eq(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_ADD_NODE:
          result = bzla_bv_add(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_MUL_NODE:
          result = bzla_bv_mul(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_ULT_NODE:
          result = bzla_bv_ult(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SLL_NODE:
          result = bzla_bv_sll(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SLT_NODE:
          result = bzla_bv_slt(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_SRL_NODE:
          result = bzla_bv_srl(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_UDIV_NODE:
          result = bzla_bv_udiv(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_UREM_NODE:
          result = bzla_bv_urem(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;
        case BZLA_BV_CONCAT_NODE:
          result = bzla_bv_concat(mm, e[1], e[0]);
          bzla_bv_free(mm, e[0]);
          bzla_bv_free(mm, e[1]);
          break;

        case BZLA_APPLY_NODE:
          assert(num_args);
          t = bzla_bv_new_tuple(mm, num_args);
          for (i = 0; i < num_args; i++)
          {
            bzla_bv_add_to_tuple(mm, t, e[i], num_args - 1 - i);
            bzla_bv_free(mm, e[i]);
          }

          /* check if there is already a value for given arguments */
          result = get_value_from_fun_model(bzla, fun_model, real_cur->e[0], t);
          if (!result)
          {
            /* value of apply is at last index of e */
            result = e[num_args];
            add_to_fun_model(bzla, fun_model, real_cur->e[0], t, result);
          }
          else
            bzla_bv_free(mm, e[num_args]);

          bzla_bv_free_tuple(mm, t);
          break;

        case BZLA_UF_NODE:
          assert(bzla_node_is_apply(cur_parent));
          result =
              get_apply_value(bzla, cur_parent, real_cur, bv_model, fun_model);
          if (!result)
          {
            BzlaSortId sort = bzla_node_get_sort_id(cur_parent);
            uint32_t bw;
            if (bzla_sort_is_fp(bzla, sort))
            {
              bw = bzla_sort_fp_get_bv_width(bzla, sort);
            }
            else if (bzla_sort_is_rm(bzla, sort))
            {
              bw = BZLA_RM_BW;
            }
            else
            {
              assert(bzla_sort_is_bv(bzla, sort));
              bw = bzla_node_bv_get_width(bzla, cur_parent);
            }
            result = bzla_bv_zero(mm, bw);
          }
          break;

        case BZLA_UPDATE_NODE:
          result =
              get_apply_value(bzla, cur_parent, real_cur, bv_model, fun_model);
          if (!result)
            result = e[2];
          else
            bzla_bv_free(mm, e[2]);
          bzla_bv_free(mm, e[1]);
          bzla_bv_free(mm, e[0]);
          break;

        default:
          assert(bzla_node_is_cond(real_cur));

          /* evaluate condition and select branch */
          if (md->as_int == 2)
          {
            /* select branch w.r.t. condition */
            next = bzla_bv_is_true(e[0]) ? real_cur->e[1] : real_cur->e[2];
            BZLA_PUSH_STACK(work_stack, cur);
            BZLA_PUSH_STACK(work_stack, cur_parent);
            /* for function conditionals we push the function and the
             * apply */
            BZLA_PUSH_STACK(work_stack, next);
            BZLA_PUSH_STACK(work_stack, cur_parent);
            bzla_bv_free(mm, e[0]);
            /* no result yet, we need to evaluate the selected function
             */
            md->as_int = 0;
            continue;
          }
          /* cache result */
          else
          {
            assert(md->as_int == 0);
            result     = e[0];
            md->as_int = 1;
          }
      }

      /* function nodes are never cached (assignment always depends on the
       * given arguments) */
      if (bzla_node_is_fun(real_cur))
      {
        assert(result);
        /* not inserted into cache */
        bzla_hashint_map_remove(mark, real_cur->id, 0);
        goto PUSH_RESULT;
      }
      else if (bzla_node_is_apply(real_cur))
      {
        /* not inserted into cache */
        bzla_hashint_map_remove(mark, real_cur->id, 0);
        if (real_cur->parameterized) goto PUSH_RESULT;
      }

    CACHE_AND_PUSH_RESULT:
      assert(!bzla_node_is_fun(real_cur));
      assert(!real_cur->parameterized);
      assert(!bzla_hashint_map_contains(bv_model, real_cur->id));
      bzla_model_add_to_bv(bzla, bv_model, real_cur, result);

    PUSH_RESULT:
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
      assert(md->as_int == 1);
    PUSH_CACHED:
      assert(!real_cur->parameterized);
      d      = bzla_hashint_map_get(bv_model, real_cur->id);
      result = bzla_bv_copy(mm, (BzlaBitVector *) d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(arg_stack) == 1);
  result = BZLA_POP_STACK(arg_stack);
  assert(result);

  BZLA_RELEASE_STACK(work_stack);
  BZLA_RELEASE_STACK(arg_stack);
  BZLA_RELEASE_STACK(reset);
  bzla_hashint_map_delete(assigned);
  bzla_hashint_map_delete(mark);
  bzla_hashint_table_delete(expanded);
  bzla_hashint_table_delete(wblasted);

  while (!BZLA_EMPTY_STACK(cleanup_expanded))
  {
    bzla_node_release(bzla, BZLA_POP_STACK(cleanup_expanded));
  }
  BZLA_RELEASE_STACK(cleanup_expanded);

  return result;
}

/*------------------------------------------------------------------------*/

static BzlaNode *
mk_default_value(Bzla *bzla, BzlaSortId sort)
{
  if (bzla_sort_is_bv(bzla, sort))
  {
    return bzla_exp_bv_zero(bzla, sort);
  }
  else if (bzla_sort_is_fp(bzla, sort))
  {
    return bzla_exp_fp_pos_zero(bzla, sort);
  }
  else
  {
    assert(bzla_sort_is_rm(bzla, sort));
    return bzla_exp_rm_const(bzla, BZLA_RM_RNE);
  }
}

BzlaNode *
bzla_model_get_value(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla->last_sat_result == BZLA_RESULT_SAT && bzla->valid_assignments);

  uint32_t i, nparams;
  BzlaNode *res, *tmp, *arg, *val, **params, *cond, *eq;
  BzlaSortId sort, domain;
  const BzlaPtrHashTable *model;
  BzlaBitVectorTuple *tup;
  BzlaBitVector *bv_val;
  BzlaPtrHashTableIterator it;
  BzlaTupleSortIterator tit;

  exp  = bzla_simplify_exp(bzla, exp);
  sort = bzla_node_get_sort_id(exp);

  if (bzla_node_is_bv(bzla, exp) || bzla_node_is_fp(bzla, exp)
      || bzla_node_is_rm(bzla, exp))
  {
    res = bzla_node_mk_value(bzla, sort, bzla_model_get_bv(bzla, exp));
  }
  else if (bzla_node_is_lambda(exp) || bzla_node_is_const_array(exp))
  {
    res = bzla_node_copy(bzla, exp);
  }
  else
  {
    assert(bzla_node_is_array(exp) || bzla_node_is_fun(exp));
    model = bzla_model_get_fun(bzla, exp);
    if (bzla_node_is_array(exp))
    {
      /* Check for const array. */
      res = 0;
      if (model)
      {
        bzla_iter_hashptr_init(&it, model);
        while (bzla_iter_hashptr_has_next(&it))
        {
          bv_val = it.bucket->data.as_ptr;
          tup    = bzla_iter_hashptr_next(&it);
          if (tup->arity == 0)
          {
            val = bzla_node_mk_value(
                bzla, bzla_sort_array_get_element(bzla, sort), bv_val);
            res = bzla_exp_const_array(bzla, sort, val);
            bzla_node_release(bzla, val);
            break;
          }
        }
      }

      /* Create fresh base array if no const array was found. */
      if (!res)
      {
        BzlaNode *val =
            mk_default_value(bzla, bzla_sort_array_get_element(bzla, sort));
        res = bzla_exp_const_array(bzla, sort, val);
        bzla_node_release(bzla, val);
      }

      /* Build write chains on top of base array. */
      if (model)
      {
        bzla_iter_hashptr_init(&it, model);
        while (bzla_iter_hashptr_has_next(&it))
        {
          bv_val = it.bucket->data.as_ptr;
          tup    = bzla_iter_hashptr_next(&it);
          /* Skip const array. */
          if (tup->arity == 0)
          {
            continue;
          }
          val = bzla_node_mk_value(
              bzla, bzla_sort_array_get_element(bzla, sort), bv_val);
          arg = bzla_node_mk_value(
              bzla, bzla_sort_array_get_index(bzla, sort), tup->bv[0]);
          tmp = bzla_exp_write(bzla, res, arg, val);
          bzla_node_release(bzla, arg);
          bzla_node_release(bzla, val);
          bzla_node_release(bzla, res);
          res = tmp;
        }
      }
    }
    else
    {
      domain  = bzla_sort_fun_get_domain(bzla, sort);
      nparams = bzla_node_fun_get_arity(bzla, exp);
      BZLA_NEWN(bzla->mm, params, nparams);
      /* create parameters x1, ..., xn for lambda */
      i = 0;
      bzla_iter_tuple_sort_init(&tit, bzla, domain);
      while (bzla_iter_tuple_sort_has_next(&tit))
      {
        params[i++] = bzla_exp_param(bzla, bzla_iter_tuple_sort_next(&tit), 0);
      }
      /* create base case: uf(x1, ..., xn) */
      res = mk_default_value(bzla, bzla_sort_fun_get_codomain(bzla, sort));
      BzlaSortId codomain_sort = bzla_sort_fun_get_codomain(bzla, sort);
      BzlaSort *domain_sort =
          bzla_sort_get_by_id(bzla, bzla_sort_fun_get_domain(bzla, sort));
      /* create ite chain */
      if (model)
      {
        bzla_iter_hashptr_init(&it, (BzlaPtrHashTable *) model);
        while (bzla_iter_hashptr_has_next(&it))
        {
          val = bzla_node_mk_value(bzla, codomain_sort, it.bucket->data.as_ptr);
          tup = (BzlaBitVectorTuple *) bzla_iter_hashptr_next(&it);
          assert(tup->arity == nparams);
          cond = bzla_exp_true(bzla);
          assert(tup->arity == domain_sort->tuple.num_elements);
          for (i = 0; i < nparams; i++)
          {
            arg = bzla_node_mk_value(
                bzla, domain_sort->tuple.elements[i]->id, tup->bv[i]);
            eq  = bzla_exp_eq(bzla, arg, params[i]);
            tmp = bzla_exp_bv_and(bzla, cond, eq);
            bzla_node_release(bzla, eq);
            bzla_node_release(bzla, arg);
            bzla_node_release(bzla, cond);
            cond = tmp;
          }
          tmp = bzla_exp_cond(bzla, cond, val, res);
          bzla_node_release(bzla, val);
          bzla_node_release(bzla, cond);
          bzla_node_release(bzla, res);
          res = tmp;
        }
      }
      tmp = bzla_exp_fun(bzla, params, nparams, res);
      bzla_node_release(bzla, res);
      res = tmp;
      for (i = 0; i < nparams; i++)
      {
        bzla_node_release(bzla, params[i]);
      }
      BZLA_DELETEN(bzla->mm, params, nparams);
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/

static void
collect_nodes(Bzla *bzla,
              BzlaNode *roots[],
              uint32_t num_roots,
              BzlaNodePtrStack *nodes)
{
  uint32_t i;
  BzlaNodePtrStack visit;
  BzlaNode *cur;
  BzlaIntHashTable *cache;

  BZLA_INIT_STACK(bzla->mm, visit);
  cache = bzla_hashint_table_new(bzla->mm);

  for (i = 0; i < num_roots; i++) BZLA_PUSH_STACK(visit, roots[i]);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;

    if (!cur->parameterized && !bzla_node_is_args(cur))
      BZLA_PUSH_STACK(*nodes, bzla_node_copy(bzla, cur));
    bzla_hashint_table_add(cache, cur->id);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
}

void
bzla_model_generate(Bzla *bzla,
                    BzlaIntHashTable *bv_model,
                    BzlaIntHashTable *fun_model,
                    bool model_for_all_nodes)
{
  assert(bzla);
  assert(bv_model);
  assert(fun_model);

  uint32_t i;
  double start;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack roots, nodes;

  start = bzla_util_time_stamp();

  BZLA_INIT_STACK(bzla->mm, nodes);

  if (model_for_all_nodes)
  {
    for (i = 1; i < BZLA_COUNT_STACK(bzla->nodes_id_table); i++)
    {
      cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i);
      if (!cur || bzla_node_is_args(cur) || bzla_node_is_proxy(cur)
          || cur->parameterized)
        continue;
      assert(!bzla_node_is_simplified(cur)
             || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
      BZLA_PUSH_STACK(
          nodes, bzla_node_copy(bzla, bzla_node_get_simplified(bzla, cur)));
    }
  }
  else /* push nodes reachable from roots only */
  {
    BZLA_INIT_STACK(bzla->mm, roots);
    bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
    bzla_iter_hashptr_queue(&it, bzla->assumptions);
    bzla_iter_hashptr_queue(&it, bzla->inputs);
    while (bzla_iter_hashptr_has_next(&it))
    {
      cur = bzla_iter_hashptr_next(&it);
      cur = bzla_node_get_simplified(bzla, cur);
      BZLA_PUSH_STACK(roots, cur);
    }
    collect_nodes(bzla, roots.start, BZLA_COUNT_STACK(roots), &nodes);
    BZLA_RELEASE_STACK(roots);
  }

  compute_model_values(
      bzla, bv_model, fun_model, nodes.start, BZLA_COUNT_STACK(nodes));

  while (!BZLA_EMPTY_STACK(nodes))
    bzla_node_release(bzla, BZLA_POP_STACK(nodes));
  BZLA_RELEASE_STACK(nodes);

  bzla->time.model_gen += bzla_util_time_stamp() - start;
}

/*------------------------------------------------------------------------*/

void
bzla_model_delete(Bzla *bzla)
{
  assert(bzla);
  bzla_model_delete_bv(bzla, &bzla->bv_model);
  delete_fun_model(bzla, &bzla->fun_model);
}
