/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasubst.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static void
update_assumptions(Bzla *bzla)
{
  assert(bzla);

  BzlaPtrHashTable *ass;
  BzlaNode *cur, *simp;
  BzlaPtrHashTableIterator it;

  ass = bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
  bzla_iter_hashptr_init(&it, bzla->orig_assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur  = bzla_iter_hashptr_next(&it);
    simp = bzla_simplify_exp(bzla, cur);
    if (!bzla_hashptr_table_get(ass, simp))
    {
      BZLALOG(2,
              "update assumption: %s -> %s",
              bzla_util_node2string(cur),
              bzla_util_node2string(simp));
      bzla_hashptr_table_add(ass, bzla_node_copy(bzla, simp));
    }
  }
  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(bzla->assumptions);
  bzla->assumptions = ass;
}

/* update hash tables of nodes in order to get rid of proxy nodes
 */
static void
update_node_hash_tables(Bzla *bzla)
{
  BzlaNode *cur, *data, *key, *simp_key, *simp_data;
  BzlaPtrHashTableIterator it, iit;
  BzlaPtrHashTable *static_rho, *new_static_rho;

  /* update static_rhos */
  bzla_iter_hashptr_init(&it, bzla->lambdas);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur        = bzla_iter_hashptr_next(&it);
    static_rho = bzla_node_lambda_get_static_rho(cur);

    if (!static_rho) continue;

    new_static_rho =
        bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    /* update static rho to get rid of proxy nodes */
    bzla_iter_hashptr_init(&iit, static_rho);
    while (bzla_iter_hashptr_has_next(&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = bzla_iter_hashptr_next(&iit);
      assert(bzla_node_is_regular(key));
      simp_key  = bzla_simplify_exp(bzla, key);
      simp_data = bzla_simplify_exp(bzla, data);

      if (!bzla_hashptr_table_get(new_static_rho, simp_key))
      {
        bzla_hashptr_table_add(new_static_rho, bzla_node_copy(bzla, simp_key))
            ->data.as_ptr = bzla_node_copy(bzla, simp_data);
      }
      bzla_node_release(bzla, key);
      bzla_node_release(bzla, data);
    }
    bzla_hashptr_table_delete(static_rho);
    bzla_node_lambda_set_static_rho(cur, new_static_rho);
  }
}

static BzlaNode *
rebuild_binder_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_binder(exp));
  assert(!bzla_node_param_get_assigned_exp(exp->e[0]));

  BzlaNode *result;

  /* we need to reset the binding lambda here as otherwise it is not possible
   * to create a new lambda term with the same param that substitutes 'exp' */
  bzla_node_param_set_binder(exp->e[0], 0);
  if (bzla_node_is_forall(exp))
    result = bzla_exp_forall(bzla, exp->e[0], exp->e[1]);
  else if (bzla_node_is_exists(exp))
    result = bzla_exp_exists(bzla, exp->e[0], exp->e[1]);
  else
  {
    assert(bzla_node_is_lambda(exp));
    result = bzla_exp_lambda(bzla, exp->e[0], exp->e[1]);
  }

  /* binder not rebuilt, set binder again */
  if (result == exp) bzla_node_param_set_binder(exp->e[0], exp);

  return result;
}

static BzlaNode *
rebuild_lambda_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_lambda(exp));
  assert(!bzla_node_param_get_assigned_exp(exp->e[0]));

  BzlaNode *result;

  result = rebuild_binder_exp(bzla, exp);

  /* copy static_rho for new lambda */
  if (bzla_node_lambda_get_static_rho(exp)
      && !bzla_node_lambda_get_static_rho(result))
    bzla_node_lambda_set_static_rho(
        result, bzla_node_lambda_copy_static_rho(bzla, exp));
  if (exp->is_array) result->is_array = 1;
  return result;
}

static BzlaNode *
rebuild_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));

  switch (exp->kind)
  {
    case BZLA_PROXY_NODE:
    case BZLA_BV_CONST_NODE:
    case BZLA_FP_CONST_NODE:
    case BZLA_RM_CONST_NODE:
    case BZLA_VAR_NODE:
    case BZLA_PARAM_NODE:
    case BZLA_UF_NODE:
      return bzla_node_copy(bzla, bzla_simplify_exp(bzla, exp));
    case BZLA_BV_SLICE_NODE:
      return bzla_exp_bv_slice(bzla,
                               exp->e[0],
                               bzla_node_bv_slice_get_upper(exp),
                               bzla_node_bv_slice_get_lower(exp));
    case BZLA_FP_TO_SBV_NODE:
      return bzla_exp_fp_to_sbv(
          bzla, exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
    case BZLA_FP_TO_UBV_NODE:
      return bzla_exp_fp_to_ubv(
          bzla, exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
    case BZLA_FP_TO_FP_BV_NODE:
      return bzla_exp_fp_to_fp_from_bv(
          bzla, exp->e[0], bzla_node_get_sort_id(exp));
    case BZLA_FP_TO_FP_FP_NODE:
      return bzla_exp_fp_to_fp_from_fp(
          bzla, exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
    case BZLA_FP_TO_FP_SBV_NODE:
      return bzla_exp_fp_to_fp_from_sbv(
          bzla, exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
    case BZLA_FP_TO_FP_UBV_NODE:
      return bzla_exp_fp_to_fp_from_ubv(
          bzla, exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
    case BZLA_LAMBDA_NODE: return rebuild_lambda_exp(bzla, exp);
    case BZLA_EXISTS_NODE:
    case BZLA_FORALL_NODE: return rebuild_binder_exp(bzla, exp);
    default: return bzla_exp_create(bzla, exp->kind, exp->e, exp->arity);
  }
}

static BzlaNode *
rebuild_noproxy(Bzla *bzla, BzlaNode *node, BzlaIntHashTable *cache)
{
  assert(bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(!bzla_node_is_simplified(node));

  size_t i;
  BzlaNode *e[4]   = {0, 0, 0, 0}, *child, *real_child, *simp;
  BzlaNode *result = 0;
  BzlaHashTableData *d;

  /* Note: the simplified pointer is not set for parameterized nodes. Hence, we
   * have to lookup cache. */
  for (i = 0; i < node->arity; i++)
  {
    child      = node->e[i];
    real_child = bzla_node_real_addr(child);
    if (real_child->parameterized
        && (d = bzla_hashint_map_get(cache, real_child->id)))
      e[i] = bzla_node_cond_invert(child, d->as_ptr);
    else
      e[i] = child;
  }

  switch (node->kind)
  {
    case BZLA_PROXY_NODE:
    case BZLA_BV_CONST_NODE:
    case BZLA_VAR_NODE:
    case BZLA_UF_NODE:
    case BZLA_PARAM_NODE:
    case BZLA_FP_CONST_NODE:
    case BZLA_RM_CONST_NODE:
      d = bzla_hashint_map_get(cache, node->id);
      if (d && d->as_ptr)
      {
        assert(d->as_ptr);
        result = bzla_node_copy(bzla, d->as_ptr);
      }
      else if (node->kind == BZLA_PARAM_NODE)
      {
        char *sym = bzla_node_get_symbol(bzla, node);
        if (0 && sym)
        {
          // TODO: make unique symbol
          size_t len = strlen(sym) + 1 + strlen("::subst");
          char buf[len];
          snprintf(buf, len, "%s::subst", sym);
          result = bzla_exp_param(bzla, node->sort_id, buf);
        }
        else
        {
          result = bzla_exp_param(bzla, node->sort_id, 0);
        }
      }
      else
      {
        result = bzla_node_copy(bzla, node);
      }
      break;

    case BZLA_BV_SLICE_NODE:
      result = bzla_exp_bv_slice(bzla,
                                 e[0],
                                 bzla_node_bv_slice_get_upper(node),
                                 bzla_node_bv_slice_get_lower(node));
      break;

    case BZLA_FP_TO_SBV_NODE:
      result =
          bzla_exp_fp_to_sbv(bzla, e[0], e[1], bzla_node_get_sort_id(node));
      break;

    case BZLA_FP_TO_UBV_NODE:
      result =
          bzla_exp_fp_to_ubv(bzla, e[0], e[1], bzla_node_get_sort_id(node));
      break;

    case BZLA_FP_TO_FP_BV_NODE:
      result =
          bzla_exp_fp_to_fp_from_bv(bzla, e[0], bzla_node_get_sort_id(node));
      break;

    case BZLA_FP_TO_FP_FP_NODE:
      result = bzla_exp_fp_to_fp_from_fp(
          bzla, e[0], e[1], bzla_node_get_sort_id(node));
      break;

    case BZLA_FP_TO_FP_SBV_NODE:
      result = bzla_exp_fp_to_fp_from_sbv(
          bzla, e[0], e[1], bzla_node_get_sort_id(node));
      break;

    case BZLA_FP_TO_FP_UBV_NODE:
      result = bzla_exp_fp_to_fp_from_ubv(
          bzla, e[0], e[1], bzla_node_get_sort_id(node));
      break;

    default: result = bzla_exp_create(bzla, node->kind, e, node->arity);
  }

  simp = bzla_node_copy(bzla, bzla_node_get_simplified(bzla, result));
  bzla_node_release(bzla, result);
  result = simp;

  if (bzla_node_is_lambda(node))
  {
    /* copy static_rho for new lambda */
    if (bzla_node_lambda_get_static_rho(node)
        && !bzla_node_lambda_get_static_rho(result))
    {
      bzla_node_lambda_set_static_rho(
          result, bzla_node_lambda_copy_static_rho(bzla, node));
    }
    result->is_array = node->is_array;
  }

  assert(result);
  return result;
}

static void
substitute(Bzla *bzla,
           BzlaNode *roots[],
           size_t nroots,
           BzlaPtrHashTable *substitutions)
{
  assert(bzla);
  assert(roots);
  assert(nroots);
  assert(substitutions);

  int32_t id;
  size_t i, cur_num_nodes;
  BzlaNodePtrStack visit, release_stack;
  BzlaHashTableData *d, *dsub;
  BzlaNode *cur, *cur_subst, *real_cur_subst, *rebuilt, *simplified;
  BzlaIntHashTable *substs, *cache;
#ifndef NDEBUG
  BzlaIntHashTable *cnt;
#endif
  BzlaPtrHashTableIterator it;
  bool opt_nondestr_subst = bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST) == 1;

  if (nroots == 0) return;

  BZLALOG(1, "start substitute");

  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_INIT_STACK(bzla->mm, release_stack);
  cache = bzla_hashint_map_new(bzla->mm);
#ifndef NDEBUG
  cnt = bzla_hashint_map_new(bzla->mm);
#endif

  /* normalize substitutions: -t1 -> t2 ---> t1 -> -t2 */
  substs = bzla_hashint_map_new(bzla->mm);
  bzla_iter_hashptr_init(&it, substitutions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur_subst = it.bucket->data.as_ptr;
    cur       = bzla_iter_hashptr_next(&it);
    assert(!bzla_node_is_simplified(cur));
    assert(!cur_subst || !bzla_node_is_simplified(cur_subst));

    if (bzla_node_is_inverted(cur))
    {
      cur = bzla_node_invert(cur);
      if (cur_subst)
      {
        cur_subst = bzla_node_invert(cur_subst);
      }
    }
    assert(bzla_node_is_regular(cur));

    d = bzla_hashint_map_add(substs, cur->id);

    /* Sometimes substitute is called with just a hash table without mapped
     * nodes (process_embedded_constraints, rebuild_formula).
     * In this case, we will just rebuild with the same node. */
    if (cur_subst)
    {
      d->as_ptr = cur_subst;
      assert(!bzla_node_is_simplified(cur_subst));
    }

    BZLALOG(1,
            "substitution: %s -> %s",
            bzla_util_node2string(cur),
            bzla_util_node2string(cur_subst));
  }

  for (i = 0; i < nroots; i++)
  {
    BZLA_PUSH_STACK(visit, roots[i]);
    BZLALOG(1, "root: %s", bzla_util_node2string(roots[i]));
  }

RESTART:
  cur_num_nodes = BZLA_COUNT_STACK(bzla->nodes_id_table);

  do
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    assert(cur);
    id = bzla_node_get_id(cur);

    /* do not traverse nodes that were not previously marked or are already
     * processed */

    if (!cur->rebuild) continue;

    d = bzla_hashint_map_get(cache, id);
    BZLALOG(2,
            "visit (%s, synth: %u, param: %u): %s",
            d == 0 ? "pre" : "post",
            bzla_node_is_synth(cur),
            cur->parameterized,
            bzla_util_node2string(cur));
    assert(opt_nondestr_subst || !bzla_node_is_simplified(cur));
    assert(!bzla_node_is_proxy(cur));

    if (!d)
    {
      d         = bzla_hashint_map_add(cache, id);
      d->as_ptr = 0;
      BZLA_PUSH_STACK(visit, cur);

      if ((dsub = bzla_hashint_map_get(substs, id)) && dsub->as_ptr)
      {
        cur_subst = dsub->as_ptr;
        BZLA_PUSH_STACK(visit, cur_subst);
      }

      if (bzla_node_is_simplified(cur))
      {
        BZLA_PUSH_STACK(visit, bzla_node_get_simplified(bzla, cur));
      }

      for (i = 0; i < cur->arity; i++)
      {
        BZLA_PUSH_STACK(visit, cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      if ((dsub = bzla_hashint_map_get(substs, id)) && dsub->as_ptr)
      {
        cur_subst = dsub->as_ptr;
      }
      else
      {
        cur_subst = cur;
      }

      cur_subst      = bzla_node_get_simplified(bzla, cur_subst);
      real_cur_subst = bzla_node_real_addr(cur_subst);

      if (opt_nondestr_subst)
      {
        rebuilt = rebuild_noproxy(bzla, real_cur_subst, cache);
      }
      else
      {
        rebuilt = rebuild_exp(bzla, real_cur_subst);
      }
      rebuilt = bzla_node_cond_invert(cur_subst, rebuilt);

      assert(rebuilt);
      assert(!bzla_node_is_simplified(rebuilt));

      if (cur != rebuilt && bzla_node_real_addr(rebuilt)->rebuild)
      {
        BZLALOG(1,
                "needs rebuild: %s != %s",
                bzla_util_node2string(cur),
                bzla_util_node2string(rebuilt));
        BZLA_PUSH_STACK(release_stack, rebuilt);
        BZLA_PUSH_STACK(visit, cur);
        BZLA_PUSH_STACK(visit, rebuilt);
#ifndef NDEBUG
        BzlaHashTableData *d;
        if (!(d = bzla_hashint_map_get(cnt, bzla_node_real_addr(cur)->id)))
          d = bzla_hashint_map_add(cnt, bzla_node_real_addr(cur)->id);
        d->as_int++;
        assert(d->as_int < 100);
#endif
        continue;
      }

      if (dsub || cur != rebuilt)
      {
        BZLALOG(1,
                dsub ? "substitute: %s -> %s" : "rebuild: %s -> %s",
                bzla_util_node2string(cur),
                bzla_util_node2string(rebuilt));
      }
      assert(!bzla_node_real_addr(rebuilt)->parameterized
             || cur->parameterized);

      bzla_hashint_map_add(cache, id)->as_ptr = bzla_node_copy(bzla, rebuilt);

      if (cur != rebuilt)
      {
        /* Do not rewrite synthesized and parameterized nodes if
         * non-destructive substitution is enabled.
         */
        if (!opt_nondestr_subst
            || (!bzla_node_is_synth(cur) && !cur->parameterized))
        {
          simplified = bzla_simplify_exp(bzla, rebuilt);
          bzla_set_simplified_exp(bzla, cur, simplified);
        }
      }
      bzla_node_release(bzla, rebuilt);

      /* mark as done */
      cur->rebuild = 0;
      BZLALOG(1, "reset needs rebuild: %s", bzla_util_node2string(cur));
#ifndef NDEBUG
      for (i = 0; i < cur->arity; i++)
        assert(!bzla_node_real_addr(cur->e[i])->rebuild);
#endif
    }
  } while (!BZLA_EMPTY_STACK(visit));

  /* We check the rebuild flag of all new nodes that were created while
   * executing above loop. If a node's rebuild flag is true, we need to process
   * the node and thus push it onto the 'visit' stack.  We have to do this in
   * order to ensure that after a substitution pass all nodes are rebuilt and
   * consistent.
   *
   * Note: We have to do this after the pass since it can happen that new nodes
   * get created while calling bzla_set_simplified_exp on a constraint that
   * have to rebuild flag enabled. For these nodes we have to do the below
   * check.
   */
  for (; cur_num_nodes < BZLA_COUNT_STACK(bzla->nodes_id_table);
       cur_num_nodes++)
  {
    cur = BZLA_PEEK_STACK(bzla->nodes_id_table, cur_num_nodes);
    if (!cur) continue;
    if (cur->rebuild && !cur->parents)
    {
      BZLALOG(1, "needs rebuild (post-subst): %s", bzla_util_node2string(cur));
      BZLA_PUSH_STACK(visit, cur);
    }
  }

  if (!BZLA_EMPTY_STACK(visit))
  {
    goto RESTART;
  }

  for (i = 0; i < cache->size; i++)
  {
    if (!cache->data[i].as_ptr) continue;
    bzla_node_release(bzla, cache->data[i].as_ptr);
  }
  bzla_hashint_map_delete(cache);
  bzla_hashint_map_delete(substs);
#ifndef NDEBUG
  bzla_hashint_map_delete(cnt);
#endif
  BZLA_RELEASE_STACK(visit);

  update_node_hash_tables(bzla);
  update_assumptions(bzla);

  while (!BZLA_EMPTY_STACK(release_stack))
  {
    bzla_node_release(bzla, BZLA_POP_STACK(release_stack));
  }
  BZLA_RELEASE_STACK(release_stack);

  BZLALOG(1, "end substitute");
  assert(bzla_dbg_check_unique_table_rebuild(bzla));
  assert(bzla_dbg_check_constraints_simp_free(bzla));
}

/* we perform all variable substitutions in one pass and rebuild the formula
 * cyclic substitutions must have been deleted before! */
void
bzla_substitute_and_rebuild(Bzla *bzla, BzlaPtrHashTable *substs)
{
  assert(bzla);
  assert(substs);

  BzlaNodePtrStack stack, root_stack;
  BzlaNode *cur, *cur_parent;
  BzlaMemMgr *mm;
  BzlaPtrHashTableIterator it;
  BzlaNodeIterator nit;
  bool ispushed;
  uint32_t i;
  bool opt_nondestr_subst;

  if (substs->count == 0u) return;

  mm                 = bzla->mm;
  opt_nondestr_subst = bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST) == 1;

  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, root_stack);

  /* search upwards for all reachable roots */
  /* we push all left sides on the search stack */
  bzla_iter_hashptr_init(&it, substs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(!bzla_node_is_simplified(cur));
    BZLA_PUSH_STACK(stack, cur);
  }

  do
  {
    assert(!BZLA_EMPTY_STACK(stack));
    cur = bzla_node_real_addr(BZLA_POP_STACK(stack));
    assert(opt_nondestr_subst || !bzla_node_is_simplified(cur));
    if (!cur->rebuild)
    {
      BZLALOG(2, "  cone: %s", bzla_util_node2string(cur));

      /* All nodes in the cone of the substitutions need to be rebuilt. This
       * flag gets propagated to the parent nodes when a node gets created.
       * After a completed substitution pass, the flag for every node must be
       * zero. */
      cur->rebuild = 1;

      bzla_iter_parent_init(&nit, cur);
      /* are we at a root ? */
      ispushed = false;
      while (bzla_iter_parent_has_next(&nit))
      {
        cur_parent = bzla_iter_parent_next(&nit);
        assert(bzla_node_is_regular(cur_parent));
        ispushed = true;
        BZLA_PUSH_STACK(stack, cur_parent);
      }
      /* Alwas rebuild param nodes of binders if non-destructive substitution
       * is enabled. */
      if (opt_nondestr_subst && bzla_node_is_binder(cur))
      {
        BZLA_PUSH_STACK(stack, cur->e[0]);
      }
      if (!ispushed)
      {
        BZLA_PUSH_STACK(root_stack, bzla_node_copy(bzla, cur));
      }
    }
  } while (!BZLA_EMPTY_STACK(stack));

  BZLA_RELEASE_STACK(stack);

  substitute(bzla, root_stack.start, BZLA_COUNT_STACK(root_stack), substs);

  for (i = 0; i < BZLA_COUNT_STACK(root_stack); i++)
  {
    bzla_node_release(bzla, BZLA_PEEK_STACK(root_stack, i));
  }
  BZLA_RELEASE_STACK(root_stack);

  assert(bzla_dbg_check_lambdas_static_rho_proxy_free(bzla));
}

BzlaNode *
bzla_substitute_nodes_node_map(Bzla *bzla,
                               BzlaNode *root,
                               BzlaNodeMap *substs,
                               BzlaIntHashTable *node_map)
{
  assert(bzla);
  assert(root);
  assert(substs);

  int32_t i;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *subst, *result, **e;
  BzlaNodePtrStack visit, args, cleanup;
  BzlaIntHashTable *mark, *mark_subst;
  BzlaHashTableData *d;
  BzlaNodeMapIterator it;

  mm         = bzla->mm;
  mark       = bzla_hashint_map_new(mm);
  mark_subst = bzla_hashint_map_new(mm);
  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, cleanup);
  BZLA_PUSH_STACK(visit, root);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);
    d        = bzla_hashint_map_get(mark, real_cur->id);
    if (!d)
    {
      subst = bzla_nodemap_mapped(substs, real_cur);
      if (subst)
      {
        /* if this assertion fails we have a cyclic substitution */
        assert(!bzla_hashint_map_get(mark, bzla_node_real_addr(subst)->id)
               || bzla_hashint_map_get(mark, bzla_node_real_addr(subst)->id)
                      ->as_ptr);
        BZLA_PUSH_STACK(visit, bzla_node_cond_invert(cur, subst));
        bzla_hashint_table_add(mark_subst, bzla_node_real_addr(subst)->id);
        continue;
      }

      (void) bzla_hashint_map_add(mark, real_cur->id);
      BZLA_PUSH_STACK(visit, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(visit, real_cur->e[i]);
    }
    else if (!d->as_ptr)
    {
      args.top -= real_cur->arity;
      e = args.top;

      if (real_cur->arity == 0)
      {
        if (bzla_node_is_param(real_cur)
            /* Do not create new param if 'real_cur' is already a
             * substitution */
            && !bzla_hashint_table_contains(mark_subst, real_cur->id))
        {
          // TODO: make unique symbol !<num>++
          result = bzla_exp_param(bzla, real_cur->sort_id, 0);
        }
        else
          result = bzla_node_copy(bzla, real_cur);
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
      else if (bzla_node_is_fp_to_fp_from_sbv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_sbv(
            bzla, e[0], e[1], bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_ubv(real_cur))
      {
        result = bzla_exp_fp_to_fp_from_ubv(
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
        }
      }
      for (i = 0; i < real_cur->arity; i++) bzla_node_release(bzla, e[i]);

      d->as_ptr = bzla_node_copy(bzla, result);
      BZLA_PUSH_STACK(cleanup, result);
      if (node_map)
      {
        assert(!bzla_hashint_map_contains(node_map, real_cur->id));
        bzla_hashint_map_add(node_map, real_cur->id)->as_int =
            bzla_node_real_addr(result)->id;
      }
    PUSH_RESULT:
      assert(real_cur->sort_id == bzla_node_real_addr(result)->sort_id);
      BZLA_PUSH_STACK(args, bzla_node_cond_invert(cur, result));
    }
    else
    {
      assert(d->as_ptr);
      result = bzla_node_copy(bzla, d->as_ptr);
      goto PUSH_RESULT;
    }
  }
  assert(BZLA_COUNT_STACK(args) == 1);
  result = BZLA_POP_STACK(args);

  /* update 'node_map' for substituted nodes */
  if (node_map)
  {
    bzla_iter_nodemap_init(&it, substs);
    while (bzla_iter_nodemap_has_next(&it))
    {
      subst = it.it.bucket->data.as_ptr;
      while (bzla_nodemap_mapped(substs, subst))
        subst = bzla_nodemap_mapped(substs, subst);
      cur = bzla_iter_nodemap_next(&it);
      assert(!bzla_hashint_map_contains(node_map, cur->id));
      bzla_hashint_map_add(node_map, cur->id)->as_int =
          bzla_node_real_addr(subst)->id;
    }
  }

  while (!BZLA_EMPTY_STACK(cleanup))
    bzla_node_release(bzla, BZLA_POP_STACK(cleanup));
  BZLA_RELEASE_STACK(cleanup);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(args);
  bzla_hashint_map_delete(mark);
  bzla_hashint_map_delete(mark_subst);
  return result;
}

BzlaNode *
bzla_substitute_nodes(Bzla *bzla, BzlaNode *root, BzlaNodeMap *substs)
{
  return bzla_substitute_nodes_node_map(bzla, root, substs, 0);
}

BzlaNode *
bzla_substitute_node(Bzla *bzla,
                     BzlaNode *root,
                     BzlaNode *node,
                     BzlaNode *subst)
{
  BzlaNodeMap *map = bzla_nodemap_new(bzla);
  bzla_nodemap_map(map, node, subst);
  BzlaNode *result = bzla_substitute_nodes_node_map(bzla, root, map, 0);
  bzla_nodemap_delete(map);
  return result;
}

void
bzla_substitute_terms(Bzla *bzla,
                      size_t terms_size,
                      BzlaNode *terms[],
                      size_t map_size,
                      BzlaNode *map_keys[],
                      BzlaNode *map_values[])
{
  size_t i;
  BzlaIntHashTable *map, *cache;
  BzlaNodePtrStack visit;
  BzlaNode *e[4];

  if (terms_size == 0 || map_size == 0) return;

  BZLA_INIT_STACK(bzla->mm, visit);
  map   = bzla_hashint_map_new(bzla->mm);
  cache = bzla_hashint_map_new(bzla->mm);

  for (i = 0; i < map_size; ++i)
  {
    assert(bzla_node_is_regular(map_keys[i]));
    assert(map_keys[i]->arity == 0); /* we expect var/uf/params only */
    bzla_hashint_map_add(map, map_keys[i]->id)->as_ptr = map_values[i];
  }

  for (i = 0; i < terms_size; ++i)
  {
    BZLA_PUSH_STACK(visit, terms[i]);
  }

  BzlaNode *cur, *result;
  BzlaHashTableData *d, *ds, *dd;
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    d   = bzla_hashint_map_get(cache, cur->id);
    ds  = bzla_hashint_map_get(map, cur->id);

    if (!d)
    {
      bzla_hashint_map_add(cache, cur->id);
      BZLA_PUSH_STACK(visit, cur);

      for (i = 0; i < cur->arity; ++i)
      {
        BZLA_PUSH_STACK(visit, cur->e[i]);
      }
    }
    else if (!d->as_ptr)
    {
      result = 0;
      if (ds)
      {
        result = bzla_node_copy(bzla, ds->as_ptr);
      }
      else
      {
        for (i = 0; i < cur->arity; ++i)
        {
          dd = bzla_hashint_map_get(cache, bzla_node_real_addr(cur->e[i])->id);
          assert(dd);
          e[i] = bzla_node_cond_invert(cur->e[i], dd->as_ptr);
        }

        if (cur->arity == 0)
        {
          if (bzla_node_is_param(cur))
          {
            result = bzla_exp_param(bzla, cur->sort_id, 0);
          }
          else
          {
            result = bzla_node_copy(bzla, cur);
          }
        }
        else if (bzla_node_is_bv_slice(cur))
        {
          result = bzla_exp_bv_slice(bzla,
                                     e[0],
                                     bzla_node_bv_slice_get_upper(cur),
                                     bzla_node_bv_slice_get_lower(cur));
        }
        else if (bzla_node_is_fp_to_sbv(cur))
        {
          result =
              bzla_exp_fp_to_sbv(bzla, e[0], e[1], bzla_node_get_sort_id(cur));
        }
        else if (bzla_node_is_fp_to_ubv(cur))
        {
          result =
              bzla_exp_fp_to_ubv(bzla, e[0], e[1], bzla_node_get_sort_id(cur));
        }
        else if (bzla_node_is_fp_to_fp_from_bv(cur))
        {
          result =
              bzla_exp_fp_to_fp_from_bv(bzla, e[0], bzla_node_get_sort_id(cur));
        }
        else if (bzla_node_is_fp_to_fp_from_fp(cur))
        {
          result = bzla_exp_fp_to_fp_from_fp(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
        }
        else if (bzla_node_is_fp_to_fp_from_sbv(cur))
        {
          result = bzla_exp_fp_to_fp_from_sbv(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
        }
        else if (bzla_node_is_fp_to_fp_from_ubv(cur))
        {
          result = bzla_exp_fp_to_fp_from_ubv(
              bzla, e[0], e[1], bzla_node_get_sort_id(cur));
        }
        else
        {
          /* if the param of a quantifier gets subtituted by a non-param,
           * we do not create a quantifier, but return the body instead */
          if (bzla_node_is_quantifier(cur) && !bzla_node_is_param(e[0]))
          {
            result = bzla_node_copy(bzla, e[1]);
          }
          else
          {
            result = bzla_exp_create(bzla, cur->kind, e, cur->arity);
          }
        }

        if (bzla_node_is_lambda(cur) && bzla_node_is_lambda(result))
        {
          /* copy static_rho for new lambda */
          if (bzla_node_lambda_get_static_rho(cur)
              && !bzla_node_lambda_get_static_rho(result))
          {
            bzla_node_lambda_set_static_rho(
                result, bzla_node_lambda_copy_static_rho(bzla, cur));
          }
          result->is_array = cur->is_array;
        }
      }

      d->as_ptr = result;
    }
  }

  for (i = 0; i < terms_size; ++i)
  {
    d = bzla_hashint_map_get(cache, bzla_node_real_addr(terms[i])->id);
    assert(d);
    terms[i] = bzla_node_copy(bzla, bzla_node_cond_invert(terms[i], d->as_ptr));
  }

  for (i = 0; i < cache->size; ++i)
  {
    if (!cache->data[i].as_ptr) continue;
    bzla_node_release(bzla, cache->data[i].as_ptr);
  }
  bzla_hashint_map_delete(map);
  bzla_hashint_map_delete(cache);
  BZLA_RELEASE_STACK(visit);
}
