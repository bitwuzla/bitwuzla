/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaunconstrained.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlamsg.h"
#include "bzlasubst.h"
#include "utils/bzlahashint.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static bool
is_uc_write(BzlaNode *cond)
{
  assert(bzla_node_is_regular(cond));
  assert(bzla_node_is_bv_cond(cond));
  assert(cond->parameterized);

  BzlaNode *lambda;

  if (cond->parents != 1) return false;

  lambda = bzla_node_real_addr(cond->first_parent);
  if (!bzla_node_is_lambda(lambda)) return false;

  return bzla_node_lambda_get_static_rho(lambda) != 0;
}

static void
mark_uc(Bzla *bzla, BzlaIntHashTable *uc, BzlaNode *exp)
{
  assert(bzla_node_is_regular(exp));
  /* no inputs allowed here */
  assert(exp->arity > 0);

  BzlaNode *subst;

  assert(!bzla_hashint_table_contains(uc, exp->id));
  bzla_hashint_table_add(uc, exp->id);

  BZLALOG(2,
          "found uc (%c) term %s",
          exp->parameterized ? 'p' : 'n',
          bzla_util_node2string(exp));

  if (exp->parameterized)
  {
    bzla->stats.param_uc_props++;
    return;
  }

  if (bzla_node_is_apply(exp) || bzla_node_is_lambda(exp)
      || bzla_node_is_fun_eq(exp) || bzla_node_is_update(exp))
    bzla->stats.fun_uc_props++;
  else
    bzla->stats.bv_uc_props++;

  if (bzla_node_is_lambda(exp) || bzla_node_is_fun_cond(exp)
      || bzla_node_is_update(exp))
  {
    subst           = bzla_exp_uf(bzla, bzla_node_get_sort_id(exp), 0);
    subst->is_array = exp->is_array;
  }
  else
    subst = bzla_exp_var(bzla, bzla_node_get_sort_id(exp), 0);

  bzla_insert_substitution(bzla, exp, subst, false);
  bzla_node_release(bzla, subst);
}

void
bzla_optimize_unconstrained(Bzla *bzla)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2);
  assert(!bzla_opt_get(bzla, BZLA_OPT_INCREMENTAL));
  assert(!bzla_opt_get(bzla, BZLA_OPT_PRODUCE_MODELS));

  double start, delta;
  uint32_t i, num_ucs;
  bool uc[4], ucp[4];
  BzlaNode *cur, *cur_parent;
  BzlaNodePtrStack stack, roots;
  BzlaPtrHashTableIterator it;
  BzlaNodeIterator pit;
  BzlaMemMgr *mm;
  BzlaIntHashTable *ucs;  /* unconstrained candidate nodes */
  BzlaIntHashTable *ucsp; /* parameterized unconstrained candidate nodes */
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;

  if (bzla->bv_vars->count == 0 && bzla->ufs->count == 0) return;

  BZLALOG(1, "start unconstrained optimization");

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  BZLA_INIT_STACK(mm, stack);
  BZLA_INIT_STACK(mm, roots);
  uc[0] = uc[1] = uc[2] = ucp[0] = ucp[1] = ucp[2] = false;

  mark = bzla_hashint_map_new(mm);
  ucs  = bzla_hashint_table_new(mm);
  ucsp = bzla_hashint_table_new(mm);
  bzla_init_substitutions(bzla);

  /* collect nodes that might contribute to a unconstrained candidate
   * propagation */
  bzla_iter_hashptr_init(&it, bzla->bv_vars);
  bzla_iter_hashptr_queue(&it, bzla->ufs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(cur));

    if (bzla_node_is_simplified(cur)) continue;

    if (cur->parents == 1)
    {
      cur_parent = bzla_node_real_addr(cur->first_parent);
      bzla_hashint_table_add(ucs, cur->id);
      BZLALOG(2, "found uc input %s", bzla_util_node2string(cur));
      // TODO (ma): why not just collect ufs and vars?
      if (bzla_node_is_uf(cur)
          || (cur_parent->kind != BZLA_ARGS_NODE
              && cur_parent->kind != BZLA_LAMBDA_NODE))
        BZLA_PUSH_STACK(stack, cur_parent);
    }
  }
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = BZLA_POP_STACK(stack);
    assert(bzla_node_is_regular(cur));
    assert(!bzla_node_is_simplified(cur)
           || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));

    if (bzla_node_is_simplified(cur)) continue;

    if (!bzla_hashint_map_contains(mark, cur->id))
    {
      bzla_hashint_map_add(mark, cur->id);
      if (!cur->parents)
        BZLA_PUSH_STACK(roots, cur);
      else
      {
        bzla_iter_parent_init(&pit, cur);
        while (bzla_iter_parent_has_next(&pit))
          BZLA_PUSH_STACK(stack, bzla_iter_parent_next(&pit));
      }
    }
  }

  /* identify unconstrained candidates */
  for (i = 0; i < BZLA_COUNT_STACK(roots); i++)
    BZLA_PUSH_STACK(stack, BZLA_PEEK_STACK(roots, i));
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur = BZLA_POP_STACK(stack);
    assert(bzla_node_is_regular(cur));
    d = bzla_hashint_map_get(mark, cur->id);

    if (!d) continue;

    assert(!bzla_node_is_bv_const(cur));
    assert(!bzla_node_is_var(cur));
    assert(!bzla_node_is_uf(cur));
    assert(!bzla_node_is_param(cur));

    if (d->as_int == 0)
    {
      d->as_int = 1;
      BZLA_PUSH_STACK(stack, cur);
      for (i = 1; i <= cur->arity; i++)
        BZLA_PUSH_STACK(stack, bzla_node_real_addr(cur->e[cur->arity - i]));
    }
    else
    {
      assert(d->as_int == 1);
      bzla_hashint_map_remove(mark, cur->id, 0);

      /* propagate unconstrained candidates */
      if (cur->parents == 0 || (cur->parents == 1 && !cur->constraint))
      {
        for (i = 0; i < cur->arity; i++)
        {
          uc[i] = bzla_hashint_table_contains(
              ucs, bzla_node_real_addr(cur->e[i])->id);
          ucp[i] = bzla_hashint_table_contains(
              ucsp, bzla_node_real_addr(cur->e[i])->id);
          assert(!uc[i] || uc[i] != ucp[i]);
          assert(!ucp[i] || uc[i] != ucp[i]);
          assert(!ucp[i] || cur->parameterized || bzla_node_is_lambda(cur));
        }

        switch (cur->kind)
        {
          case BZLA_BV_SLICE_NODE:
          case BZLA_APPLY_NODE:
            if (uc[0])
            {
              if (cur->parameterized)
              {
                if (bzla_node_is_apply(cur)) mark_uc(bzla, ucsp, cur);
              }
              else
                mark_uc(bzla, ucs, cur);
            }
            break;
          case BZLA_BV_ADD_NODE:
          case BZLA_BV_EQ_NODE:
          case BZLA_FUN_EQ_NODE:
            if (!cur->parameterized && (uc[0] || uc[1]))
              mark_uc(bzla, ucs, cur);
            break;
          case BZLA_BV_ULT_NODE:
          case BZLA_BV_CONCAT_NODE:
          case BZLA_BV_AND_NODE:
          case BZLA_BV_MUL_NODE:
          case BZLA_BV_SLL_NODE:
          case BZLA_BV_SRL_NODE:
          case BZLA_BV_UDIV_NODE:
          case BZLA_BV_UREM_NODE:
            if (!cur->parameterized && uc[0] && uc[1]) mark_uc(bzla, ucs, cur);
            break;
          case BZLA_COND_NODE:
            if ((uc[1] && uc[2]) || (uc[0] && (uc[1] || uc[2])))
              mark_uc(bzla, ucs, cur);
            else if (uc[1] && ucp[2])
            {
              /* case: x = t ? uc : ucp */
              if (is_uc_write(cur)) mark_uc(bzla, ucsp, cur);
            }
            break;
          case BZLA_UPDATE_NODE:
            if (uc[0] && uc[2]) mark_uc(bzla, ucs, cur);
            break;
          // TODO (ma): functions with parents > 1 can still be
          //            handled as unconstrained, but the applications
          //            on it cannot be unconstrained anymore
          //            (function congruence needs to be enforced)
          case BZLA_LAMBDA_NODE:
            assert(cur->parents <= 1);
            if (ucp[1]
                /* only consider head lambda of curried lambdas */
                && (!cur->first_parent
                    || !bzla_node_is_lambda(cur->first_parent)))
              mark_uc(bzla, ucs, cur);
            break;
          default: break;
        }
      }
    }
  }
  bzla_hashint_map_delete(mark);

  num_ucs = bzla->substitutions->count;
  bzla_substitute_and_rebuild(bzla, bzla->substitutions);

  /* cleanup */
  bzla_delete_substitutions(bzla);
  bzla_hashint_table_delete(ucs);
  bzla_hashint_table_delete(ucsp);
  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(roots);

  delta = bzla_util_time_stamp() - start;
  bzla->time.ucopt += delta;
  BZLALOG(1, "end unconstrained optimization");
  BZLA_MSG(bzla->msg,
           1,
           "detected %u unconstrained terms in %.3f seconds",
           num_ucs,
           delta);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
}
