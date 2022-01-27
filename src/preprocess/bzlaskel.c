/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifdef BZLA_USE_LINGELING
#include "preprocess/bzlaskel.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "lglib.h"
#include "utils/bzlahashint.h"
#include "utils/bzlautil.h"

static int32_t
fixed_exp(Bzla *bzla, BzlaNode *exp)
{
  BzlaNode *real_exp;
  BzlaSATMgr *smgr;
  BzlaAIG *aig;
  int32_t res, id;

  real_exp = bzla_node_real_addr(exp);
  assert(bzla_node_bv_get_width(bzla, real_exp) == 1);
  if (!bzla_node_is_synth(real_exp)) return 0;
  assert(real_exp->av);
  assert(real_exp->av->width == 1);
  assert(real_exp->av->aigs);
  aig = real_exp->av->aigs[0];
  if (aig == BZLA_AIG_TRUE)
    res = 1;
  else if (aig == BZLA_AIG_FALSE)
    res = -1;
  else
  {
    id = bzla_aig_get_cnf_id(aig);
    if (!id) return 0;
    smgr = bzla_get_sat_mgr(bzla);
    res  = bzla_sat_fixed(smgr, id);
  }
  if (bzla_node_is_inverted(exp)) res = -res;
  return res;
}

static int32_t
process_skeleton_tseitin_lit(BzlaPtrHashTable *ids, BzlaNode *exp)
{
  BzlaPtrHashBucket *b;
  BzlaNode *real_exp;
  int32_t res;

  real_exp = bzla_node_real_addr(exp);
  assert(bzla_node_bv_get_width(real_exp->bzla, real_exp) == 1);
  b = bzla_hashptr_table_get(ids, real_exp);
  if (!b)
  {
    b              = bzla_hashptr_table_add(ids, real_exp);
    b->data.as_int = (int32_t) ids->count;
  }

  res = b->data.as_int;
  assert(res > 0);

  if (bzla_node_is_inverted(exp)) res = -res;

  return res;
}

static void
process_skeleton_tseitin(Bzla *bzla,
                         LGL *lgl,
                         BzlaNodePtrStack *work_stack,
                         BzlaIntHashTable *mark,
                         BzlaPtrHashTable *ids,
                         BzlaNode *root)
{
  assert(bzla);

  int32_t i, lhs, rhs[3], fixed;
  BzlaNode *exp;
  BzlaHashTableData *d;

  BZLA_PUSH_STACK(*work_stack, root);

  do
  {
    exp = BZLA_POP_STACK(*work_stack);
    assert(exp);
    exp = bzla_node_real_addr(exp);
    d   = bzla_hashint_map_get(mark, exp->id);

    if (!d)
    {
      bzla_hashint_map_add(mark, exp->id);

      BZLA_PUSH_STACK(*work_stack, exp);
      for (i = exp->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(*work_stack, exp->e[i]);
    }
    else if (d->as_int == 0)
    {
      d->as_int = 1;
      if (bzla_node_is_fun(exp) || bzla_node_is_args(exp) || exp->parameterized
          || bzla_node_is_fp(bzla, exp) || bzla_node_is_rm(bzla, exp)
          || bzla_node_bv_get_width(bzla, exp) != 1)
      {
        continue;
      }

#ifndef NDEBUG
      BzlaNode *child;
      for (i = 0; i < exp->arity; i++)
      {
        child = bzla_node_real_addr(exp->e[i]);
        d     = bzla_hashint_map_get(mark, child->id);
        assert(d->as_int == 1);
        if (!bzla_node_is_fun(child) && !bzla_node_is_args(child)
            && !bzla_node_is_fp(bzla, child) && !bzla_node_is_rm(bzla, child)
            && !child->parameterized
            && bzla_node_bv_get_width(bzla, child) == 1)
          assert(bzla_hashptr_table_get(ids, child));
      }
#endif
      lhs   = process_skeleton_tseitin_lit(ids, exp);
      fixed = fixed_exp(bzla, exp);
      if (fixed)
      {
        lgladd(lgl, (fixed > 0) ? lhs : -lhs);
        lgladd(lgl, 0);
      }

      switch (exp->kind)
      {
        case BZLA_BV_AND_NODE:
          rhs[0] = process_skeleton_tseitin_lit(ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit(ids, exp->e[1]);

          lgladd(lgl, -lhs);
          lgladd(lgl, rhs[0]);
          lgladd(lgl, 0);

          lgladd(lgl, -lhs);
          lgladd(lgl, rhs[1]);
          lgladd(lgl, 0);

          lgladd(lgl, lhs);
          lgladd(lgl, -rhs[0]);
          lgladd(lgl, -rhs[1]);
          lgladd(lgl, 0);
          break;

        case BZLA_BV_EQ_NODE:
          if (bzla_node_bv_get_width(bzla, exp->e[0]) != 1) break;
          assert(bzla_node_bv_get_width(bzla, exp->e[1]) == 1);
          rhs[0] = process_skeleton_tseitin_lit(ids, exp->e[0]);
          rhs[1] = process_skeleton_tseitin_lit(ids, exp->e[1]);

          lgladd(lgl, -lhs);
          lgladd(lgl, -rhs[0]);
          lgladd(lgl, rhs[1]);
          lgladd(lgl, 0);

          lgladd(lgl, -lhs);
          lgladd(lgl, rhs[0]);
          lgladd(lgl, -rhs[1]);
          lgladd(lgl, 0);

          lgladd(lgl, lhs);
          lgladd(lgl, rhs[0]);
          lgladd(lgl, rhs[1]);
          lgladd(lgl, 0);

          lgladd(lgl, lhs);
          lgladd(lgl, -rhs[0]);
          lgladd(lgl, -rhs[1]);
          lgladd(lgl, 0);

          break;

#if 0
	    // can not happen, skeleton preprocessing is enabled when
	    // rewrite level > 2, Boolean condition are rewritten when
	    // rewrite level > 0
	    case BZLA_COND_NODE:
	      assert (bzla_node_bv_get_width (bzla, exp->e[0]) == 1);
	      if (bzla_node_bv_get_width (bzla, exp->e[1]) != 1)
		break;
	      assert (bzla_node_bv_get_width (bzla, exp->e[2]) == 1);
	      rhs[0] = process_skeleton_tseitin_lit (ids, exp->e[0]);
	      rhs[1] = process_skeleton_tseitin_lit (ids, exp->e[1]);
	      rhs[2] = process_skeleton_tseitin_lit (ids, exp->e[2]);

	      lgladd (lgl, -lhs);
	      lgladd (lgl, -rhs[0]);
	      lgladd (lgl, rhs[1]);
	      lgladd (lgl, 0);

	      lgladd (lgl, -lhs);
	      lgladd (lgl, rhs[0]);
	      lgladd (lgl, rhs[2]);
	      lgladd (lgl, 0);

	      lgladd (lgl, lhs);
	      lgladd (lgl, -rhs[0]);
	      lgladd (lgl, -rhs[1]);
	      lgladd (lgl, 0);

	      lgladd (lgl, lhs);
	      lgladd (lgl, rhs[0]);
	      lgladd (lgl, -rhs[2]);
	      lgladd (lgl, 0);
	      break;
#endif

        default:
          assert(!bzla_node_is_cond(exp));
          assert(!bzla_node_is_proxy(exp));
          break;
      }
    }
  } while (!BZLA_EMPTY_STACK(*work_stack));
}

void
bzla_process_skeleton(Bzla *bzla)
{
  BzlaPtrHashTable *ids;
  uint32_t count, fixed;
  BzlaNodePtrStack work_stack, new_assertions;
  BzlaMemMgr *mm = bzla->mm;
  BzlaPtrHashTableIterator it;
  double start, delta;
  int32_t res, lit, val;
  size_t i;
  BzlaNode *exp;
  LGL *lgl;
  BzlaIntHashTable *mark;

  start = bzla_util_time_stamp();

  ids = bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);

  lgl = lglinit();
  lglsetprefix(lgl, "[lglskel] ");

  if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) >= 2)
  {
    lglsetopt(lgl, "verbose", bzla_opt_get(bzla, BZLA_OPT_VERBOSITY) - 1);
    lglbnr("Lingeling", "[lglskel] ", stdout);
    fflush(stdout);
  }
  else
    lglsetopt(lgl, "verbose", -1);

  count = 0;

  BZLA_INIT_STACK(mm, work_stack);
  BZLA_INIT_STACK(mm, new_assertions);
  mark = bzla_hashint_map_new(mm);

  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    count++;
    exp = bzla_iter_hashptr_next(&it);
    assert(bzla_node_bv_get_width(bzla, exp) == 1);
    process_skeleton_tseitin(bzla, lgl, &work_stack, mark, ids, exp);
    lgladd(lgl, process_skeleton_tseitin_lit(ids, exp));
    lgladd(lgl, 0);
  }

  BZLA_RELEASE_STACK(work_stack);
  bzla_hashint_map_delete(mark);

  BZLA_MSG(bzla->msg,
           1,
           "found %u skeleton literals in %u constraints",
           ids->count,
           count);

  res = lglsimp(lgl, 0);

  if (bzla_opt_get(bzla, BZLA_OPT_VERBOSITY))
  {
    BZLA_MSG(bzla->msg, 1, "skeleton preprocessing result %d", res);
    lglstats(lgl);
  }

  fixed = 0;

  if (res == 20)
  {
    BZLA_MSG(bzla->msg, 1, "skeleton inconsistent");
    bzla->inconsistent = true;
  }
  else
  {
    assert(res == 0 || res == 10);
    bzla_iter_hashptr_init(&it, ids);
    while (bzla_iter_hashptr_has_next(&it))
    {
      exp = bzla_iter_hashptr_next(&it);
      assert(!bzla_node_is_inverted(exp));
      lit = process_skeleton_tseitin_lit(ids, exp);
      val = lglfixed(lgl, lit);
      if (val)
      {
        if (val < 0) exp = bzla_node_invert(exp);
        if (!bzla_hashptr_table_get(bzla->synthesized_constraints, exp)
            && !bzla_hashptr_table_get(bzla->unsynthesized_constraints, exp))
        {
          BZLALOG(
              1, "found constraint (skeleton): %s", bzla_util_node2string(exp));
          BZLA_PUSH_STACK(new_assertions, exp);
          bzla->stats.skeleton_constraints++;
          fixed++;
        }
      }
      else
      {
        assert(!bzla_hashptr_table_get(bzla->synthesized_constraints, exp));
        assert(!bzla_hashptr_table_get(bzla->unsynthesized_constraints, exp));
      }
    }
  }

  bzla_hashptr_table_delete(ids);
  lglrelease(lgl);

  for (i = 0; i < BZLA_COUNT_STACK(new_assertions); i++)
  {
    bzla_assert_exp(bzla, BZLA_PEEK_STACK(new_assertions, i));
  }
  BZLA_RELEASE_STACK(new_assertions);

  delta = bzla_util_time_stamp() - start;
  bzla->time.skel += delta;
  BZLA_MSG(bzla->msg,
           1,
           "skeleton preprocessing produced %u new constraints in %.1f seconds",
           fixed,
           delta);

  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
}
#endif
