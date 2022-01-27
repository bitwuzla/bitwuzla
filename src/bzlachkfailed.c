/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlachkfailed.h"

#include "bzlaclone.h"
#include "bzlacore.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

static void
rebuild_formula(Bzla *bzla, uint32_t rewrite_level)
{
  assert(bzla);

  uint32_t i, cnt;
  BzlaNode *cur;
  BzlaPtrHashTable *t;

  BZLALOG(1, "rebuild formula with rewrite level %u", rewrite_level);

  /* set new rewrite level */
  bzla_opt_set(bzla, BZLA_OPT_RW_LEVEL, rewrite_level);

  t = bzla_hashptr_table_new(bzla->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  /* collect all leaves and rebuild whole formula */
  for (i = 1, cnt = BZLA_COUNT_STACK(bzla->nodes_id_table); i <= cnt; i++)
  {
    if (!(cur = BZLA_PEEK_STACK(bzla->nodes_id_table, cnt - i))) continue;

    if (bzla_node_is_simplified(cur)) continue;

    if (cur->arity == 0)
    {
      assert(bzla_node_is_var(cur) || bzla_node_is_bv_const(cur)
             || bzla_node_is_fp_const(cur) || bzla_node_is_rm_const(cur)
             || bzla_node_is_param(cur) || bzla_node_is_uf(cur));
      bzla_hashptr_table_add(t, cur);
    }
  }

  bzla_substitute_and_rebuild(bzla, t);
  bzla_hashptr_table_delete(t);

  BZLALOG(1, "rebuild formula done");
}

void
bzla_check_failed_assumptions(Bzla *bzla)
{
  assert(bzla);
  assert(bzla->last_sat_result == BZLA_RESULT_UNSAT);

  Bzla *clone;
  BzlaNode *ass, *cass;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack stack;

  clone = bzla_clone_exp_layer(bzla, 0, true);
  bzla_set_msg_prefix(clone, "chkf");
  bzla_opt_set(clone, BZLA_OPT_FUN_DUAL_PROP, 0);
  bzla_opt_set(clone, BZLA_OPT_CHECK_UNCONSTRAINED, 0);
  bzla_opt_set(clone, BZLA_OPT_CHECK_MODEL, 0);
  bzla_opt_set(clone, BZLA_OPT_CHECK_UNSAT_ASSUMPTIONS, 0);
  bzla_opt_set(clone, BZLA_OPT_PRINT_DIMACS, 0);
  bzla_opt_set(clone, BZLA_OPT_AUTO_CLEANUP, 1);
  bzla_set_term(clone, 0, 0);

  bzla_opt_set(clone, BZLA_OPT_ENGINE, BZLA_ENGINE_FUN);
  assert(clone->slv);
  clone->slv->api.delet(clone->slv);
  clone->slv = 0;

  /* clone->assertions have already been added at this point. */
  while (!BZLA_EMPTY_STACK(clone->assertions))
  {
    ass = BZLA_POP_STACK(clone->assertions);
    bzla_node_release(clone, ass);
  }

  /* Set to false in order to not trigger a reset of the assumptions when a
   * constraint is replaced (and thus a 'new' one added) when simplifying
   * expressions in bzla_substitute_and_rebuild. */
  clone->valid_assignments = 0;

  /* rebuild formula to eliminate all simplified nodes. */
  rebuild_formula(clone, 3);

  /* assert failed assumptions */
  BZLA_INIT_STACK(bzla->mm, stack);
  bzla_iter_hashptr_init(&it, bzla->orig_assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    ass = bzla_iter_hashptr_next(&it);
    if (bzla_failed_exp(bzla, ass))
    {
      BZLALOG(2, "failed assumption: %s", bzla_util_node2string(ass));
      cass = bzla_node_match(clone, ass);
      assert(cass);
      BZLA_PUSH_STACK(stack, cass);
    }
  }
  while (!BZLA_EMPTY_STACK(stack))
  {
    cass = BZLA_POP_STACK(stack);
    bzla_assert_exp(clone, cass);
    bzla_node_release(clone, cass);
  }
  BZLA_RELEASE_STACK(stack);

  /* cleanup assumptions */
  bzla_iter_hashptr_init(&it, clone->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(clone, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(clone->assumptions);
  clone->assumptions =
      bzla_hashptr_table_new(clone->mm,
                             (BzlaHashPtr) bzla_node_hash_by_id,
                             (BzlaCmpPtr) bzla_node_compare_by_id);

  assert(bzla_check_sat(clone, -1, -1) == BZLA_RESULT_UNSAT);
  bzla_delete(clone);
}
