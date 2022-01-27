/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaelimapplies.h"

#include "bzlabeta.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "preprocess/bzlapputils.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static void
eliminate_update_nodes(Bzla *bzla)
{
  uint32_t i;
  BzlaNode *cur, *subst;

  bzla_init_substitutions(bzla);
  for (i = 1; i < BZLA_COUNT_STACK(bzla->nodes_id_table); i++)
  {
    cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i);
    if (!cur || !bzla_node_is_update(cur) || bzla_node_is_simplified(cur))
      continue;
    subst = bzla_exp_lambda_write(bzla, cur->e[0], cur->e[1]->e[0], cur->e[2]);
    bzla_insert_substitution(bzla, cur, subst, 0);
    bzla_node_release(bzla, subst);
  }
  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);
}

void
bzla_eliminate_applies(Bzla *bzla)
{
  assert(bzla);

  size_t i;
  uint32_t num_applies, num_applies_total = 0, round;
  double start, delta;
  BzlaNode *app, *fun, *subst;
  BzlaNodeIterator it;
  BzlaNodePtrStack lambdas;
  BzlaPtrHashTableIterator h_it;
  BzlaPtrHashTable *cache;
  BzlaPtrHashTable *substs;
  BzlaIntHashTable *app_cache;

  if (bzla_opt_get(bzla, BZLA_OPT_PP_BETA_REDUCE) == BZLA_BETA_REDUCE_ALL)
  {
    eliminate_update_nodes(bzla);
  }

  if (bzla->lambdas->count == 0) return;

  start     = bzla_util_time_stamp();
  round     = 1;
  cache     = bzla_hashptr_table_new(bzla->mm,
                                 (BzlaHashPtr) bzla_node_pair_hash,
                                 (BzlaCmpPtr) bzla_node_pair_compare);
  app_cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, lambdas);

  /* NOTE: in some cases substitute_and_rebuild creates applies that can be
   * beta-reduced. this can happen when parameterized applies become not
   * parameterized. hence, we beta-reduce applies until fix point.
   */
  do
  {
    BZLALOG(1, "start apply elimination (round %u)", round);

    num_applies = 0;

    substs = bzla_hashptr_table_new(bzla->mm,
                                    (BzlaHashPtr) bzla_node_hash_by_id,
                                    (BzlaCmpPtr) bzla_node_compare_by_id);

    bzla_pputils_collect_lambdas(bzla, &lambdas);

    /* collect function applications */
    for (i = 0; i < BZLA_COUNT_STACK(lambdas); i++)
    {
      fun = BZLA_PEEK_STACK(lambdas, i);

      bzla_iter_apply_parent_init(&it, fun);
      while (bzla_iter_apply_parent_has_next(&it))
      {
        app = bzla_iter_apply_parent_next(&it);

        if (bzla_node_is_simplified(app)) continue;

        if (bzla_hashint_table_contains(app_cache, bzla_node_get_id(app)))
          continue;

        /* If we have quantifiers, we always want to eliminate lambdas. */
        if (bzla->quantifiers->count == 0 && app->parameterized) continue;

        num_applies++;
        subst = bzla_beta_reduce_full(bzla, app, cache);
        assert(!bzla_hashptr_table_get(substs, app));
        bzla_hashptr_table_add(substs, app)->data.as_ptr = subst;
        bzla_hashint_table_add(app_cache, bzla_node_get_id(app));
      }
    }
    BZLA_RESET_STACK(lambdas);

    num_applies_total += num_applies;
    BZLA_MSG(bzla->msg,
             1,
             "eliminate %u applications in round %u",
             num_applies,
             round);

    bzla_substitute_and_rebuild(bzla, substs);

    bzla_iter_hashptr_init(&h_it, substs);
    while (bzla_iter_hashptr_has_next(&h_it))
    {
      bzla_node_release(bzla, bzla_iter_hashptr_next_data(&h_it)->as_ptr);
    }
    bzla_hashptr_table_delete(substs);

    BZLALOG(1, "end apply elimination (round %u)", round);
    round++;
  } while (num_applies > 0);

  bzla_hashint_table_delete(app_cache);

  bzla_iter_hashptr_init(&h_it, cache);
  while (bzla_iter_hashptr_has_next(&h_it))
  {
    bzla_node_release(bzla, h_it.bucket->data.as_ptr);
    bzla_node_pair_delete(bzla, bzla_iter_hashptr_next(&h_it));
  }
  bzla_hashptr_table_delete(cache);

#ifndef NDEBUG
  BZLA_RESET_STACK(lambdas);
  bzla_pputils_collect_lambdas(bzla, &lambdas);
  for (i = 0; i < BZLA_COUNT_STACK(lambdas); i++)
  {
    fun = BZLA_PEEK_STACK(lambdas, i);

    bzla_iter_apply_parent_init(&it, fun);
    while (bzla_iter_apply_parent_has_next(&it))
    {
      app = bzla_iter_apply_parent_next(&it);
      assert(app->parameterized
             || bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    }
  }
#endif
  BZLA_RELEASE_STACK(lambdas);

  delta = bzla_util_time_stamp() - start;
  bzla->time.elimapplies += delta;
  BZLA_MSG(bzla->msg,
           1,
           "eliminated %d function applications in %.1f seconds",
           num_applies_total,
           delta);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
}
