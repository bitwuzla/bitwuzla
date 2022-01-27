/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaack.h"

#include "bzlacore.h"
#include "bzlaexp.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

void
bzla_add_ackermann_constraints(Bzla *bzla)
{
  assert(bzla);

  uint32_t i, j, num_constraints = 0;
  double start, delta;
  BzlaNode *uf, *app_i, *app_j, *p, *c, *imp, *a_i, *a_j, *eq, *tmp;
  BzlaNode *cur;
  BzlaArgsIterator ait_i, ait_j;
  BzlaNodeIterator nit;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack applies, visit;
  BzlaIntHashTable *cache;
  BzlaMemMgr *mm;

  start = bzla_util_time_stamp();
  mm    = bzla->mm;
  cache = bzla_hashint_table_new(mm);
  BZLA_INIT_STACK(mm, visit);

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    BZLA_PUSH_STACK(visit, bzla_iter_hashptr_next(&it));

  /* mark reachable nodes */
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)) continue;
    bzla_hashint_table_add(cache, cur->id);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  BZLA_RELEASE_STACK(visit);

  bzla_iter_hashptr_init(&it, bzla->ufs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    uf = bzla_iter_hashptr_next(&it);
    BZLA_INIT_STACK(bzla->mm, applies);
    bzla_iter_apply_parent_init(&nit, uf);
    while (bzla_iter_apply_parent_has_next(&nit))
    {
      app_i = bzla_iter_apply_parent_next(&nit);
      if (app_i->parameterized) continue;
      if (!bzla_hashint_table_contains(cache, app_i->id)) continue;
      BZLA_PUSH_STACK(applies, app_i);
    }

    for (i = 0; i < BZLA_COUNT_STACK(applies); i++)
    {
      app_i = BZLA_PEEK_STACK(applies, i);
      for (j = i + 1; j < BZLA_COUNT_STACK(applies); j++)
      {
        app_j = BZLA_PEEK_STACK(applies, j);
        p     = 0;
        assert(bzla_node_get_sort_id(app_i->e[1])
               == bzla_node_get_sort_id(app_j->e[1]));
        bzla_iter_args_init(&ait_i, app_i->e[1]);
        bzla_iter_args_init(&ait_j, app_j->e[1]);
        while (bzla_iter_args_has_next(&ait_i))
        {
          a_i = bzla_iter_args_next(&ait_i);
          a_j = bzla_iter_args_next(&ait_j);
          eq  = bzla_exp_eq(bzla, a_i, a_j);

          if (!p)
            p = eq;
          else
          {
            tmp = p;
            p   = bzla_exp_bv_and(bzla, tmp, eq);
            bzla_node_release(bzla, tmp);
            bzla_node_release(bzla, eq);
          }
        }
        c   = bzla_exp_eq(bzla, app_i, app_j);
        imp = bzla_exp_implies(bzla, p, c);
        bzla->stats.ackermann_constraints++;
        num_constraints++;
        bzla_assert_exp(bzla, imp);
        bzla_node_release(bzla, p);
        bzla_node_release(bzla, c);
        bzla_node_release(bzla, imp);
      }
    }
    BZLA_RELEASE_STACK(applies);
  }
  bzla_hashint_table_delete(cache);
  delta = bzla_util_time_stamp() - start;
  BZLA_MSG(bzla->msg,
           1,
           "added %d ackermann constraints in %.3f seconds",
           num_constraints,
           delta);
  bzla->time.ack += delta;
}
