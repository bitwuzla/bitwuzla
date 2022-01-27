/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlapputils.h"

#include "bzlacore.h"
#include "utils/bzlahashint.h"

void
bzla_pputils_collect_lambdas(Bzla *bzla, BzlaNodePtrStack *lambdas)
{
  assert(bzla);
  assert(lambdas);

  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack visit;
  BzlaPtrHashTableIterator it;
  BzlaIntHashTable *cache;

  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);
  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(visit, bzla_iter_hashptr_next(&it));
  }

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id) || !cur->lambda_below)
      continue;

    bzla_hashint_table_add(cache, cur->id);
    if (bzla_node_is_lambda(cur)) BZLA_PUSH_STACK(*lambdas, cur);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(visit);
}
