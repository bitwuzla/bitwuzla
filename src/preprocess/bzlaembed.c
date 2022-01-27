/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaembed.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "utils/bzlautil.h"

void
bzla_process_embedded_constraints(Bzla *bzla)
{
  assert(bzla);

  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack ec;
  double start, delta;
  BzlaNode *cur;
  uint32_t count;

  if (bzla->embedded_constraints->count == 0u)
  {
    return;
  }

  BZLALOG(1, "start embedded constraint processing");

  start = bzla_util_time_stamp();
  count = 0;
  BZLA_INIT_STACK(bzla->mm, ec);
  bzla_iter_hashptr_init(&it, bzla->embedded_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_node_copy(bzla, bzla_iter_hashptr_next(&it));
    assert(bzla_node_real_addr(cur)->constraint);
    BZLA_PUSH_STACK(ec, cur);
    if (bzla_node_real_addr(cur)->parents > 0)
    {
      bzla->stats.ec_substitutions++;
    }
  }

  bzla_substitute_and_rebuild(bzla, bzla->embedded_constraints);

  while (!BZLA_EMPTY_STACK(ec))
  {
    cur = BZLA_POP_STACK(ec);

    if (bzla_hashptr_table_get(bzla->embedded_constraints, cur))
    {
      count++;
      bzla_hashptr_table_remove(bzla->embedded_constraints, cur, 0, 0);
      bzla_node_release(bzla, cur);
    }
    bzla_node_release(bzla, cur);
  }
  BZLA_RELEASE_STACK(ec);

  delta = bzla_util_time_stamp() - start;
  bzla->time.embedded += delta;
  BZLA_MSG(bzla->msg,
           1,
           "replaced %u embedded constraints in %1.f seconds",
           count,
           delta);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
  BZLALOG(1, "end embedded constraint processing");
}
