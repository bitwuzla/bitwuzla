/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlaelimites.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlalog.h"
#include "bzlanode.h"
#include "bzlasubst.h"
#include "preprocess/bzlapputils.h"
#include "preprocess/bzlapreprocess.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

static char *
mk_ite_symbol(Bzla *bzla, BzlaNode *cur)
{
  assert(bzla_node_is_regular(cur));

  size_t len;
  char *symbol;

  len = strlen("sk_ite_") + 1;
  len += bzla_util_num_digits(bzla_node_get_id(cur));

  BZLA_NEWN(bzla->mm, symbol, len);
  snprintf(symbol, len, "sk_ite_%u", bzla_node_get_id(cur));
  return symbol;
}

void
bzla_eliminate_ites(Bzla *bzla)
{
  assert(bzla);

  double start, delta;
  char *symbol;
  uint32_t num_ites, i;
  BzlaNode *cur, *var, *eq_then, *eq_else, *impl_then, *impl_else;
  BzlaPtrHashTableIterator it;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;

  if (bzla->ops[BZLA_COND_NODE].cur == 0) return;

  start = bzla_util_time_stamp();

  cache = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);
  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  // TODO: Should we also apply to assumptions?
  // bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    BZLA_PUSH_STACK(visit, bzla_iter_hashptr_next(&it));
  }

  num_ites = 0;
  bzla_init_substitutions(bzla);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, bzla_node_get_id(cur))) continue;

    bzla_hashint_table_add(cache, bzla_node_get_id(cur));

    if (bzla_node_is_cond(cur) && !cur->parameterized)
    {
      symbol = mk_ite_symbol(bzla, cur);
      var    = bzla_node_create_var(bzla, bzla_node_get_sort_id(cur), symbol);
      bzla_mem_freestr(bzla->mm, symbol);

      eq_then = bzla_exp_eq(bzla, var, cur->e[1]);
      eq_else = bzla_exp_eq(bzla, var, cur->e[2]);

      impl_then = bzla_exp_implies(bzla, cur->e[0], eq_then);
      impl_else = bzla_exp_implies(bzla, bzla_node_invert(cur->e[0]), eq_else);

      bzla_assert_exp(bzla, impl_then);
      bzla_assert_exp(bzla, impl_else);

      bzla_insert_substitution(bzla, cur, var, 0);
      bzla_node_release(bzla, var);
      bzla_node_release(bzla, eq_then);
      bzla_node_release(bzla, eq_else);
      bzla_node_release(bzla, impl_then);
      bzla_node_release(bzla, impl_else);
      ++num_ites;
    }

    for (i = 0; i < cur->arity; ++i)
    {
      BZLA_PUSH_STACK(visit, cur->e[i]);
    }
  }

  bzla_substitute_and_rebuild(bzla, bzla->substitutions);
  bzla_delete_substitutions(bzla);
  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(visit);

  delta = bzla_util_time_stamp() - start;
  bzla->time.elimites += delta;
  BZLA_MSG(bzla->msg, 1, "eliminated %u ITEs in %.1f seconds", num_ites, delta);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
}
