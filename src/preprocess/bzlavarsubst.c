/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "preprocess/bzlavarsubst.h"

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlalog.h"
#include "bzlasubst.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

static void
substitute_remove_cycles(Bzla *bzla, BzlaPtrHashTable *substs)
{
  BzlaPtrHashTable *order;
  BzlaNode *cur, *left, *right, *child;
  BzlaPtrHashBucket *b, *b_temp;
  BzlaPtrHashTableIterator it;
  int32_t order_num, val, max;
  uint32_t i;
  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  BzlaIntHashTable *mark;
  BzlaHashTableData *d;

  mm        = bzla->mm;
  order_num = 1;
  order     = bzla_hashptr_table_new(mm,
                                 (BzlaHashPtr) bzla_node_hash_by_id,
                                 (BzlaCmpPtr) bzla_node_compare_by_id);
  mark      = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, stack);

  /* we search for cyclic substitution dependencies
   * and map the substitutions to an ordering number */
  bzla_iter_hashptr_init(&it, substs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(cur));
    assert(bzla_node_is_var(cur) || bzla_node_is_uf(cur));
    BZLA_PUSH_STACK(stack, cur);

    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(stack));

      if (!cur)
      {
        cur = BZLA_POP_STACK(stack); /* left */
        assert(bzla_node_is_regular(cur));
        assert(bzla_node_is_var(cur) || bzla_node_is_uf(cur));
        assert(!bzla_hashptr_table_get(order, cur));
        bzla_hashptr_table_add(order, cur)->data.as_int = order_num++;
        continue;
      }
      /* visited (DFS) */
      if (bzla_hashint_table_contains(mark, cur->id)) continue;

      bzla_hashint_table_add(mark, cur->id);

      if (bzla_node_is_bv_const(cur) || bzla_node_is_var(cur)
          || bzla_node_is_rm_const(cur) || bzla_node_is_fp_const(cur)
          || bzla_node_is_param(cur) || bzla_node_is_uf(cur))
      {
        b_temp = bzla_hashptr_table_get(substs, cur);
        if (b_temp)
        {
          BZLA_PUSH_STACK(stack, cur); /* left  */
          BZLA_PUSH_STACK(stack, 0);
          BZLA_PUSH_STACK(stack, /* right */
                          (BzlaNode *) b_temp->data.as_ptr);
        }
        else
        {
          assert(!bzla_hashptr_table_get(order, cur));
          bzla_hashptr_table_add(order, cur)->data.as_int = 0;
        }
      }
      else
      {
        assert(cur->arity >= 1);
        assert(cur->arity <= BZLA_NODE_MAX_CHILDREN);
        for (i = 1; i <= cur->arity; i++)
          BZLA_PUSH_STACK(stack, cur->e[cur->arity - i]);
      }
    }
  }

  bzla_hashint_table_delete(mark);
  mark = bzla_hashint_map_new(mm);

  /* we look for cycles */
  bzla_iter_hashptr_init(&it, substs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    b   = it.bucket;
    cur = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(cur));
    assert(bzla_node_is_var(cur) || bzla_node_is_uf(cur));
    BZLA_PUSH_STACK(stack, (BzlaNode *) b->data.as_ptr);

    /* we assume that there are no direct cycles as a result of occurrence
     * check */
    while (!BZLA_EMPTY_STACK(stack))
    {
      cur = bzla_node_real_addr(BZLA_POP_STACK(stack));
      d   = bzla_hashint_map_get(mark, cur->id);

      if (d && d->as_int == 1) /* cur has max order of its children */
        continue;

      if (bzla_node_is_bv_const(cur) || bzla_node_is_var(cur)
          || bzla_node_is_rm_const(cur) || bzla_node_is_fp_const(cur)
          || bzla_node_is_param(cur) || bzla_node_is_uf(cur))
      {
        assert(bzla_hashptr_table_get(order, cur));
        continue;
      }

      assert(cur->arity >= 1);
      assert(cur->arity <= BZLA_NODE_MAX_CHILDREN);

      if (!d)
      {
        bzla_hashint_map_add(mark, cur->id);
        BZLA_PUSH_STACK(stack, cur);
        for (i = 1; i <= cur->arity; i++)
          BZLA_PUSH_STACK(stack, cur->e[cur->arity - i]);
      }
      else /* cur is visited, its children are visited */
      {
        /* compute maximum of children */
        assert(d->as_int == 0);
        d->as_int = 1;
        max       = 0;
        for (i = 1; i <= cur->arity; i++)
        {
          child  = bzla_node_real_addr(cur->e[cur->arity - i]);
          b_temp = bzla_hashptr_table_get(order, child);
          assert(b_temp);
          val = b_temp->data.as_int;
          assert(val >= 0);
          max = BZLA_MAX_UTIL(max, val);
        }
        bzla_hashptr_table_add(order, cur)->data.as_int = max;
      }
    }
  }
  bzla_hashint_map_delete(mark);

  assert(BZLA_EMPTY_STACK(stack));
  /* we eliminate cyclic substitutions, and reset mark flags */
  bzla_iter_hashptr_init(&it, substs);
  while (bzla_iter_hashptr_has_next(&it))
  {
    right = (BzlaNode *) it.bucket->data.as_ptr;
    assert(right);
    left = bzla_iter_hashptr_next(&it);
    assert(bzla_node_is_regular(left));
    assert(bzla_node_is_var(left) || bzla_node_is_uf(left));
    b_temp = bzla_hashptr_table_get(order, left);
    assert(b_temp);
    order_num = b_temp->data.as_int;
    b_temp    = bzla_hashptr_table_get(order, bzla_node_real_addr(right));
    assert(b_temp);
    max = b_temp->data.as_int;
    assert(order_num != max);
    /* found cycle */
    if (max > order_num) BZLA_PUSH_STACK(stack, left);
  }

  /* we delete cyclic substitutions */
  while (!BZLA_EMPTY_STACK(stack))
  {
    left = BZLA_POP_STACK(stack);
    assert(bzla_node_is_regular(left));
    assert(bzla_node_is_var(left) || bzla_node_is_uf(left));
    right = (BzlaNode *) bzla_hashptr_table_get(substs, left)->data.as_ptr;
    assert(right);
    bzla_hashptr_table_remove(substs, left, 0, 0);
    BZLALOG(1,
            "remove (cyclic) variable substitution: %s -> %s",
            bzla_util_node2string(left),
            bzla_util_node2string(right));
    bzla_node_release(bzla, left);
    bzla_node_release(bzla, right);
  }

  bzla_hashptr_table_delete(order);
  BZLA_RELEASE_STACK(stack);
}

void
bzla_substitute_var_exps(Bzla *bzla)
{
  assert(bzla);

  BzlaPtrHashTable *varsubst_constraints, *substs;
  BzlaNode *cur, *simp, *left, *right, *simp_right;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  double start, delta;
  uint32_t count;
  BzlaMemMgr *mm;

  mm                   = bzla->mm;
  varsubst_constraints = bzla->varsubst_constraints;

  if (varsubst_constraints->count == 0u) return;

  start = bzla_util_time_stamp();

  /* new equality constraints may be added during rebuild */
  count = 0;
  while (varsubst_constraints->count > 0u)
  {
    substs = bzla_hashptr_table_new(mm,
                                    (BzlaHashPtr) bzla_node_hash_by_id,
                                    (BzlaCmpPtr) bzla_node_compare_by_id);

    /* we copy the current substitution constraints into a local hash table,
     * and empty the global substitution table */
    while (varsubst_constraints->count > 0u)
    {
      b     = varsubst_constraints->first;
      cur   = (BzlaNode *) b->key;
      right = (BzlaNode *) b->data.as_ptr;
      simp  = bzla_node_get_simplified(bzla, cur);
      bzla_hashptr_table_remove(varsubst_constraints, cur, 0, 0);

      if (bzla_node_is_regular(simp)
          && (bzla_node_is_var(simp) || bzla_node_is_uf(simp)))
      {
        assert(bzla_node_is_regular(simp));
        assert(bzla_node_is_var(simp) || bzla_node_is_uf(simp));
        simp_right = bzla_node_get_simplified(bzla, right);
        assert(!bzla_node_is_simplified(simp_right));
        /* In rare cases it may happen that 'cur' simplifies to a variable
         * that was already added to subst. In this case we ignore this
         * substitution. */
        if (!bzla_hashptr_table_get(substs, simp))
        {
          bzla_hashptr_table_add(substs, bzla_node_copy(bzla, simp))
              ->data.as_ptr = bzla_node_copy(bzla, simp_right);
        }
      }
      bzla_node_release(bzla, cur);
      bzla_node_release(bzla, right);
    }
    assert(varsubst_constraints->count == 0u);

    BZLALOG(1, "start variable substitution");

    /* remove cycles from substitution table 'substs' */
    substitute_remove_cycles(bzla, substs);

    /* we rebuild and substiute variables in one pass */
    bzla_substitute_and_rebuild(bzla, substs);

    BZLALOG(1, "end variable substitution");

    /* cleanup, we delete all substitution constraints */
    bzla_iter_hashptr_init(&it, substs);
    while (bzla_iter_hashptr_has_next(&it))
    {
      right = (BzlaNode *) it.bucket->data.as_ptr;
      assert(right);
      left = bzla_iter_hashptr_next(&it);
      assert(bzla_node_is_regular(left));
      assert(bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST)
             || bzla_node_is_proxy(left));
      assert(bzla_node_is_simplified(left)
             || (!bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST)
                 || bzla_node_is_synth(left)));

      /* Count number of performed substitutions. */
      if (bzla_node_is_simplified(left))
      {
        count++;
      }
      bzla_node_release(bzla, left);
      bzla_node_release(bzla, right);
    }

    bzla_hashptr_table_delete(substs);
  }
  bzla->stats.var_substitutions += count;

  delta = bzla_util_time_stamp() - start;
  bzla->time.subst += delta;
  BZLA_MSG(
      bzla->msg, 1, "%d variables substituted in %.1f seconds", count, delta);
  assert(bzla_dbg_check_all_hash_tables_proxy_free(bzla));
  assert(bzla_dbg_check_all_hash_tables_simp_free(bzla));
  assert(bzla_dbg_check_unique_table_children_proxy_free(bzla));
}
