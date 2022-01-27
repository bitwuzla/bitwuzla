/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "bzladbg.h"

#include <limits.h>

#include "bzlalog.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/
/* core                                                                   */
/*------------------------------------------------------------------------*/

bool
bzla_dbg_check_lambdas_static_rho_proxy_free(const Bzla *bzla)
{
  BzlaNode *cur, *data, *key;
  BzlaPtrHashTableIterator it, iit;
  BzlaPtrHashTable *static_rho;

  bzla_iter_hashptr_init(&it, bzla->lambdas);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur        = bzla_iter_hashptr_next(&it);
    static_rho = bzla_node_lambda_get_static_rho(cur);
    if (!static_rho) continue;

    bzla_iter_hashptr_init(&iit, static_rho);
    while (bzla_iter_hashptr_has_next(&iit))
    {
      data = iit.bucket->data.as_ptr;
      key  = bzla_iter_hashptr_next(&iit);
      assert(data);
      if (bzla_node_is_proxy(data)) return false;
      if (bzla_node_is_proxy(key)) return false;
    }
  }
  return true;
}

bool
bzla_dbg_check_unique_table_children_proxy_free(const Bzla *bzla)
{
  uint32_t i, j;
  BzlaNode *cur;

  for (i = 0; i < bzla->nodes_unique_table.size; i++)
    for (cur = bzla->nodes_unique_table.chains[i]; cur; cur = cur->next)
      for (j = 0; j < cur->arity; j++)
        if (bzla_node_is_proxy(cur->e[j]))
        {
          BZLALOG(1,
                  "found proxy node in unique table: %s (parent: %s)",
                  bzla_util_node2string(cur->e[j]),
                  bzla_util_node2string(cur));
          return false;
        }
  return true;
}

bool
bzla_dbg_check_hash_table_proxy_free(BzlaPtrHashTable *table)
{
  BzlaPtrHashTableIterator it;
  BzlaNode *cur;

  bzla_iter_hashptr_init(&it, table);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    if (bzla_node_is_proxy(cur)) return false;
  }
  return true;
}

bool
bzla_dbg_check_all_hash_tables_proxy_free(const Bzla *bzla)
{
  if (!bzla_dbg_check_hash_table_proxy_free(bzla->embedded_constraints))
    return false;
  if (!bzla_dbg_check_hash_table_proxy_free(bzla->unsynthesized_constraints))
    return false;
  if (!bzla_dbg_check_hash_table_proxy_free(bzla->synthesized_constraints))
    return false;
  return true;
}

bool
bzla_dbg_check_hash_table_simp_free(BzlaPtrHashTable *table)
{
  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, table);
  while (bzla_iter_hashptr_has_next(&it))
    if (bzla_node_is_simplified(bzla_iter_hashptr_next(&it))) return false;
  return true;
}

bool
bzla_dbg_check_unique_table_rebuild(const Bzla *bzla)
{
  uint32_t i;
  BzlaNode *cur;

  for (i = 0; i < bzla->nodes_unique_table.size; i++)
    for (cur = bzla->nodes_unique_table.chains[i]; cur; cur = cur->next)
    {
      if (cur->rebuild)
      {
        BZLALOG(1,
                "found node with rebuild flag enabled: %s",
                bzla_util_node2string(cur));
        return false;
      }
    }
  return true;
}

bool
bzla_dbg_check_all_hash_tables_simp_free(const Bzla *bzla)
{
  if (!bzla_dbg_check_hash_table_simp_free(bzla->embedded_constraints))
    return false;
  if (!bzla_dbg_check_hash_table_simp_free(bzla->unsynthesized_constraints))
    return false;
  if (!bzla_dbg_check_hash_table_simp_free(bzla->synthesized_constraints))
    return false;
  return true;
}

bool
bzla_dbg_check_constraints_not_const(const Bzla *bzla)
{
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(cur);
    if (bzla_node_is_bv_const(cur)) return false;
  }

  bzla_iter_hashptr_init(&it, bzla->synthesized_constraints);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    assert(cur);
    if (bzla_node_is_bv_const(cur)) return false;
  }
  return true;
}

bool
bzla_dbg_check_assumptions_simp_free(const Bzla *bzla)
{
  BzlaPtrHashTableIterator it;
  bzla_iter_hashptr_init(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
    if (bzla_node_is_simplified(bzla_iter_hashptr_next(&it))) return false;
  return true;
}

bool
bzla_dbg_check_nodes_simp_free(Bzla *bzla, BzlaNode *nodes[], size_t nnodes)
{
  size_t i;
  int32_t id;
  BzlaNode *cur;
  BzlaPtrHashTableIterator it;
  BzlaIntHashTable *cache;
  BzlaPtrHashTable *rho;
  BzlaNodePtrStack visit;
  bool opt_nondestr_subst;

  BZLA_INIT_STACK(bzla->mm, visit);
  cache              = bzla_hashint_table_new(bzla->mm);
  opt_nondestr_subst = bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST) == 1;

  for (i = 0; i < nnodes; i++)
  {
    BZLA_PUSH_STACK(visit, nodes[i]);
    BZLALOG(3, "  root: %s", bzla_util_node2string(nodes[i]));
  }

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
    id  = bzla_node_get_id(cur);
    BZLALOG(3, "check simp free: %s", bzla_util_node2string(cur));
    if (opt_nondestr_subst && bzla_node_is_synth(cur))
    {
      continue;
    }
    if (bzla_node_is_simplified(cur))
    {
      BZLALOG(3,
              "  simplified: %s",
              bzla_util_node2string(bzla_node_get_simplified(bzla, cur)));
    }
    assert(!bzla_node_is_simplified(cur));

    if (bzla_hashint_table_contains(cache, id)) continue;

    if (bzla_node_is_lambda(cur)
        && (rho = bzla_node_lambda_get_static_rho(cur)))
    {
      bzla_iter_hashptr_init(&it, rho);
      while (bzla_iter_hashptr_has_next(&it))
      {
        BZLA_PUSH_STACK(visit, it.bucket->data.as_ptr);
        BZLA_PUSH_STACK(visit, bzla_iter_hashptr_next(&it));
      }
    }

    bzla_hashint_table_add(cache, id);
    for (i = 0; i < cur->arity; i++)
    {
      BZLA_PUSH_STACK(visit, cur->e[i]);
    }
  }

  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
  return true;
}

bool
bzla_dbg_check_constraints_simp_free(Bzla *bzla)
{
  BzlaNode *cur;
  BzlaNodePtrStack nodes;
  BzlaPtrHashTableIterator it;

  BZLA_INIT_STACK(bzla->mm, nodes);

  bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&it, bzla->assumptions);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(nodes, cur);
  }

  bzla_dbg_check_nodes_simp_free(bzla, nodes.start, BZLA_COUNT_STACK(nodes));
  BZLA_RELEASE_STACK(nodes);
  return true;
}

/*------------------------------------------------------------------------*/
/* exp                                                                    */
/*------------------------------------------------------------------------*/

bool
bzla_dbg_precond_slice_exp(Bzla *bzla,
                           const BzlaNode *exp,
                           uint32_t upper,
                           uint32_t lower)
{
  assert(bzla);
  assert(exp);
  assert(!bzla_node_is_simplified(exp));
  assert(!bzla_node_is_fun(exp));
  assert(upper >= lower);
  assert(upper < bzla_node_bv_get_width(bzla, exp));
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_ext_exp(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));
  return true;
}

bool
bzla_dbg_precond_regular_unary_bv_exp(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(!bzla_node_is_simplified(exp));
  assert(!bzla_node_is_fun(exp));
  assert(bzla_node_is_bv(bzla, exp));
  return true;
}

bool
bzla_dbg_precond_regular_unary_fp_exp(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(!bzla_node_is_simplified(exp));
  assert(!bzla_node_is_fun(exp));
  assert(bzla_node_is_fp(bzla, exp));
  return true;
}

bool
bzla_dbg_precond_unary_fp_to_fp_exp(Bzla *bzla,
                                    const BzlaNode *exp,
                                    const BzlaSortId sort)
{
  assert(bzla);
  assert(exp);
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(!bzla_node_is_simplified(exp));
  assert(bzla_node_is_bv(bzla, exp));
  return true;
}

bool
bzla_dbg_precond_binary_fp_conversion_exp(Bzla *bzla,
                                          const BzlaNode *e0,
                                          const BzlaNode *e1,
                                          const BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(bzla_sort_is_fp(bzla, sort) || bzla_sort_is_bv(bzla, sort));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(bzla_node_is_rm(bzla, e0));
  assert(!bzla_sort_is_fp(bzla, sort) || bzla_node_is_bv(bzla, e1)
         || bzla_node_is_fp(bzla, e1));
  assert(!bzla_sort_is_bv(bzla, sort) || bzla_node_is_fp(bzla, e1));
  return true;
}

bool
bzla_dbg_precond_eq_exp(Bzla *bzla, const BzlaNode *e0, const BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;

  assert(bzla);
  assert(e0);
  assert(e1);

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  assert(real_e0);
  assert(real_e1);
  assert(real_e0->bzla == bzla);
  assert(real_e1->bzla == bzla);
  assert(!bzla_node_is_simplified(real_e0));
  assert(!bzla_node_is_simplified(real_e1));
  assert(bzla_node_get_sort_id(real_e0) == bzla_node_get_sort_id(real_e1));
  assert(real_e0->is_array == real_e1->is_array);
  assert(!bzla_node_is_fun(real_e0)
         || (bzla_node_is_regular(e0) && bzla_node_is_regular(e1)));
  return true;
}

bool
bzla_dbg_precond_concat_exp(Bzla *bzla, const BzlaNode *e0, const BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(!bzla_node_is_fun(e0));
  assert(!bzla_node_is_fun(e1));
  assert(bzla_node_bv_get_width(bzla, e0)
         <= INT32_MAX - bzla_node_bv_get_width(bzla, e1));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_shift_exp(Bzla *bzla, const BzlaNode *e0, const BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(!bzla_node_is_fun(e0));
  assert(!bzla_node_is_fun(e1));
  assert(bzla_node_bv_get_width(bzla, e0) == bzla_node_bv_get_width(bzla, e1));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_regular_binary_bv_exp(Bzla *bzla,
                                       const BzlaNode *e0,
                                       const BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(bzla_node_is_bv(bzla, e0));
  assert(bzla_node_is_bv(bzla, e1));
  assert(bzla_node_get_sort_id(e0) == bzla_node_get_sort_id(e1));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_regular_binary_fp_exp(Bzla *bzla,
                                       const BzlaNode *e0,
                                       const BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(bzla_node_is_fp(bzla, e0));
  assert(bzla_node_is_fp(bzla, e1));
  assert(bzla_node_get_sort_id(e0) == bzla_node_get_sort_id(e1));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_rm_binary_fp_exp(Bzla *bzla,
                                  const BzlaNode *e0,
                                  const BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(bzla_node_is_rm(bzla, e0));
  assert(bzla_node_is_fp(bzla, e1));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_rm_ternary_fp_exp(Bzla *bzla,
                                   const BzlaNode *e0,
                                   const BzlaNode *e1,
                                   const BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(!bzla_node_is_simplified(e2));
  assert(bzla_node_is_rm(bzla, e0));
  assert(bzla_node_is_fp(bzla, e1));
  assert(bzla_node_is_fp(bzla, e2));
  assert(bzla_node_get_sort_id(e1) == bzla_node_get_sort_id(e2));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  assert(bzla_node_real_addr(e2)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_rm_quaternary_fp_exp(Bzla *bzla,
                                      const BzlaNode *e0,
                                      const BzlaNode *e1,
                                      const BzlaNode *e2,
                                      const BzlaNode *e3)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  assert(e3);
  assert(!bzla_node_is_simplified(e0));
  assert(!bzla_node_is_simplified(e1));
  assert(!bzla_node_is_simplified(e2));
  assert(!bzla_node_is_simplified(e3));
  assert(bzla_node_is_rm(bzla, e0));
  assert(bzla_node_is_fp(bzla, e1));
  assert(bzla_node_is_fp(bzla, e2));
  assert(bzla_node_is_fp(bzla, e3));
  assert(bzla_node_get_sort_id(e1) == bzla_node_get_sort_id(e2));
  assert(bzla_node_get_sort_id(e1) == bzla_node_get_sort_id(e3));
  assert(bzla_node_real_addr(e0)->bzla == bzla);
  assert(bzla_node_real_addr(e1)->bzla == bzla);
  assert(bzla_node_real_addr(e2)->bzla == bzla);
  assert(bzla_node_real_addr(e3)->bzla == bzla);
  return true;
}

bool
bzla_dbg_precond_read_exp(Bzla *bzla,
                          const BzlaNode *e_array,
                          const BzlaNode *e_index)
{
  assert(bzla);
  assert(e_array);
  assert(e_index);
  assert(bzla_node_is_regular(e_array));
  assert(bzla_node_is_fun(e_array));
  assert(!bzla_node_is_simplified(e_array));
  assert(!bzla_node_is_simplified(e_index));
  assert(!bzla_node_is_fun(e_index));
  assert(bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(e_array))
         == bzla_node_get_sort_id(e_index));
  assert(bzla_node_real_addr(e_array)->bzla == bzla);
  assert(bzla_node_real_addr(e_index)->bzla == bzla);
  assert(e_array->is_array);
  return true;
}

bool
bzla_dbg_precond_write_exp(Bzla *bzla,
                           const BzlaNode *e_array,
                           const BzlaNode *e_index,
                           const BzlaNode *e_value)
{
  assert(bzla);
  assert(e_array);
  assert(e_index);
  assert(e_value);
  assert(bzla_node_is_regular(e_array));
  assert(bzla_node_is_fun(e_array));
  assert(!bzla_node_is_simplified(e_array));
  assert(!bzla_node_is_simplified(e_index));
  assert(!bzla_node_is_simplified(e_value));
  assert(!bzla_node_is_fun(e_index));
  assert(!bzla_node_is_fun(e_value));
  assert(bzla_sort_array_get_index(bzla, bzla_node_get_sort_id(e_array))
         == bzla_node_get_sort_id(e_index));
  assert(bzla_sort_array_get_element(bzla, bzla_node_get_sort_id(e_array))
         == bzla_node_get_sort_id(e_value));
  assert(bzla_node_real_addr(e_array)->bzla == bzla);
  assert(bzla_node_real_addr(e_index)->bzla == bzla);
  assert(bzla_node_real_addr(e_value)->bzla == bzla);
  assert(e_array->is_array);
  return true;
}

bool
bzla_dbg_precond_cond_exp(Bzla *bzla,
                          const BzlaNode *e_cond,
                          const BzlaNode *e_if,
                          const BzlaNode *e_else)
{
  assert(bzla);
  assert(e_cond);
  assert(e_if);
  assert(e_else);
  assert(!bzla_node_is_simplified(e_cond));
  assert(bzla_node_bv_get_width(bzla, e_cond) == 1);

  BzlaNode *real_e_if, *real_e_else;

  real_e_if   = bzla_node_real_addr(e_if);
  real_e_else = bzla_node_real_addr(e_else);

  assert(!bzla_node_is_simplified(real_e_if));
  assert(!bzla_node_is_simplified(real_e_else));
  assert(bzla_node_get_sort_id(real_e_if)
         == bzla_node_get_sort_id(real_e_else));
  assert(bzla_node_real_addr(e_cond)->bzla == bzla);
  assert(real_e_if->bzla == bzla);
  assert(real_e_else->bzla == bzla);
  assert(real_e_if->is_array == real_e_else->is_array);
  return true;
}

bool
bzla_dbg_precond_apply_exp(Bzla *bzla,
                           const BzlaNode *fun,
                           const BzlaNode *args)
{
  assert(bzla);
  assert(fun);
  assert(args);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_regular(args));
  assert(bzla_node_is_fun(fun));
  assert(bzla_node_is_args(args));
  assert(bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(fun))
         == bzla_node_get_sort_id(args));
  return true;
}

void
bzla_dbg_print_free_params(Bzla *bzla, BzlaNode *n)
{
  BzlaPtrHashBucket *b;
  BzlaIntHashTable *t;
  BzlaIntHashTableIterator it;
  BzlaNode *cur;
  int32_t id;

  b = bzla_hashptr_table_get(bzla->parameterized, n);

  if (!b) return;

  t = b->data.as_ptr;
  bzla_iter_hashint_init(&it, t);
  while (bzla_iter_hashint_has_next(&it))
  {
    id  = bzla_iter_hashint_next(&it);
    cur = bzla_node_get_by_id(bzla, id);
    printf("free param: %s\n", bzla_util_node2string(cur));
  }
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
