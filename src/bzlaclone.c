/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "bzlaaig.h"
#include "bzlaaigvec.h"
#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlalog.h"
#include "bzlamodel.h"
#include "bzlamsg.h"
#include "bzlaproputils.h"
#include "bzlarwcache.h"
#include "bzlasat.h"
#include "bzlaslvaigprop.h"
#include "bzlaslvfun.h"
#include "bzlaslvprop.h"
#include "bzlaslvsls.h"
#include "bzlasort.h"
#include "sat/bzlalgl.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodemap.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

#include <gmp.h>

BZLA_DECLARE_STACK(BzlaNodePtrStackPtr, BzlaNodePtrStack *);
BZLA_DECLARE_STACK(BzlaPtrHashTablePtrPtr, BzlaPtrHashTable **);

/*------------------------------------------------------------------------*/

void *
bzla_clone_key_as_node(BzlaMemMgr *mm, const void *map, const void *key)
{
  assert(map);
  assert(key);

  BzlaNode *exp, *cloned_exp;
  BzlaNodeMap *exp_map;

  (void) mm;
  exp        = (BzlaNode *) key;
  exp_map    = (BzlaNodeMap *) map;
  cloned_exp = bzla_nodemap_mapped(exp_map, exp);
  assert(cloned_exp);
  return cloned_exp;
}

void *
bzla_clone_key_as_str(BzlaMemMgr *mm, const void *map, const void *key)
{
  assert(mm);
  assert(key);

  (void) map;

  return bzla_mem_strdup(mm, (char *) key);
}

void *
bzla_clone_key_as_static_str(BzlaMemMgr *mm, const void *map, const void *key)
{
  (void) mm;
  (void) map;
  return (void *) key;
}

void *
bzla_clone_key_as_bv_tuple(BzlaMemMgr *mm, const void *map, const void *t)
{
  assert(mm);
  assert(t);
  (void) map;
  return bzla_bv_copy_tuple(mm, (BzlaBitVectorTuple *) t);
}

void *
bzla_clone_key_as_rw_cache_tuple(BzlaMemMgr *mm, const void *map, const void *t)
{
  assert(mm);
  assert(t);
  (void) map;

  BzlaRwCacheTuple *res;
  BZLA_CNEW(mm, res);
  memcpy(res, t, sizeof(BzlaRwCacheTuple));
  return res;
}

void
bzla_clone_data_as_node_ptr(BzlaMemMgr *mm,
                            const void *map,
                            BzlaHashTableData *data,
                            BzlaHashTableData *cloned_data)
{
  assert(map);
  assert(data);
  assert(cloned_data);

  BzlaNode *exp, *cloned_exp;
  BzlaNodeMap *exp_map;

  (void) mm;
  exp        = (BzlaNode *) data->as_ptr;
  exp_map    = (BzlaNodeMap *) map;
  cloned_exp = bzla_nodemap_mapped(exp_map, exp);
  assert(cloned_exp);
  cloned_data->as_ptr = cloned_exp;
}

void
bzla_clone_data_as_str_ptr(BzlaMemMgr *mm,
                           const void *str_table,
                           BzlaHashTableData *data,
                           BzlaHashTableData *cloned_data)
{
  assert(str_table);
  assert(data);
  assert(cloned_data);

  char *str;

  (void) mm;
  str = data->as_str;
  assert(bzla_hashptr_table_get((BzlaPtrHashTable *) str_table, str));

  cloned_data->as_str =
      (char *) bzla_hashptr_table_get((BzlaPtrHashTable *) str_table, str)->key;
}

void
bzla_clone_data_as_str(BzlaMemMgr *mm,
                       const void *str_table,
                       BzlaHashTableData *data,
                       BzlaHashTableData *cloned_data)
{
  assert(mm);
  (void) str_table;
  cloned_data->as_str = bzla_mem_strdup(mm, (char *) data->as_str);
}

void
bzla_clone_data_as_int(BzlaMemMgr *mm,
                       const void *map,
                       BzlaHashTableData *data,
                       BzlaHashTableData *cloned_data)
{
  assert(data);
  assert(cloned_data);

  (void) mm;
  (void) map;
  cloned_data->as_int = data->as_int;
}

void
bzla_clone_data_as_dbl(BzlaMemMgr *mm,
                       const void *map,
                       BzlaHashTableData *data,
                       BzlaHashTableData *cloned_data)
{
  assert(data);
  assert(cloned_data);

  (void) mm;
  (void) map;

  cloned_data->as_dbl = data->as_dbl;
}

void
bzla_clone_data_as_bv_ptr(BzlaMemMgr *mm,
                          const void *map,
                          BzlaHashTableData *data,
                          BzlaHashTableData *cloned_data)
{
  assert(mm);
  assert(data);
  assert(cloned_data);

  (void) map;
  cloned_data->as_ptr = bzla_bv_copy(mm, (BzlaBitVector *) data->as_ptr);
}

void
bzla_clone_data_as_ptr_htable(BzlaMemMgr *mm,
                              const void *map,
                              BzlaHashTableData *data,
                              BzlaHashTableData *cloned_data)
{
  assert(mm);
  assert(map);
  assert(data);
  assert(cloned_data);

  BzlaPtrHashTable *table;
  BzlaNodeMap *exp_map;

  table   = (BzlaPtrHashTable *) data->as_ptr;
  exp_map = (BzlaNodeMap *) map;

  cloned_data->as_ptr = bzla_hashptr_table_clone(
      mm, table, bzla_clone_key_as_node, 0, exp_map, 0);
}

void
bzla_clone_data_as_int_htable(BzlaMemMgr *mm,
                              const void *map,
                              BzlaHashTableData *data,
                              BzlaHashTableData *cloned_data)
{
  (void) map;
  assert(mm);
  assert(map);
  assert(data);
  assert(cloned_data);

  BzlaIntHashTable *table, *res;

  table = (BzlaIntHashTable *) data->as_ptr;

  res = bzla_hashint_table_new(mm);

  BZLA_DELETEN(mm, res->keys, res->size);
  BZLA_DELETEN(mm, res->hop_info, res->size);

  res->size  = table->size;
  res->count = table->count;
  BZLA_CNEWN(mm, res->keys, res->size);
  BZLA_CNEWN(mm, res->hop_info, res->size);
  if (table->data) BZLA_CNEWN(mm, res->data, res->size);

  memcpy(res->keys, table->keys, table->size);
  memcpy(res->hop_info, table->hop_info, table->size);
  if (table->data) memcpy(res->data, table->data, table->size);

  cloned_data->as_ptr = res;
}

void
bzla_clone_data_as_bv_ptr_htable(BzlaMemMgr *mm,
                                 const void *map,
                                 BzlaHashTableData *data,
                                 BzlaHashTableData *cloned_data)
{
  assert(mm);
  assert(data);
  assert(cloned_data);

  BzlaPtrHashTable *table;
  table               = (BzlaPtrHashTable *) data->as_ptr;
  cloned_data->as_ptr = bzla_hashptr_table_clone(mm,
                                                 table,
                                                 bzla_clone_key_as_bv_tuple,
                                                 bzla_clone_data_as_bv_ptr,
                                                 map,
                                                 map);
}

/*------------------------------------------------------------------------*/

static void
clone_sorts_unique_table(Bzla *bzla, Bzla *clone)
{
  assert(bzla);
  assert(clone);

  uint32_t i, j;
  BzlaSort *sort, *csort;
  BzlaSortId cid;
  BzlaSortIdStack elements;
  BzlaSortUniqueTable *table, *res;
  BzlaMemMgr *mm;

  mm    = clone->mm;
  table = &bzla->sorts_unique_table;
  res   = &clone->sorts_unique_table;

  BZLA_INIT_STACK(mm, elements);

  BZLA_CNEWN(mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = 0;
  res->mm           = mm;
  BZLA_INIT_STACK(mm, res->id2sort);

  for (i = 0; i < BZLA_COUNT_STACK(table->id2sort); i++)
  {
    sort = BZLA_PEEK_STACK(table->id2sort, i);

    if (!sort)
    {
      BZLA_PUSH_STACK(res->id2sort, 0);
      continue;
    }

    switch (sort->kind)
    {
      case BZLA_BV_SORT: cid = bzla_sort_bv(clone, sort->bitvec.width); break;
      case BZLA_FP_SORT:
        cid = bzla_sort_fp(clone, sort->fp.width_exp, sort->fp.width_sig);
        break;
      case BZLA_FUN_SORT:
        assert(BZLA_PEEK_STACK(res->id2sort, sort->fun.domain->id));
        if (sort->fun.is_array)
        {
          cid = bzla_sort_array(clone,
                                sort->fun.domain->tuple.elements[0]->id,
                                sort->fun.codomain->id);
        }
        else
        {
          cid = bzla_sort_fun(
              clone, sort->fun.domain->id, sort->fun.codomain->id);
        }
        break;

      case BZLA_RM_SORT: cid = bzla_sort_rm(clone); break;

      case BZLA_TUPLE_SORT:
        BZLA_RESET_STACK(elements);
        for (j = 0; j < sort->tuple.num_elements; j++)
          BZLA_PUSH_STACK(elements, sort->tuple.elements[j]->id);
        cid =
            bzla_sort_tuple(clone, elements.start, BZLA_COUNT_STACK(elements));
        break;

      default: cid = 0; break;
    }
    assert(cid);
    csort = BZLA_PEEK_STACK(res->id2sort, cid);
    assert(csort->refs == 1);
    assert(csort->id == sort->id);
    assert(csort->kind == sort->kind);
    assert(csort->table != sort->table);
  }

  /* update sort references (must be the same as in table) */
  assert(BZLA_COUNT_STACK(table->id2sort) == BZLA_COUNT_STACK(res->id2sort));
  for (i = 0; i < BZLA_COUNT_STACK(res->id2sort); i++)
  {
    sort  = BZLA_PEEK_STACK(table->id2sort, i);
    csort = BZLA_PEEK_STACK(res->id2sort, i);
    if (!sort)
    {
      assert(!csort);
      continue;
    }
    assert(csort->id == sort->id);
    assert(csort->parents == sort->parents);
    assert(csort->ext_refs == 0);
    assert(sort->refs == csort->refs - 1 + sort->refs - sort->parents);
    csort->refs     = sort->refs;
    csort->ext_refs = sort->ext_refs;
  }
  assert(res->num_elements == table->num_elements);
  BZLA_RELEASE_STACK(elements);
}

#if 0
static void
clone_sorts_unique_table (BzlaMemMgr * mm,
			  BzlaSortUniqueTable * table,
			  BzlaSortUniqueTable * res)
{
  assert (mm);
  assert (table);
  assert (res);

  uint32_t i, j;
  BzlaSort *sort, *csort, *tmp;
  BzlaSortPtrStack elements;
  
  BZLA_INIT_STACK (elements);

  BZLA_CNEWN (mm, res->chains, table->size);
  res->size = table->size;
  res->num_elements = 0;
  res->mm = mm;
  BZLA_INIT_STACK (res->id2sort);

  for (i = 0; i < BZLA_COUNT_STACK (table->id2sort); i++)
    {
      sort = BZLA_PEEK_STACK (table->id2sort, i);

      if (!sort)
	{
	  BZLA_PUSH_STACK (res->mm, res->id2sort, 0);
	  continue;
	}

      switch (sort->kind)
	{
	  case BZLA_BOOL_SORT:
	    csort = bzla_sort_bool (res);
	    break;

	  case BZLA_BV_SORT:
	    csort = bzla_sort_bv (res, sort->bitvec.len);
	    break;

	  case BZLA_LST_SORT:
	    csort = bzla_sort_lst (res,
			BZLA_PEEK_STACK (res->id2sort, sort->lst.head->id),
			BZLA_PEEK_STACK (res->id2sort, sort->lst.tail->id));
	    break;

	  case BZLA_ARRAY_SORT:
	    csort = bzla_sort_array (res,
			BZLA_PEEK_STACK (res->id2sort, sort->array.index->id),
			BZLA_PEEK_STACK (res->id2sort,
					 sort->array.element->id));
	    break;

	  case BZLA_FUN_SORT:
	    tmp = BZLA_PEEK_STACK (res->id2sort, sort->fun.domain->id);
	    assert (tmp);
	    if (sort->fun.arity > 1)
	      {
		assert (sort->fun.domain->kind == BZLA_TUPLE_SORT);
		assert (tmp->kind == BZLA_TUPLE_SORT);
		assert (sort->fun.arity == tmp->tuple.num_elements);
		csort = bzla_sort_fun (res, tmp->tuple.elements,
			    sort->fun.arity,
			    BZLA_PEEK_STACK (res->id2sort,
					     sort->fun.codomain->id));
	      }
	    else
	      {
		assert (sort->fun.domain->kind != BZLA_TUPLE_SORT
			&& sort->fun.domain->kind != BZLA_LST_SORT);
		csort = bzla_sort_fun (res, &tmp, 1,
			    BZLA_PEEK_STACK (res->id2sort,
					     sort->fun.codomain->id));
	      }
	    break;

	  case BZLA_TUPLE_SORT:
	    BZLA_RESET_STACK (elements);
	    for (j = 0; j < sort->tuple.num_elements; j++)
	      BZLA_PUSH_STACK (mm, elements,
			       BZLA_PEEK_STACK (res->id2sort,
						sort->tuple.elements[j]->id));
	    csort = bzla_sort_tuple (res, elements.start,
				     BZLA_COUNT_STACK (elements));
	    break;

	  default:
	    csort = 0;
	    break;
	}
      assert (csort);
      assert (csort->refs == 1);
      assert (csort->id == sort->id);
      assert (csort->kind == sort->kind);
      assert (csort->table != sort->table);
    }

  /* update sort references (must be the same as in table) */
  assert (BZLA_COUNT_STACK (table->id2sort) == BZLA_COUNT_STACK (res->id2sort));
  for (i = 0; i < BZLA_COUNT_STACK (res->id2sort); i++)
    {
      sort = BZLA_PEEK_STACK (table->id2sort, i);
      csort = BZLA_PEEK_STACK (res->id2sort, i);
      if (!sort)
	{
	  assert (!csort);
	  continue;
	}
      assert (csort->id == sort->id);
      assert (csort->parents == sort->parents);
      assert (csort->ext_refs == 0);
      assert (sort->refs == csort->refs - 1 + sort->refs - sort->parents);
      csort->refs = sort->refs;
      csort->ext_refs = sort->ext_refs;
    }
  assert (res->num_elements == table->num_elements);
  BZLA_RELEASE_STACK (mm, elements);
}
#endif

static BzlaNode *
clone_exp(Bzla *clone,
          BzlaNode *exp,
          BzlaNodePtrPtrStack *parents,
          BzlaNodePtrPtrStack *nodes,
          BzlaNodePtrStack *rhos,
          BzlaNodePtrStack *static_rhos,
          BzlaNodeMap *exp_map,
          bool exp_layer_only,
          bool clone_simplified)
{
  assert(clone);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(parents);
  assert(nodes);
  assert(exp_map);

  uint32_t i;
  BzlaBitVector *bits;
  BzlaFloatingPoint *fp;
  BzlaNode *res;
  BzlaParamNode *param;
  BzlaMemMgr *mm;

  mm = clone->mm;

  res = bzla_mem_malloc(mm, exp->bytes);
  memcpy(res, exp, exp->bytes);

  /* ------------------- BZLA_VAR_NODE_STRUCT (all nodes) -----------------> */
  if (bzla_node_is_bv_const(exp))
  {
    bits = bzla_bv_copy(mm, bzla_node_bv_const_get_bits_ptr(exp));
    bzla_node_bv_const_set_bits(res, bits);
    bits = bzla_bv_copy(mm, bzla_node_bv_const_get_invbits_ptr(exp));
    bzla_node_bv_const_set_invbits(res, bits);
  }
  else if (bzla_node_is_fp_const(exp))
  {
    fp = bzla_fp_copy(clone, bzla_node_fp_const_get_fp(exp));
    bzla_node_fp_const_set_fp(res, fp);
  }

  /* Note: no need to cache aig vectors here (exp->av is unique to exp). */
  if (bzla_node_is_fun(exp))
  {
    if (exp_layer_only)
    {
      res->rho = 0;
    }
    else if (exp->rho)
    {
      BZLA_PUSH_STACK(*rhos, res);
      BZLA_PUSH_STACK(*rhos, exp);
    }
  }
  else if (exp->av)
  {
    res->av = exp_layer_only ? 0 : bzla_aigvec_clone(exp->av, clone->avmgr);
  }

  assert(!exp->next || !bzla_node_is_invalid(exp->next));
  BZLA_PUSH_STACK_IF(exp->next, *nodes, &res->next);

  assert(!bzla_node_is_simplified(exp)
         || !bzla_node_is_invalid(exp->simplified));
  if (clone_simplified || bzla_node_is_proxy(exp))
  {
    BZLA_PUSH_STACK_IF(exp->simplified, *nodes, &res->simplified);
  }
  else
  {
    res->simplified = 0;
  }

  res->bzla = clone;

  assert(!exp->first_parent || !bzla_node_is_invalid(exp->first_parent));
  assert(!exp->last_parent || !bzla_node_is_invalid(exp->last_parent));

  BZLA_PUSH_STACK_IF(exp->first_parent, *parents, &res->first_parent);
  BZLA_PUSH_STACK_IF(exp->last_parent, *parents, &res->last_parent);
  /* <---------------------------------------------------------------------- */

  /* ------------- BZLA_ADDITIONAL_VAR_NODE_STRUCT (all nodes) ------------- */
  if (!bzla_node_is_bv_const(exp) && !bzla_node_is_fp_const(exp))
  {
    if (!bzla_node_is_var(exp) && !bzla_node_is_param(exp))
    {
      if (exp->arity)
      {
        for (i = 0; i < exp->arity; i++)
        {
          res->e[i] = bzla_nodemap_mapped(exp_map, exp->e[i]);
          assert(exp->e[i] != res->e[i]);
          assert(res->e[i]);
        }
      }

      for (i = 0; i < exp->arity; i++)
      {
        assert(!exp->prev_parent[i]
               || !bzla_node_is_invalid(exp->prev_parent[i]));
        assert(!exp->next_parent[i]
               || !bzla_node_is_invalid(exp->next_parent[i]));

        BZLA_PUSH_STACK_IF(exp->prev_parent[i], *parents, &res->prev_parent[i]);
        BZLA_PUSH_STACK_IF(exp->next_parent[i], *parents, &res->next_parent[i]);
      }
    }
  }
  /* <---------------------------------------------------------------------- */

  if (bzla_node_is_param(exp))
  {
    param = (BzlaParamNode *) exp;
    assert(!bzla_node_param_is_bound(exp)
           || !bzla_node_is_invalid(bzla_node_param_get_binder(exp)));
    assert(!param->assigned_exp || !bzla_node_is_invalid(param->assigned_exp));

    BZLA_PUSH_STACK_IF(
        param->binder, *nodes, (BzlaNode **) &((BzlaParamNode *) res)->binder);
    BZLA_PUSH_STACK_IF(param->assigned_exp,
                       *nodes,
                       (BzlaNode **) &((BzlaParamNode *) res)->assigned_exp);
  }

  if (bzla_node_is_binder(exp))
  {
    if (bzla_node_is_lambda(exp) && bzla_node_lambda_get_static_rho(exp))
    {
      BZLA_PUSH_STACK(*static_rhos, res);
      BZLA_PUSH_STACK(*static_rhos, exp);
    }
    assert(!bzla_node_binder_get_body(exp)
           || !bzla_node_is_invalid(bzla_node_binder_get_body(exp)));
    BZLA_PUSH_STACK_IF(bzla_node_binder_get_body(exp),
                       *nodes,
                       &((BzlaBinderNode *) res)->body);
  }

  bzla_nodemap_map(exp_map, exp, res);

  return res;
}

void
bzla_clone_node_ptr_stack(BzlaMemMgr *mm,
                          BzlaNodePtrStack *stack,
                          BzlaNodePtrStack *res,
                          BzlaNodeMap *exp_map,
                          bool is_zero_terminated)
{
  assert(mm);
  assert(stack);
  assert(res);
  assert(exp_map);

  uint32_t i, n;
  BzlaNode *cloned_exp;
  bool has_zero_terminated;

  BZLA_INIT_STACK(mm, *res);
  assert(BZLA_SIZE_STACK(*stack) || !BZLA_COUNT_STACK(*stack));
  if (BZLA_SIZE_STACK(*stack))
  {
    BZLA_NEWN(mm, res->start, BZLA_SIZE_STACK(*stack));
    res->top = res->start;
    res->end = res->start + BZLA_SIZE_STACK(*stack);

    n                   = BZLA_COUNT_STACK(*stack);
    has_zero_terminated = n && !BZLA_PEEK_STACK(*stack, n - 1);
    if (is_zero_terminated && has_zero_terminated) n -= 1;

    for (i = 0; i < n; i++)
    {
      assert((*stack).start[i]);
      cloned_exp = bzla_nodemap_mapped(exp_map, (*stack).start[i]);
      assert(cloned_exp);
      BZLA_PUSH_STACK(*res, cloned_exp);
    }

    if (is_zero_terminated && has_zero_terminated) BZLA_PUSH_STACK(*res, 0);
  }
  assert(BZLA_COUNT_STACK(*stack) == BZLA_COUNT_STACK(*res));
  assert(BZLA_SIZE_STACK(*stack) == BZLA_SIZE_STACK(*res));
}

void
bzla_clone_sort_id_stack(BzlaMemMgr *mm,
                         BzlaSortIdStack *stack,
                         BzlaSortIdStack *res)
{
  assert(mm);
  assert(stack);
  assert(res);

  BZLA_INIT_STACK(mm, *res);
  assert(BZLA_SIZE_STACK(*stack) || !BZLA_COUNT_STACK(*stack));
  if (BZLA_SIZE_STACK(*stack))
  {
    BZLA_NEWN(mm, res->start, BZLA_SIZE_STACK(*stack));
    res->top = res->start;
    res->end = res->start + BZLA_SIZE_STACK(*stack);

    /* sort id stack is zero terminated */
    for (uint32_t i = 0, n = BZLA_COUNT_STACK(*stack) - 1; i < n; i++)
    {
      assert((*stack).start[i]);
      BZLA_PUSH_STACK(*res, BZLA_PEEK_STACK(*stack, i));
    }
    BZLA_PUSH_STACK(*res, 0);
  }
  assert(BZLA_COUNT_STACK(*stack) == BZLA_COUNT_STACK(*res));
  assert(BZLA_SIZE_STACK(*stack) == BZLA_SIZE_STACK(*res));
}

static void
clone_nodes_id_table(Bzla *bzla,
                     Bzla *clone,
                     BzlaNodePtrStack *res,
                     BzlaNodeMap *exp_map,
                     bool exp_layer_only,
                     BzlaNodePtrStack *rhos,
                     bool clone_simplified)
{
  assert(bzla);
  assert(clone);
  assert(res);
  assert(exp_map);

  size_t i;
  int32_t tag;
  BzlaNode **tmp, *exp, *cloned_exp;
  BzlaMemMgr *mm;
  BzlaNodePtrStack *id_table;
  BzlaNodePtrPtrStack parents, nodes;
  BzlaPtrHashTable *t;
  BzlaNodePtrStack static_rhos;

  mm       = clone->mm;
  id_table = &bzla->nodes_id_table;

  BZLA_INIT_STACK(mm, parents);
  BZLA_INIT_STACK(mm, nodes);
  BZLA_INIT_STACK(mm, static_rhos);

  BZLA_INIT_STACK(mm, *res);
  assert(BZLA_SIZE_STACK(*id_table) || !BZLA_COUNT_STACK(*id_table));

  if (BZLA_SIZE_STACK(*id_table))
  {
    BZLA_NEWN(mm, res->start, BZLA_SIZE_STACK(*id_table));
    res->top      = res->start + BZLA_COUNT_STACK(*id_table);
    res->end      = res->start + BZLA_SIZE_STACK(*id_table);
    res->start[0] = 0;

    /* first element (id = 0) is empty */
    for (i = 1; i < BZLA_COUNT_STACK(*id_table); i++)
    {
      exp           = id_table->start[i];
      res->start[i] = exp ? clone_exp(clone,
                                      exp,
                                      &parents,
                                      &nodes,
                                      rhos,
                                      &static_rhos,
                                      exp_map,
                                      exp_layer_only,
                                      clone_simplified)
                          : 0;
      assert(!exp || res->start[i]->id > 0);
      assert(!exp || (size_t) res->start[i]->id == i);
    }
  }
  assert(BZLA_COUNT_STACK(*res) == BZLA_COUNT_STACK(*id_table));
  assert(BZLA_SIZE_STACK(*res) == BZLA_SIZE_STACK(*id_table));

  /* update children, parent, lambda and next pointers of expressions */
  while (!BZLA_EMPTY_STACK(nodes))
  {
    tmp = BZLA_POP_STACK(nodes);
    assert(*tmp);
    *tmp = bzla_nodemap_mapped(exp_map, *tmp);
    assert(*tmp);
  }

  while (!BZLA_EMPTY_STACK(parents))
  {
    tmp = BZLA_POP_STACK(parents);
    assert(*tmp);
    tag  = bzla_node_get_tag(*tmp);
    *tmp = bzla_nodemap_mapped(exp_map, bzla_node_real_addr(*tmp));
    assert(*tmp);
    *tmp = bzla_node_set_tag(*tmp, tag);
  }

  /* clone static_rho tables */
  while (!BZLA_EMPTY_STACK(static_rhos))
  {
    exp        = BZLA_POP_STACK(static_rhos);
    cloned_exp = BZLA_POP_STACK(static_rhos);
    assert(bzla_node_is_lambda(exp));
    assert(bzla_node_is_lambda(cloned_exp));
    t = bzla_node_lambda_get_static_rho(exp);
    assert(t);
    bzla_node_lambda_set_static_rho(
        cloned_exp,
        bzla_hashptr_table_clone(mm,
                                 t,
                                 bzla_clone_key_as_node,
                                 bzla_clone_data_as_node_ptr,
                                 exp_map,
                                 exp_map));
  }

  BZLA_RELEASE_STACK(parents);
  BZLA_RELEASE_STACK(nodes);
  BZLA_RELEASE_STACK(static_rhos);
}

static void
clone_nodes_unique_table(Bzla *bzla, Bzla *clone, BzlaNodeMap *exp_map)
{
  assert(bzla);
  assert(clone);
  assert(exp_map);

  uint32_t i;
  BzlaNodeUniqueTable *table, *res;
  BzlaMemMgr *mm;

  mm    = clone->mm;
  table = &bzla->nodes_unique_table;
  res   = &clone->nodes_unique_table;

  BZLA_CNEWN(mm, res->chains, table->size);
  res->size         = table->size;
  res->num_elements = table->num_elements;

  for (i = 0; i < table->size; i++)
  {
    if (!table->chains[i]) continue;
    res->chains[i] = bzla_nodemap_mapped(exp_map, table->chains[i]);
    assert(res->chains[i]);
  }
}

#define MEM_INT_HASH_TABLE(table)                               \
  ((table) ? sizeof(*(table)) + (table)->size * sizeof(int32_t) \
                 + (table)->size * sizeof(uint8_t)              \
           : 0)

#define MEM_INT_HASH_MAP(table)                                                \
  ((table)                                                                     \
       ? MEM_INT_HASH_TABLE(table) + (table)->size * sizeof(BzlaHashTableData) \
       : 0)

#define MEM_PTR_HASH_TABLE(table)                                           \
  ((table) ? sizeof(*(table)) + (table)->size * sizeof(BzlaPtrHashBucket *) \
                 + (table)->count * sizeof(BzlaPtrHashBucket)               \
           : 0)

#define CHKCLONE_MEM_INT_HASH_TABLE(table, clone)                   \
  do                                                                \
  {                                                                 \
    assert(MEM_INT_HASH_TABLE(table) == MEM_INT_HASH_TABLE(clone)); \
  } while (0)

#define CHKCLONE_MEM_INT_HASH_MAP(table, clone)                 \
  do                                                            \
  {                                                             \
    assert(MEM_INT_HASH_MAP(table) == MEM_INT_HASH_MAP(clone)); \
  } while (0)

#define CHKCLONE_MEM_PTR_HASH_TABLE(table, clone)                   \
  do                                                                \
  {                                                                 \
    assert(MEM_PTR_HASH_TABLE(table) == MEM_PTR_HASH_TABLE(clone)); \
  } while (0)

#define CLONE_PTR_HASH_TABLE(table)                           \
  do                                                          \
  {                                                           \
    clone->table = bzla_hashptr_table_clone(                  \
        mm, bzla->table, bzla_clone_key_as_node, 0, emap, 0); \
    CHKCLONE_MEM_PTR_HASH_TABLE(bzla->table, clone->table);   \
  } while (0)

#define CLONE_PTR_HASH_TABLE_DATA(table, data_func)                      \
  do                                                                     \
  {                                                                      \
    BZLALOG_TIMESTAMP(delta);                                            \
    clone->table = bzla_hashptr_table_clone(                             \
        mm, bzla->table, bzla_clone_key_as_node, data_func, emap, emap); \
    BZLALOG(2,                                                           \
            "  clone " #table " table: %.3f s",                          \
            (bzla_util_time_stamp() - delta));                           \
    CHKCLONE_MEM_PTR_HASH_TABLE(bzla->table, clone->table);              \
  } while (0)

#if 0
#define CLONE_INT_HASH_MAP_DATA(table, data_func)                         \
  do                                                                      \
  {                                                                       \
    BZLALOG_TIMESTAMP(delta);                                             \
    clone->table = bzla_hashint_map_clone(mm, bzla->table, data_func, 0); \
    BZLALOG(2,                                                            \
            "  clone " #table " table: %.3f s",                           \
            (bzla_util_time_stamp() - delta));                            \
    CHKCLONE_MEM_INT_HASH_MAP(bzla->table, clone->table);                 \
  } while (0)
#endif

#define MEM_BITVEC(bv) ((bv) ? bzla_bv_size(bv) : 0)

static Bzla *
clone_aux_bzla(Bzla *bzla,
               BzlaNodeMap **exp_map,
               bool exp_layer_only,
               bool clone_slv,
               bool clone_simplified)
{
  assert(bzla);
  assert(exp_layer_only
         || bzla_sat_mgr_has_clone_support(bzla_get_sat_mgr(bzla)));
  Bzla *clone;
  BzlaNodeMap *emap = 0;
  BzlaMemMgr *mm;
  double start, delta;
  uint32_t i, len;
  char *prefix, *clone_prefix;
  BzlaNode *exp, *cloned_exp;
  BzlaPtrHashTableIterator pit;
  BzlaNodePtrStack rhos;
#ifndef NDEBUG
  uint32_t h;
  size_t allocated;
  BzlaNode *cur;
  BzlaAIGMgr *amgr;
  BzlaBVAss *bvass;
  BzlaFunAss *funass;
  BzlaPtrHashTableIterator cpit, ncpit;
  BzlaIntHashTableIterator iit, ciit;
  BzlaSort *sort;
  char **ind, **val;
  amgr = exp_layer_only ? 0 : bzla_get_aig_mgr(bzla);
  BzlaHashTableData *data, *cdata;
  BzlaOption o;
#endif

  BZLALOG(2, "start cloning bzla %p ...", bzla);
  start = bzla_util_time_stamp();
  bzla->stats.clone_calls += 1;

  mm = bzla_mem_mgr_new();
  BZLA_CNEW(mm, clone);
#ifndef NDEBUG
  allocated = sizeof(Bzla);
#endif
  memcpy(clone, bzla, sizeof(Bzla));
  clone->mm  = mm;
  clone->rng = bzla_rng_clone(bzla->rng, mm);
#ifndef NDEBUG
  allocated += sizeof(BzlaRNG);
  allocated += sizeof(gmp_randstate_t);
#endif

  BZLA_CLR(&clone->cbs);
  bzla_opt_clone_opts(bzla, clone);
#ifndef NDEBUG
  allocated += BZLA_OPT_NUM_OPTS * sizeof(BzlaOpt);
  for (o = bzla_opt_first(bzla); bzla_opt_is_valid(bzla, o);
       o = bzla_opt_next(bzla, o))
  {
    if (bzla->options[o].valstr)
      allocated += strlen(bzla->options[o].valstr) + 1;
    if (bzla->options[o].options)
      allocated += MEM_PTR_HASH_TABLE(clone->options[o].options)
                   + clone->options[o].options->count * sizeof(BzlaOptHelp);
  }
  allocated += MEM_PTR_HASH_TABLE(clone->str2opt);
#endif
  assert(allocated == clone->mm->allocated);

  /* always auto cleanup internal and external references (may be dangling
   * otherise) */
  bzla_opt_set(clone, BZLA_OPT_AUTO_CLEANUP, 1);
  bzla_opt_set(clone, BZLA_OPT_AUTO_CLEANUP_INTERNAL, 1);

  if (exp_layer_only)
  {
    /* reset */
    clone->bzla_sat_bzla_called = 0;
    clone->last_sat_result      = 0;
    bzla_reset_time(clone);
#ifndef NDEBUG
    /* we need to explicitely reset the pointer to the table, since
     * it is the memcpy-ied pointer of bzla->stats.rw_rules_applied */
    clone->stats.rw_rules_applied = 0;
#endif
    bzla_reset_stats(clone);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE(clone->stats.rw_rules_applied);
    assert(allocated == clone->mm->allocated);
#endif
  }

  clone->msg = bzla_msg_new(clone);
  assert((allocated += sizeof(BzlaMsg)) == clone->mm->allocated);

  /* set msg prefix for clone */
  clone_prefix = "clone";
  len          = bzla->msg->prefix ? strlen(bzla->msg->prefix) : 0;
  len += strlen(clone_prefix) + 1;
#ifndef NDEBUG
  allocated += len + 1;
#endif
  BZLA_NEWN(clone->mm, prefix, len + 1);
  sprintf(prefix, "%s>%s", bzla->msg->prefix, clone_prefix);
  bzla_set_msg_prefix(clone, prefix);
  BZLA_DELETEN(clone->mm, prefix, len + 1);

  if (exp_layer_only)
  {
    clone->bv_assignments = bzla_ass_new_bv_list(mm);
    assert((allocated += sizeof(BzlaBVAssList)) == clone->mm->allocated);
  }
  else
  {
    BZLALOG_TIMESTAMP(delta);
    clone->bv_assignments =
        bzla_ass_clone_bv_list(clone->mm, bzla->bv_assignments);
    BZLALOG(
        1, "  clone BV assignments: %.3f s", (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
    for (bvass = bzla->bv_assignments->first; bvass; bvass = bvass->next)
      allocated += sizeof(BzlaBVAss) + strlen(bzla_ass_get_bv_str(bvass)) + 1;
    assert((allocated += sizeof(BzlaBVAssList)) == clone->mm->allocated);
#endif
  }

  if (exp_layer_only)
  {
    clone->fun_assignments = bzla_ass_new_fun_list(mm);
    assert((allocated += sizeof(BzlaFunAssList)) == clone->mm->allocated);
  }
  else
  {
    BZLALOG_TIMESTAMP(delta);
    clone->fun_assignments =
        bzla_ass_clone_fun_list(clone->mm, bzla->fun_assignments);
    BZLALOG(2,
            "  clone array assignments: %.3f s",
            (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
    for (funass = bzla->fun_assignments->first; funass; funass = funass->next)
    {
      allocated += sizeof(BzlaFunAss) + 2 * funass->size * sizeof(char *);
      bzla_ass_get_fun_indices_values(funass, &ind, &val, funass->size);
      for (i = 0; i < funass->size; i++)
        allocated += strlen(ind[i]) + 1 + strlen(val[i]) + 1;
    }
    assert((allocated += sizeof(BzlaFunAssList)) == clone->mm->allocated);
#endif
  }

  if (bzla->avmgr)
  {
    if (exp_layer_only)
    {
      clone->avmgr = bzla_aigvec_mgr_new(clone);
      assert((allocated += sizeof(BzlaAIGVecMgr) + sizeof(BzlaAIGMgr)
                           + sizeof(BzlaSATMgr)
                           /* true and false AIGs */
                           + 2 * sizeof(BzlaAIG *)
                           + sizeof(int32_t)) /* unique table chains */
             == clone->mm->allocated);
    }
    else
    {
      BZLALOG_TIMESTAMP(delta);
      clone->avmgr = bzla_aigvec_mgr_clone(clone, bzla->avmgr);
      BZLALOG(2, "  clone AIG mgr: %.3f s", (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
      allocated +=
          sizeof(BzlaAIGVecMgr) + sizeof(BzlaAIGMgr)
          + sizeof(BzlaSATMgr)
          /* memory of AIG nodes */
          + (amgr->cur_num_aigs + amgr->cur_num_aig_vars) * sizeof(BzlaAIG)
          /* children for AND AIGs */
          + amgr->cur_num_aigs * sizeof(int32_t) * 2
          /* unique table chain */
          + amgr->table.size * sizeof(int32_t)
          + BZLA_SIZE_STACK(amgr->id2aig) * sizeof(BzlaAIG *)
          + BZLA_SIZE_STACK(amgr->cnfid2aig) * sizeof(int32_t);
#ifdef BZLA_USE_LINGELING
      assert(strcmp(amgr->smgr->name, "Lingeling") == 0
             || strcmp(amgr->smgr->name, "DIMACS Printer") == 0);
      assert(strcmp(amgr->smgr->name, "DIMACS Printer") != 0
             || strcmp(((BzlaCnfPrinter *) amgr->smgr->solver)->smgr->name,
                       "Lingeling")
                    == 0);
      allocated += amgr->smgr->solver ? sizeof(BzlaLGL) : 0;
      if (strcmp(amgr->smgr->name, "DIMACS Printer") == 0)
      {
        BzlaCnfPrinter *cnf_printer = ((BzlaCnfPrinter *) amgr->smgr->solver);
        allocated +=
            sizeof(BzlaCnfPrinter) + sizeof(BzlaSATMgr)
            + BZLA_SIZE_STACK(cnf_printer->clauses) * sizeof(int32_t)
            + BZLA_SIZE_STACK(cnf_printer->assumptions) * sizeof(int32_t);
      }
#endif
      assert(allocated == clone->mm->allocated);
#endif
    }
  }

  BZLALOG_TIMESTAMP(delta);
  clone_sorts_unique_table(bzla, clone);
  BZLALOG(2,
          "  clone sorts unique table: %.3f s",
          (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
  allocated +=
      bzla->sorts_unique_table.size * sizeof(BzlaSort *)
      + bzla->sorts_unique_table.num_elements * sizeof(BzlaSort)
      + BZLA_SIZE_STACK(bzla->sorts_unique_table.id2sort) * sizeof(BzlaSort *);
  for (i = 0; i < BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort); i++)
  {
    sort = BZLA_PEEK_STACK(bzla->sorts_unique_table.id2sort, i);
    if (!sort || sort->kind != BZLA_TUPLE_SORT) continue;
    allocated += sort->tuple.num_elements * sizeof(BzlaSort *);
  }
  assert(allocated == clone->mm->allocated);
#endif

  emap = bzla_nodemap_new(clone);
  assert((allocated += sizeof(*emap) + MEM_PTR_HASH_TABLE(emap->table))
         == clone->mm->allocated);

  BZLA_INIT_STACK(bzla->mm, rhos);
  BZLALOG_TIMESTAMP(delta);
  clone_nodes_id_table(bzla,
                       clone,
                       &clone->nodes_id_table,
                       emap,
                       exp_layer_only,
                       &rhos,
                       clone_simplified);
  BZLALOG(
      2, "  clone nodes id table: %.3f s", (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
  for (i = 1; i < BZLA_COUNT_STACK(bzla->nodes_id_table); i++)
  {
    if (!(cur = BZLA_PEEK_STACK(bzla->nodes_id_table, i))) continue;
    allocated += cur->bytes;
    if (bzla_node_is_bv_const(cur))
    {
      allocated += MEM_BITVEC(bzla_node_bv_const_get_bits_ptr(cur));
      allocated += MEM_BITVEC(bzla_node_bv_const_get_invbits_ptr(cur));
    }
    else if (bzla_node_is_fp_const(cur))
    {
      allocated += bzla_fp_get_bytes(cur);
    }
    if (!exp_layer_only)
    {
      if (!bzla_node_is_fun(cur) && cur->av)
      {
        allocated += sizeof(*(cur->av)) + cur->av->width * sizeof(BzlaAIG *);
      }
    }
    if (bzla_node_is_lambda(cur) && bzla_node_lambda_get_static_rho(cur))
    {
      allocated += MEM_PTR_HASH_TABLE(bzla_node_lambda_get_static_rho(cur));
    }
  }
  /* Note: hash table is initialized with size 1 */
  allocated += (emap->table->size - 1) * sizeof(BzlaPtrHashBucket *)
               + emap->table->count * sizeof(BzlaPtrHashBucket)
               + BZLA_SIZE_STACK(bzla->nodes_id_table) * sizeof(BzlaNode *);
  assert(allocated == clone->mm->allocated);
#endif

  clone->true_exp = bzla_nodemap_mapped(emap, bzla->true_exp);
  assert(clone->true_exp);

  BZLALOG_TIMESTAMP(delta);
  clone_nodes_unique_table(bzla, clone, emap);
  BZLALOG(2,
          "  clone nodes unique table: %.3f s",
          (bzla_util_time_stamp() - delta));
  assert((allocated += bzla->nodes_unique_table.size * sizeof(BzlaNode *))
         == clone->mm->allocated);

  clone->node2symbol = bzla_hashptr_table_clone(mm,
                                                bzla->node2symbol,
                                                bzla_clone_key_as_node,
                                                bzla_clone_data_as_str,
                                                emap,
                                                NULL);
#ifndef NDEBUG
  bzla_iter_hashptr_init(&pit, bzla->node2symbol);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    allocated += strlen(bzla_iter_hashptr_next_data(&pit)->as_str) + 1;
  }
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->node2symbol))
         == clone->mm->allocated);
#endif

  CLONE_PTR_HASH_TABLE_DATA(inputs, bzla_clone_data_as_int);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->inputs))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(bv_vars);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->bv_vars))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(ufs);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->ufs)) == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA(lambdas, bzla_clone_data_as_int);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->lambdas))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA(quantifiers, bzla_clone_data_as_int);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->quantifiers))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA(feqs, bzla_clone_data_as_int);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->feqs)) == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA(substitutions, bzla_clone_data_as_node_ptr);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->substitutions))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE_DATA(varsubst_constraints, bzla_clone_data_as_node_ptr);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->varsubst_constraints))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(embedded_constraints);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->embedded_constraints))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(unsynthesized_constraints);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->unsynthesized_constraints))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(synthesized_constraints);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->synthesized_constraints))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(assumptions);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->assumptions))
         == clone->mm->allocated);
  CLONE_PTR_HASH_TABLE(orig_assumptions);
  assert((allocated += MEM_PTR_HASH_TABLE(bzla->orig_assumptions))
         == clone->mm->allocated);

  clone->assertions_cache =
      bzla_hashint_table_clone(clone->mm, bzla->assertions_cache);
  assert((allocated += MEM_INT_HASH_TABLE(bzla->assertions_cache))
         == clone->mm->allocated);

  bzla_clone_node_ptr_stack(
      mm, &bzla->assertions, &clone->assertions, emap, false);
  assert((allocated += BZLA_SIZE_STACK(bzla->assertions) * sizeof(BzlaNode *))
         == clone->mm->allocated);

  BZLA_INIT_STACK(clone->mm, clone->assertions_trail);
  for (i = 0; i < BZLA_COUNT_STACK(bzla->assertions_trail); i++)
    BZLA_PUSH_STACK(clone->assertions_trail,
                    BZLA_PEEK_STACK(bzla->assertions_trail, i));
  BZLA_ADJUST_STACK(bzla->assertions_trail, clone->assertions_trail);
  assert(
      (allocated += BZLA_SIZE_STACK(bzla->assertions_trail) * sizeof(uint32_t))
      == clone->mm->allocated);

  if (bzla->bv_model)
  {
    clone->bv_model = bzla_model_clone_bv(clone, bzla->bv_model, false);
#ifndef NDEBUG
    bzla_iter_hashint_init(&iit, bzla->bv_model);
    bzla_iter_hashint_init(&ciit, clone->bv_model);
    while (bzla_iter_hashint_has_next(&iit))
    {
      data  = bzla_iter_hashint_next_data(&iit);
      cdata = bzla_iter_hashint_next_data(&ciit);
      assert(bzla_bv_size((BzlaBitVector *) data->as_ptr)
             == bzla_bv_size((BzlaBitVector *) cdata->as_ptr));
      allocated += bzla_bv_size((BzlaBitVector *) cdata->as_ptr);
    }
#endif
  }
  assert((allocated += MEM_INT_HASH_MAP(bzla->bv_model))
         == clone->mm->allocated);
#ifndef NDEBUG
  if (!exp_layer_only && bzla->stats.rw_rules_applied)
  {
    clone->stats.rw_rules_applied =
        bzla_hashptr_table_clone(mm,
                                 bzla->stats.rw_rules_applied,
                                 bzla_clone_key_as_static_str,
                                 bzla_clone_data_as_int,
                                 0,
                                 0);
    assert((allocated += MEM_PTR_HASH_TABLE(bzla->stats.rw_rules_applied))
           == clone->mm->allocated);
  }
#endif
  if (bzla->fun_model)
  {
    clone->fun_model = bzla_model_clone_fun(clone, bzla->fun_model, false);
#ifndef NDEBUG
    bzla_iter_hashint_init(&iit, bzla->fun_model);
    bzla_iter_hashint_init(&ciit, clone->fun_model);
    while (bzla_iter_hashint_has_next(&iit))
    {
      data  = bzla_iter_hashint_next_data(&iit);
      cdata = bzla_iter_hashint_next_data(&ciit);
      assert(MEM_PTR_HASH_TABLE((BzlaPtrHashTable *) data->as_ptr)
             == MEM_PTR_HASH_TABLE((BzlaPtrHashTable *) cdata->as_ptr));
      allocated += MEM_PTR_HASH_TABLE((BzlaPtrHashTable *) data->as_ptr);
      bzla_iter_hashptr_init(&ncpit, ((BzlaPtrHashTable *) data->as_ptr));
      while (bzla_iter_hashptr_has_next(&ncpit))
      {
        allocated += bzla_bv_size((BzlaBitVector *) ncpit.bucket->data.as_ptr);
        allocated += bzla_bv_size_tuple(
            (BzlaBitVectorTuple *) bzla_iter_hashptr_next(&ncpit));
      }
    }
#endif
  }
  assert((allocated += MEM_INT_HASH_MAP(bzla->fun_model))
         == clone->mm->allocated);

  /* NOTE: we need bv_model for cloning rhos */
  while (!BZLA_EMPTY_STACK(rhos))
  {
    exp        = BZLA_POP_STACK(rhos);
    cloned_exp = BZLA_POP_STACK(rhos);
    assert(bzla_node_is_fun(exp));
    assert(bzla_node_is_fun(cloned_exp));
    assert(exp->rho);
    cloned_exp->rho = bzla_hashptr_table_clone(mm,
                                               exp->rho,
                                               bzla_clone_key_as_node,
                                               bzla_clone_data_as_node_ptr,
                                               emap,
                                               emap);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE(cloned_exp->rho);
#endif
  }
  BZLA_RELEASE_STACK(rhos);
  assert(allocated == clone->mm->allocated);

  if (exp_layer_only)
  {
    BZLA_INIT_STACK(mm, clone->functions_with_model);
    /* we need to decrement the reference count of the cloned expressions
     * that were pushed onto the functions_with_model stack. */
    for (i = 0; i < BZLA_COUNT_STACK(bzla->functions_with_model); i++)
      bzla_node_release(
          clone,
          bzla_nodemap_mapped(emap,
                              BZLA_PEEK_STACK(bzla->functions_with_model, i)));
  }
  else
  {
    BZLALOG_TIMESTAMP(delta);
    bzla_clone_node_ptr_stack(mm,
                              &bzla->functions_with_model,
                              &clone->functions_with_model,
                              emap,
                              false);
    BZLALOG(2,
            "  clone functions_with_model: %.3f s",
            bzla_util_time_stamp() - delta);
    assert((allocated +=
            BZLA_SIZE_STACK(bzla->functions_with_model) * sizeof(BzlaNode *))
           == clone->mm->allocated);
  }

  BZLALOG_TIMESTAMP(delta);
  bzla_clone_node_ptr_stack(mm, &bzla->outputs, &clone->outputs, emap, false);
  BZLALOG(2, "  clone outputs: %.3f s", bzla_util_time_stamp() - delta);
  assert((allocated += BZLA_SIZE_STACK(bzla->outputs) * sizeof(BzlaNode *))
         == clone->mm->allocated);

  BZLALOG_TIMESTAMP(delta);
  clone->parameterized = bzla_hashptr_table_clone(mm,
                                                  bzla->parameterized,
                                                  bzla_clone_key_as_node,
                                                  bzla_clone_data_as_int_htable,
                                                  emap,
                                                  emap);
  BZLALOG(2,
          "  clone parameterized table: %.3f s",
          (bzla_util_time_stamp() - delta));
#ifndef NDEBUG
  CHKCLONE_MEM_PTR_HASH_TABLE(bzla->parameterized, clone->parameterized);
  allocated += MEM_PTR_HASH_TABLE(bzla->parameterized);
  bzla_iter_hashptr_init(&pit, bzla->parameterized);
  bzla_iter_hashptr_init(&cpit, clone->parameterized);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    assert(bzla_hashint_table_size(pit.bucket->data.as_ptr)
           == bzla_hashint_table_size(cpit.bucket->data.as_ptr));
    allocated += bzla_hashint_table_size(cpit.bucket->data.as_ptr);
    (void) bzla_iter_hashptr_next(&pit);
    (void) bzla_iter_hashptr_next(&cpit);
  }
  assert(allocated == clone->mm->allocated);
#endif
  BZLA_NEW(mm, clone->rw_cache);
  memcpy(clone->rw_cache, bzla->rw_cache, sizeof(BzlaRwCache));
  clone->rw_cache->bzla  = clone;
  clone->rw_cache->cache = bzla_hashptr_table_clone(
      mm, bzla->rw_cache->cache, bzla_clone_key_as_rw_cache_tuple, 0, 0, 0);
#ifndef NDEBUG
  CHKCLONE_MEM_PTR_HASH_TABLE(bzla->rw_cache->cache, clone->rw_cache->cache);
  allocated += sizeof(*bzla->rw_cache);
  allocated += bzla->rw_cache->cache->count * sizeof(BzlaRwCacheTuple);
  allocated += MEM_PTR_HASH_TABLE(bzla->rw_cache->cache);
#endif

  /* move synthesized constraints to unsynthesized if we only clone the exp
   * layer */
  if (exp_layer_only)
  {
#ifndef NDEBUG
    allocated -= MEM_PTR_HASH_TABLE(clone->synthesized_constraints);
    allocated -= MEM_PTR_HASH_TABLE(clone->unsynthesized_constraints);
#endif
    bzla_iter_hashptr_init(&pit, clone->synthesized_constraints);
    while (bzla_iter_hashptr_has_next(&pit))
    {
      exp = bzla_iter_hashptr_next(&pit);
      bzla_hashptr_table_add(clone->unsynthesized_constraints, exp);
    }
    bzla_hashptr_table_delete(clone->synthesized_constraints);
    clone->synthesized_constraints =
        bzla_hashptr_table_new(mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
#ifndef NDEBUG
    allocated += MEM_PTR_HASH_TABLE(clone->synthesized_constraints);
    allocated += MEM_PTR_HASH_TABLE(clone->unsynthesized_constraints);
    assert(allocated == clone->mm->allocated);
#endif
  }

  if (clone_slv && bzla->slv)
    clone->slv = bzla->slv->api.clone(clone, bzla->slv, emap);
  else
    clone->slv = 0;
  assert(!clone_slv || (bzla->slv && clone->slv)
         || (!bzla->slv && !clone->slv));
#ifndef NDEBUG
  if (clone->slv)
  {
    if (clone->slv->kind == BZLA_FUN_SOLVER_KIND)
    {
      BzlaFunSolver *slv  = BZLA_FUN_SOLVER(bzla);
      BzlaFunSolver *cslv = BZLA_FUN_SOLVER(clone);

      allocated += sizeof(BzlaFunSolver);

      allocated += MEM_PTR_HASH_TABLE(slv->lemmas);
      allocated += BZLA_SIZE_STACK(slv->cur_lemmas) * sizeof(BzlaNode *);
      allocated += BZLA_SIZE_STACK(slv->constraints) * sizeof(BzlaNode *);

      if (slv->score)
      {
        h = bzla_opt_get(bzla, BZLA_OPT_FUN_JUST_HEURISTIC);
        if (h == BZLA_JUST_HEUR_BRANCH_MIN_APP)
        {
          CHKCLONE_MEM_PTR_HASH_TABLE(slv->score, cslv->score);
          allocated += MEM_PTR_HASH_TABLE(slv->score);

          bzla_iter_hashptr_init(&pit, slv->score);
          bzla_iter_hashptr_init(&cpit, cslv->score);
          while (bzla_iter_hashptr_has_next(&pit))
          {
            assert(
                MEM_PTR_HASH_TABLE((BzlaPtrHashTable *) pit.bucket->data.as_ptr)
                == MEM_PTR_HASH_TABLE(
                    (BzlaPtrHashTable *) cpit.bucket->data.as_ptr));
            allocated += MEM_PTR_HASH_TABLE(
                (BzlaPtrHashTable *) pit.bucket->data.as_ptr);
            (void) bzla_iter_hashptr_next(&pit);
            (void) bzla_iter_hashptr_next(&cpit);
          }
        }
        else
        {
          assert(h == BZLA_JUST_HEUR_BRANCH_MIN_DEP);
          allocated += MEM_PTR_HASH_TABLE(slv->score);
        }
      }

      assert(BZLA_SIZE_STACK(slv->stats.lemmas_size)
             == BZLA_SIZE_STACK(cslv->stats.lemmas_size));
      assert(BZLA_COUNT_STACK(slv->stats.lemmas_size)
             == BZLA_COUNT_STACK(cslv->stats.lemmas_size));
      allocated += BZLA_SIZE_STACK(slv->stats.lemmas_size) * sizeof(uint32_t);
    }
    else if (clone->slv->kind == BZLA_SLS_SOLVER_KIND)
    {
      BzlaSLSMove *m;
      BzlaSLSSolver *slv  = BZLA_SLS_SOLVER(bzla);
      BzlaSLSSolver *cslv = BZLA_SLS_SOLVER(clone);

      CHKCLONE_MEM_INT_HASH_MAP(slv->roots, cslv->roots);
      CHKCLONE_MEM_INT_HASH_MAP(slv->score, cslv->score);
      CHKCLONE_MEM_INT_HASH_MAP(slv->weights, cslv->weights);

      allocated += sizeof(BzlaSLSSolver) + MEM_INT_HASH_MAP(cslv->roots)
                   + MEM_INT_HASH_MAP(cslv->score)
                   + MEM_INT_HASH_MAP(cslv->weights);

      if (slv->weights)
        allocated += slv->weights->count * sizeof(BzlaSLSConstrData);

      assert(BZLA_SIZE_STACK(slv->moves) == BZLA_SIZE_STACK(cslv->moves));
      assert(BZLA_COUNT_STACK(slv->moves) == BZLA_COUNT_STACK(cslv->moves));

      allocated += BZLA_SIZE_STACK(cslv->moves) * sizeof(BzlaSLSMove *)
                   + BZLA_COUNT_STACK(cslv->moves) * sizeof(BzlaSLSMove);

      for (i = 0; i < BZLA_COUNT_STACK(cslv->moves); i++)
      {
        assert(BZLA_PEEK_STACK(cslv->moves, i));
        m = BZLA_PEEK_STACK(cslv->moves, i);
        assert(MEM_PTR_HASH_TABLE(m->cans)
               == MEM_PTR_HASH_TABLE(BZLA_PEEK_STACK(cslv->moves, i)->cans));
        allocated += MEM_PTR_HASH_TABLE(m->cans);
        bzla_iter_hashint_init(&iit, m->cans);
        while (bzla_iter_hashint_has_next(&iit))
          allocated += bzla_bv_size(bzla_iter_hashint_next_data(&iit)->as_ptr);
      }

      if (cslv->max_cans)
      {
        assert(slv->max_cans);
        assert(slv->max_cans->count == cslv->max_cans->count);
        allocated += MEM_PTR_HASH_TABLE(cslv->max_cans);
        bzla_iter_hashint_init(&iit, cslv->max_cans);
        while (bzla_iter_hashint_has_next(&iit))
          allocated += bzla_bv_size(bzla_iter_hashint_next_data(&iit)->as_ptr);
      }
    }
    else if (clone->slv->kind == BZLA_PROP_SOLVER_KIND)
    {
      BzlaPropSolver *slv  = BZLA_PROP_SOLVER(bzla);
      BzlaPropSolver *cslv = BZLA_PROP_SOLVER(clone);

      CHKCLONE_MEM_INT_HASH_MAP(slv->roots, cslv->roots);
      CHKCLONE_MEM_INT_HASH_MAP(slv->score, cslv->score);

      allocated +=
          sizeof(BzlaPropSolver) + MEM_PTR_HASH_TABLE(cslv->roots)
          + MEM_PTR_HASH_TABLE(cslv->score)
#ifndef NDEBUG
          + BZLA_SIZE_STACK(cslv->prop_path) * sizeof(BzlaPropEntailInfo);
#endif
      +BZLA_SIZE_STACK(cslv->toprop) * sizeof(BzlaPropEntailInfo);
      for (i = 0; i < BZLA_COUNT_STACK(cslv->toprop); i++)
        allocated += MEM_BITVEC(BZLA_PEEK_STACK(cslv->toprop, i).bvexp);
    }
    else if (clone->slv->kind == BZLA_AIGPROP_SOLVER_KIND)
    {
      allocated += sizeof(BzlaAIGPropSolver);
    }

    assert(allocated == clone->mm->allocated);
  }
#endif

  clone->word_blaster = bzla_fp_word_blaster_clone(bzla, clone, emap);
  assert(allocated == clone->mm->allocated);

#ifndef NDEBUG
  clone->clone = NULL;
#endif
  clone->close_apitrace = 0;

  if (exp_map)
    *exp_map = emap;
  else
    bzla_nodemap_delete(emap);

#ifndef NDEBUG
  /* flag sanity checks */
  bzla_iter_hashptr_init(&pit, bzla->synthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->unsynthesized_constraints);
  bzla_iter_hashptr_queue(&pit, bzla->embedded_constraints);
  while (bzla_iter_hashptr_has_next(&pit))
  {
    exp = bzla_iter_hashptr_next(&pit);
    assert(bzla_node_real_addr(exp)->constraint);
  }
#endif

  bzla->time.cloning += bzla_util_time_stamp() - start;
  BZLALOG(2, "cloning total: %.3f s", bzla->time.cloning);
  return clone;
}

Bzla *
bzla_clone(Bzla *bzla)
{
  assert(bzla);
  return clone_aux_bzla(bzla,
                        0,
                        !bzla_sat_mgr_has_clone_support(bzla_get_sat_mgr(bzla)),
                        true,
                        true);
}

Bzla *
bzla_clone_exp_layer(Bzla *bzla, BzlaNodeMap **exp_map, bool clone_simplified)
{
  assert(bzla);
  return clone_aux_bzla(bzla, exp_map, true, true, clone_simplified);
}

Bzla *
bzla_clone_formula(Bzla *bzla)
{
  assert(bzla);
  return clone_aux_bzla(bzla, 0, true, false, true);
}

BzlaSortId
bzla_clone_recursively_rebuild_sort(Bzla *bzla, Bzla *clone, BzlaSortId sort)
{
  uint32_t i;
  BzlaSort *s;
  BzlaSortId r, s0, s1;
  BzlaSortPtrStack sort_stack;
  BzlaIntHashTable *map;
  BzlaHashTableData *d;
  BzlaMemMgr *mm;
  BzlaSortIdStack sort_ids;

  mm  = bzla->mm;
  map = bzla_hashint_map_new(mm);

  s = bzla_sort_get_by_id(bzla, sort);

  BZLA_INIT_STACK(mm, sort_ids);
  BZLA_INIT_STACK(mm, sort_stack);
  BZLA_PUSH_STACK(sort_stack, s);
  while (!BZLA_EMPTY_STACK(sort_stack))
  {
    s = BZLA_POP_STACK(sort_stack);
    d = bzla_hashint_map_get(map, s->id);
    if (!d)
    {
      bzla_hashint_map_add(map, s->id);

      BZLA_PUSH_STACK(sort_stack, s);
      switch (s->kind)
      {
        case BZLA_ARRAY_SORT:
          BZLA_PUSH_STACK(sort_stack, s->array.element);
          BZLA_PUSH_STACK(sort_stack, s->array.index);
          break;
        case BZLA_LST_SORT:
          BZLA_PUSH_STACK(sort_stack, s->lst.head);
          BZLA_PUSH_STACK(sort_stack, s->lst.tail);
          break;
        case BZLA_FUN_SORT:
          BZLA_PUSH_STACK(sort_stack, s->fun.domain);
          BZLA_PUSH_STACK(sort_stack, s->fun.codomain);
          break;
        case BZLA_TUPLE_SORT:
          for (i = 0; i < s->tuple.num_elements; i++)
            BZLA_PUSH_STACK(sort_stack, s->tuple.elements[i]);
          break;
        default: assert(s->kind == BZLA_BOOL_SORT || s->kind == BZLA_BV_SORT);
      }
    }
    else if (!d->as_int)
    {
      switch (s->kind)
      {
        case BZLA_ARRAY_SORT:
          s0 = bzla_hashint_map_get(map, s->array.index->id)->as_int;
          s1 = bzla_hashint_map_get(map, s->array.element->id)->as_int;
          r  = bzla_sort_array(clone, s0, s1);
          break;
#if 0
	      case BZLA_LST_SORT:
		s0 = bzla_hashint_map_get (map, s->lst.head->id)->as_int;
		s1 = bzla_hashint_map_get (map, s->lst.tail->id)->as_int;
		r = bzla_lst_sort (clone, s0, s1);
		break;
#endif
        case BZLA_FUN_SORT:
          s0 = bzla_hashint_map_get(map, s->fun.domain->id)->as_int;
          s1 = bzla_hashint_map_get(map, s->fun.codomain->id)->as_int;
          if (s->fun.is_array)
          {
            r = bzla_sort_array(
                clone, bzla_sort_array_get_index(clone, s0), s1);
          }
          else
          {
            r = bzla_sort_fun(clone, s0, s1);
          }
          break;
        case BZLA_TUPLE_SORT:
          for (i = 0; i < s->tuple.num_elements; i++)
          {
            s0 = bzla_hashint_map_get(map, s->tuple.elements[i]->id)->as_int;
            BZLA_PUSH_STACK(sort_ids, s0);
          }
          r = bzla_sort_tuple(clone, sort_ids.start, s->tuple.num_elements);
          BZLA_RESET_STACK(sort_ids);
          break;
        case BZLA_BOOL_SORT: r = bzla_sort_bool(clone); break;
        default:
          assert(s->kind == BZLA_BV_SORT);
          r = bzla_sort_bv(clone, s->bitvec.width);
      }
      assert(r);
      d->as_int = r;
    }
  }
  d = bzla_hashint_map_get(map, sort);
  assert(d);
  assert(d->as_int);
  r = bzla_sort_copy(clone, d->as_int);

  for (i = 0; i < map->size; i++)
  {
    if (!map->keys[i]) continue;
    s0 = map->data[i].as_int;
    bzla_sort_release(clone, s0);
  }
  bzla_hashint_map_delete(map);
  BZLA_RELEASE_STACK(sort_ids);
  BZLA_RELEASE_STACK(sort_stack);
  return r;
}

BzlaNode *
bzla_clone_recursively_rebuild_exp(Bzla *bzla,
                                   Bzla *clone,
                                   BzlaNode *exp,
                                   BzlaNodeMap *exp_map,
                                   uint32_t rewrite_level)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_real_addr(exp)->bzla == bzla);
  assert(exp_map);

  uint32_t i, rwl;
  char *symbol;
  BzlaNode *real_exp, *cur, *cur_clone, *e[BZLA_NODE_MAX_CHILDREN];
  BzlaNodePtrStack work_stack;
  BzlaIntHashTable *mark;
  BzlaMemMgr *mm;
  BzlaPtrHashBucket *b;
  BzlaSortId sort;

  mm   = bzla->mm;
  mark = bzla_hashint_table_new(mm);

  /* in some cases we may want to rebuild the expressions with a certain
   * rewrite level */
  rwl = bzla_opt_get(clone, BZLA_OPT_RW_LEVEL);
  if (rwl > 0) bzla_opt_set(clone, BZLA_OPT_RW_LEVEL, rewrite_level);

  BZLA_INIT_STACK(mm, work_stack);

  real_exp = bzla_node_real_addr(exp);
  BZLA_PUSH_STACK(work_stack, real_exp);
  while (!BZLA_EMPTY_STACK(work_stack))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(work_stack));

    if (bzla_nodemap_mapped(exp_map, cur)) continue;

    if (!bzla_hashint_table_contains(mark, cur->id))
    {
      bzla_hashint_table_add(mark, cur->id);
      BZLA_PUSH_STACK(work_stack, cur);
      for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(work_stack, cur->e[i]);
    }
    else
    {
      assert(!bzla_nodemap_mapped(exp_map, cur));
      assert(!bzla_node_is_proxy(cur));
      for (i = 0; i < cur->arity; i++)
      {
        e[i] = bzla_nodemap_mapped(exp_map, cur->e[i]);
        assert(e[i]);
      }
      switch (cur->kind)
      {
        case BZLA_BV_CONST_NODE:
          cur_clone =
              bzla_exp_bv_const(clone, bzla_node_bv_const_get_bits(cur));
          break;
        case BZLA_VAR_NODE:
          b      = bzla_hashptr_table_get(bzla->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          sort      = bzla_sort_bv(clone, bzla_node_bv_get_width(bzla, cur));
          cur_clone = bzla_exp_var(clone, sort, symbol);
          bzla_sort_release(clone, sort);
          break;
        case BZLA_PARAM_NODE:
          b      = bzla_hashptr_table_get(bzla->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          sort      = bzla_sort_bv(clone, bzla_node_bv_get_width(bzla, cur));
          cur_clone = bzla_exp_param(clone, sort, symbol);
          bzla_sort_release(clone, sort);
          break;
        case BZLA_UF_NODE:
          b      = bzla_hashptr_table_get(bzla->node2symbol, cur);
          symbol = b ? b->data.as_str : 0;
          sort = bzla_clone_recursively_rebuild_sort(bzla, clone, cur->sort_id);
          cur_clone = bzla_exp_uf(clone, sort, symbol);
          bzla_sort_release(clone, sort);
          break;
        case BZLA_BV_SLICE_NODE:
          cur_clone = bzla_exp_bv_slice(clone,
                                        e[0],
                                        bzla_node_bv_slice_get_upper(cur),
                                        bzla_node_bv_slice_get_lower(cur));
          break;
        case BZLA_BV_AND_NODE:
          cur_clone = bzla_exp_bv_and(clone, e[0], e[1]);
          break;
        case BZLA_BV_EQ_NODE:
        case BZLA_FUN_EQ_NODE:
          cur_clone = bzla_exp_eq(clone, e[0], e[1]);
          break;
        case BZLA_BV_ADD_NODE:
          cur_clone = bzla_exp_bv_add(clone, e[0], e[1]);
          break;
        case BZLA_BV_MUL_NODE:
          cur_clone = bzla_exp_bv_mul(clone, e[0], e[1]);
          break;
        case BZLA_BV_ULT_NODE:
          cur_clone = bzla_exp_bv_ult(clone, e[0], e[1]);
          break;
        case BZLA_BV_SLT_NODE:
          cur_clone = bzla_exp_bv_slt(clone, e[0], e[1]);
          break;
        case BZLA_BV_SLL_NODE:
          cur_clone = bzla_exp_bv_sll(clone, e[0], e[1]);
          break;
        case BZLA_BV_SRL_NODE:
          cur_clone = bzla_exp_bv_srl(clone, e[0], e[1]);
          break;
        case BZLA_BV_UDIV_NODE:
          cur_clone = bzla_exp_bv_udiv(clone, e[0], e[1]);
          break;
        case BZLA_BV_UREM_NODE:
          cur_clone = bzla_exp_bv_urem(clone, e[0], e[1]);
          break;
        case BZLA_BV_CONCAT_NODE:
          cur_clone = bzla_exp_bv_concat(clone, e[0], e[1]);
          break;
        case BZLA_LAMBDA_NODE:
          assert(!bzla_node_param_get_assigned_exp(e[0]));
          bzla_node_param_set_binder(e[0], 0);
          cur_clone = bzla_exp_lambda(clone, e[0], e[1]);
          break;
        case BZLA_APPLY_NODE:
          // FIXME use bzla_exp_apply as soon as applies are
          // generated with rewriting (currently without)
          // cur_clone = bzla_exp_apply (clone, e[0], e[1]);
          cur_clone = bzla_node_create_apply(clone, e[0], e[1]);
          break;
        case BZLA_ARGS_NODE:
          cur_clone = bzla_exp_args(clone, e, cur->arity);
          break;
        case BZLA_EXISTS_NODE:
          cur_clone = bzla_exp_exists(clone, e[0], e[1]);
          break;
        case BZLA_FORALL_NODE:
          cur_clone = bzla_exp_forall(clone, e[0], e[1]);
          break;
        default:
          assert(bzla_node_is_bv_cond(cur));
          cur_clone = bzla_exp_cond(clone, e[0], e[1], e[2]);
      }
      bzla_nodemap_map(exp_map, cur, cur_clone);
      bzla_node_release(clone, cur_clone);
    }
  }

  BZLA_RELEASE_STACK(work_stack);
  bzla_hashint_table_delete(mark);

  /* reset rewrite_level to original value */
  bzla_opt_set(clone, BZLA_OPT_RW_LEVEL, rwl);
  return bzla_node_copy(clone, bzla_nodemap_mapped(exp_map, exp));
}
