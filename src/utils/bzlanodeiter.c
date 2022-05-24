/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlanodeiter.h"

/*------------------------------------------------------------------------*/
/* node iterators					                  */
/*------------------------------------------------------------------------*/

void
bzla_iter_apply_parent_init(BzlaNodeIterator *it, const BzlaNode *exp)
{
  assert(it);
  assert(exp);
  it->cur = bzla_node_real_addr(bzla_node_real_addr(exp)->last_parent);
}

bool
bzla_iter_apply_parent_has_next(const BzlaNodeIterator *it)
{
  assert(it);
  assert(bzla_node_is_regular(it->cur));
  /* function child of apply is at position 0, so cur is not tagged */
  return it->cur && bzla_node_is_apply(it->cur);
}

BzlaNode *
bzla_iter_apply_parent_next(BzlaNodeIterator *it)
{
  BzlaNode *result;
  assert(it);
  result = it->cur;
  assert(result);
  it->cur = bzla_node_real_addr(BZLA_PREV_PARENT(result));
  assert(bzla_node_is_regular(result));
  assert(bzla_node_is_apply(result));
  return result;
}

/*------------------------------------------------------------------------*/

void
bzla_iter_parent_init(BzlaNodeIterator *it, const BzlaNode *exp)
{
  assert(it);
  assert(exp);
  it->cur = bzla_node_real_addr(exp)->first_parent;
}

bool
bzla_iter_parent_has_next(const BzlaNodeIterator *it)
{
  assert(it);
  return it->cur != 0;
}

BzlaNode *
bzla_iter_parent_next(BzlaNodeIterator *it)
{
  assert(it);

  BzlaNode *result;
  result = it->cur;
  assert(result);
  it->cur = BZLA_NEXT_PARENT(result);

  return bzla_node_real_addr(result);
}

/*------------------------------------------------------------------------*/

void
bzla_iter_args_init(BzlaArgsIterator *it, const BzlaNode *exp)
{
  assert(it);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_args(exp));

  it->pos = 0;
  it->exp = exp;
  it->cur = exp->e[0];
}

bool
bzla_iter_args_has_next(const BzlaArgsIterator *it)
{
  assert(it);
  return it->cur != 0;
}

BzlaNode *
bzla_iter_args_next(BzlaArgsIterator *it)
{
  assert(it);
  assert(it->cur);

  BzlaNode *result;

  result = it->cur;

  /* end of this args node, continue with next */
  if (bzla_node_is_args(result))
  {
    assert(it->pos == 2);
    assert(bzla_node_is_regular(result));
    it->pos = 0;
    it->exp = result;
    it->cur = result->e[0];
    result  = it->cur;
  }

  /* prepare next argument */
  it->pos++;
  if (it->pos < it->exp->arity)
    it->cur = it->exp->e[it->pos];
  else
    it->cur = 0;

  assert(!bzla_node_is_args(result));
  return result;
}

/*------------------------------------------------------------------------*/

void
bzla_iter_binder_init(BzlaNodeIterator *it, BzlaNode *exp)
{
  assert(it);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_binder(exp));

  it->cur = exp;
}

BzlaNode *
bzla_iter_binder_next(BzlaNodeIterator *it)
{
  assert(it);
  assert(it->cur);

  BzlaNode *result;
  result  = it->cur;
  it->cur = result->e[1];
  return result;
}

bool
bzla_iter_binder_has_next(const BzlaNodeIterator *it)
{
  assert(it);
  assert(it->cur);
  return !bzla_node_is_inverted(it->cur) && bzla_node_is_binder(it->cur);
}

bool
bzla_iter_binder_has_next_inverted(const BzlaNodeIterator *it)
{
  assert(it);
  assert(it->cur);
  return !bzla_node_is_inverted(it->cur) && bzla_node_is_binder(it->cur);
}

void
bzla_iter_lambda_init(BzlaNodeIterator *it, BzlaNode *exp)
{
  bzla_iter_binder_init(it, exp);
  assert(bzla_node_is_lambda(exp));
}

BzlaNode *
bzla_iter_lambda_next(BzlaNodeIterator *it)
{
  return bzla_iter_binder_next(it);
}

bool
bzla_iter_lambda_has_next(const BzlaNodeIterator *it)
{
  assert(it);
  assert(it->cur);
  return bzla_node_is_lambda(it->cur);
}

/*------------------------------------------------------------------------*/

#if 0
void
bzla_iter_param_init (BzlaNodeIterator * it, BzlaNode * exp)
{
  bzla_iter_binder_init (it, exp);
}

BzlaNode *
bzla_iter_param_next (BzlaNodeIterator * it)
{
  BzlaNode *result;
  result = bzla_iter_binder_next (it);
  assert (bzla_node_is_param (result->e[0]));
  return result->e[0];
}

bool
bzla_has_next_param_iterator (BzlaNodeIterator * it)
{
  return bzla_has_next_binder_iterator (it);
}
#endif

/*------------------------------------------------------------------------*/

#if 0
static void
find_next_unique_node (BzlaNodeIterator * it)
{
  while (!it->cur && it->pos < it->bzla->nodes_unique_table.size)
    it->cur = it->bzla->nodes_unique_table.chains[it->pos++];
  assert (it->cur
	  || it->num_elements == it->bzla->nodes_unique_table.num_elements);
}

void
bzla_iter_unique_table_init (BzlaNodeIterator * it, const Bzla * bzla)
{
  assert (bzla);
  assert (it);

  it->bzla = bzla;
  it->pos = 0;
#ifndef NDEBUG
  it->num_elements = 0;
#endif
  it->cur = 0;
  find_next_unique_node (it);
}

bool
bzla_iter_unique_table_has_next (const BzlaNodeIterator * it)
{
  assert (it);
  assert (it->cur || it->pos >= it->bzla->nodes_unique_table.size);
  return it->cur != 0;
}

BzlaNode *
bzla_iter_unique_table_next (BzlaNodeIterator * it)
{
  assert (it);
  assert (it->cur);

  BzlaNode *result;

  result = it->cur;
#ifndef NDEBUG
  it->num_elements++;
  assert (it->num_elements <= it->bzla->nodes_unique_table.num_elements);
  assert (result);
#endif
  it->cur = it->cur->next;
  if (!it->cur)
    find_next_unique_node (it);
  return result;
}
#endif
