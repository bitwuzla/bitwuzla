/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAEXPITER_H_INCLUDED
#define BZLAEXPITER_H_INCLUDED

#include <stdbool.h>

#include "bzlacore.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaNodeIterator
{
  const Bzla *bzla; /* required for unique table iterator */
  uint32_t pos;     /* required for unique table iterator */
#ifndef NDEBUG
  uint32_t num_elements;
#endif
  BzlaNode *cur;
} BzlaNodeIterator;

#define BZLA_NEXT_PARENT(exp) \
  (bzla_node_real_addr(exp)->next_parent[bzla_node_get_tag(exp)])

#define BZLA_PREV_PARENT(exp) \
  (bzla_node_real_addr(exp)->prev_parent[bzla_node_get_tag(exp)])

void bzla_iter_apply_parent_init(BzlaNodeIterator *it, const BzlaNode *exp);
bool bzla_iter_apply_parent_has_next(const BzlaNodeIterator *it);
BzlaNode *bzla_iter_apply_parent_next(BzlaNodeIterator *it);

void bzla_iter_parent_init(BzlaNodeIterator *it, const BzlaNode *exp);
bool bzla_iter_parent_has_next(const BzlaNodeIterator *it);
BzlaNode *bzla_iter_parent_next(BzlaNodeIterator *it);

void bzla_iter_lambda_init(BzlaNodeIterator *it, BzlaNode *exp);
bool bzla_iter_lambda_has_next(const BzlaNodeIterator *it);
BzlaNode *bzla_iter_lambda_next(BzlaNodeIterator *it);

void bzla_iter_binder_init(BzlaNodeIterator *it, BzlaNode *exp);
bool bzla_iter_binder_has_next(const BzlaNodeIterator *it);
bool bzla_iter_binder_has_next_inverted(const BzlaNodeIterator *it);
BzlaNode *bzla_iter_binder_next(BzlaNodeIterator *it);

#if 0
void bzla_iter_param_init (BzlaNodeIterator * it, BzlaNode * exp);
bool bzla_iter_param_has_next (const BzlaNodeIterator * it);
BzlaNode * bzla_iter_param_next (BzlaNodeIterator * it);

void bzla_iter_unique_table_init (BzlaNodeIterator * it, const Bzla * exp);
bool bzla_iter_unique_table_has_next (const BzlaNodeIterator * it);
BzlaNode * bzla_iter_unique_table_next (BzlaNodeIterator * it);
#endif

/*------------------------------------------------------------------------*/

typedef struct BzlaArgsIterator
{
  uint32_t pos;
  BzlaNode *cur;
  const BzlaNode *exp;
} BzlaArgsIterator;

void bzla_iter_args_init(BzlaArgsIterator *it, const BzlaNode *exp);
bool bzla_iter_args_has_next(const BzlaArgsIterator *it);
BzlaNode *bzla_iter_args_next(BzlaArgsIterator *it);

/*------------------------------------------------------------------------*/

#endif
