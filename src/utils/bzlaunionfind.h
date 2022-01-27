/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAUNIONFIND_H_INCLUDED
#define BZLAUNIONFIND_H_INCLUDED

#include <stdbool.h>

#include "bzlatypes.h"
#include "utils/bzlamem.h"

typedef struct BzlaUnionFind BzlaUnionFind;

/* Create new union-find data structure */
BzlaUnionFind *bzla_ufind_new(BzlaMemMgr *mm);

/* Delete union-find data structure. */
void bzla_ufind_delete(BzlaUnionFind *ufind);

/* Add a new set containing 'x'. */
void bzla_ufind_add(BzlaUnionFind *ufind, BzlaNode *x);

/* Merge sets of 'x' and 'y'. */
void bzla_ufind_merge(BzlaUnionFind *ufind, BzlaNode *x, BzlaNode *y);

/* Get representative of 'x'. */
BzlaNode *bzla_ufind_get_repr(BzlaUnionFind *ufind, BzlaNode *x);

/* Check whether 'x' and 'y' belong to the same set. */
bool bzla_ufind_is_equal(BzlaUnionFind *ufind, BzlaNode *x, BzlaNode *y);

#endif
