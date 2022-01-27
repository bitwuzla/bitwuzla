/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlaunionfind.h"

#include "bzlanode.h"
#include "utils/bzlahashint.h"

struct BzlaUnionFind
{
  BzlaMemMgr *mm;
  BzlaIntHashTable *cache; /* Maps node ids to UnionFindNode */
};

struct UnionFindNode
{
  int32_t id;
  struct UnionFindNode *parent;
  BzlaNode *node;
};

typedef struct UnionFindNode UnionFindNode;

static UnionFindNode *
get_node(BzlaUnionFind *ufind, BzlaNode *n)
{
  assert(ufind);
  assert(n);

  int32_t id = bzla_node_get_id(n);
  assert(bzla_hashint_map_contains(ufind->cache, id));
  return bzla_hashint_map_get(ufind->cache, id)->as_ptr;
}

static UnionFindNode *
new_node(BzlaUnionFind *ufind, BzlaNode *n)
{
  assert(ufind);
  assert(n);

  int32_t id;
  UnionFindNode *ufind_node;

  id = bzla_node_get_id(n);

  if (bzla_hashint_map_contains(ufind->cache, id))
  {
    ufind_node = bzla_hashint_map_get(ufind->cache, id)->as_ptr;
  }
  else
  {
    BZLA_CNEW(ufind->mm, ufind_node);
    bzla_hashint_map_add(ufind->cache, id)->as_ptr = ufind_node;
    ufind_node->node                               = n;
    ufind_node->id                                 = id;
  }
  return ufind_node;
}

static UnionFindNode *
find_node(UnionFindNode *node)
{
  assert(node);

  UnionFindNode *parent, *repr;

  /* Find representative. */
  repr = node;
  while (repr->parent)
  {
    repr = repr->parent;
  }

  /* Shorten path for all nodes. */
  while (node->parent)
  {
    parent       = node->parent;
    node->parent = repr;
    node         = parent;
  }

  return repr;
}

BzlaUnionFind *
bzla_ufind_new(BzlaMemMgr *mm)
{
  assert(mm);

  BzlaUnionFind *ufind;

  BZLA_CNEW(mm, ufind);
  ufind->mm    = mm;
  ufind->cache = bzla_hashint_map_new(mm);

  return ufind;
}

void
bzla_ufind_delete(BzlaUnionFind *ufind)
{
  assert(ufind);

  for (size_t i = 0; i < ufind->cache->size; i++)
  {
    if (!ufind->cache->data[i].as_ptr) continue;
    BZLA_DELETE(ufind->mm, (UnionFindNode *) ufind->cache->data[i].as_ptr);
  }
  bzla_hashint_map_delete(ufind->cache);
  BZLA_DELETE(ufind->mm, ufind);
}

void
bzla_ufind_add(BzlaUnionFind *ufind, BzlaNode *x)
{
  assert(ufind);
  assert(x);

  (void) new_node(ufind, x);
}

void
bzla_ufind_merge(BzlaUnionFind *ufind, BzlaNode *x, BzlaNode *y)
{
  assert(ufind);
  assert(x);
  assert(y);

  UnionFindNode *n1, *n2;

  n1 = find_node(new_node(ufind, x));
  n2 = find_node(new_node(ufind, y));

  assert(!n1->parent);
  assert(!n2->parent);

  if (n1->id != n2->id)
  {
    /* Choose node with lower id to be representative. */
    if (abs(n1->id) < abs(n2->id))
    {
      n2->parent = n1;
    }
    else
    {
      n1->parent = n2;
    }
  }
}

BzlaNode *
bzla_ufind_get_repr(BzlaUnionFind *ufind, BzlaNode *x)
{
  assert(ufind);
  assert(x);

  int32_t id = bzla_node_get_id(x);
  if (bzla_hashint_map_contains(ufind->cache, id))
  {
    UnionFindNode *n = find_node(get_node(ufind, x));
    return n->node;
  }
  return x;
}

bool
bzla_ufind_is_equal(BzlaUnionFind *ufind, BzlaNode *x, BzlaNode *y)
{
  assert(ufind);
  assert(x);
  assert(y);

  return bzla_ufind_get_repr(ufind, x) == bzla_ufind_get_repr(ufind, y);
}
