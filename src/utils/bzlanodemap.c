/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlanodemap.h"

#include "bzlacore.h"
#include "utils/bzlahashint.h"

/*------------------------------------------------------------------------*/

BzlaNodeMap *
bzla_nodemap_new(Bzla *bzla)
{
  BzlaNodeMap *res;

  assert(bzla);

  BZLA_NEW(bzla->mm, res);
  res->bzla  = bzla;
  res->table = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  return res;
}

void
bzla_nodemap_delete(BzlaNodeMap *map)
{
  assert(map);

  BzlaPtrHashTableIterator it;
  BzlaNode *src;
  BzlaNode *dst;

  bzla_iter_hashptr_init(&it, map->table);
  while (bzla_iter_hashptr_has_next(&it))
  {
    dst = (BzlaNode *) it.bucket->data.as_ptr;
    bzla_node_release(bzla_node_real_addr(dst)->bzla, dst);
    src = bzla_iter_hashptr_next(&it);
    bzla_node_release(bzla_node_real_addr(src)->bzla, src);
  }
  bzla_hashptr_table_delete(map->table);
  BZLA_DELETE(map->bzla->mm, map);
}

BzlaNode *
bzla_nodemap_mapped(BzlaNodeMap *map, const BzlaNode *node)
{
  BzlaPtrHashBucket *bucket;
  BzlaNode *real_node;
  BzlaNode *res;

  real_node = bzla_node_real_addr(node);
  bucket    = bzla_hashptr_table_get(map->table, real_node);
  if (!bucket) return 0;
  assert(bucket->key == real_node);
  res = bucket->data.as_ptr;
  if (bzla_node_is_inverted(node)) res = bzla_node_invert(res);
  return res;
}

void
bzla_nodemap_map(BzlaNodeMap *map, BzlaNode *src, BzlaNode *dst)
{
  BzlaPtrHashBucket *bucket;

  assert(map);
  assert(src);
  assert(dst);

  if (bzla_node_is_inverted(src))
  {
    src = bzla_node_invert(src);
    dst = bzla_node_invert(dst);
  }
  assert(!bzla_hashptr_table_get(map->table, src));
  bucket = bzla_hashptr_table_add(map->table, src);
  assert(bucket);
  assert(bucket->key == src);
  bucket->key = bzla_node_copy(bzla_node_real_addr(src)->bzla, src);
  assert(!bucket->data.as_ptr);
  bucket->data.as_ptr = bzla_node_copy(bzla_node_real_addr(dst)->bzla, dst);
}

/*------------------------------------------------------------------------*/
/* iterators    						          */
/*------------------------------------------------------------------------*/

void
bzla_iter_nodemap_init(BzlaNodeMapIterator *it, const BzlaNodeMap *map)
{
  assert(map);
  bzla_iter_hashptr_init(&it->it, map->table);
}

void
bzla_iter_nodemap_init_reversed(BzlaNodeMapIterator *it, const BzlaNodeMap *map)
{
  assert(map);
  bzla_iter_hashptr_init_reversed(&it->it, map->table);
}

bool
bzla_iter_nodemap_has_next(const BzlaNodeMapIterator *it)
{
  return bzla_iter_hashptr_has_next(&it->it);
}

void
bzla_iter_nodemap_queue(BzlaNodeMapIterator *it, const BzlaNodeMap *map)
{
  assert(map);
  bzla_iter_hashptr_queue(&it->it, map->table);
}

BzlaNode *
bzla_iter_nodemap_next(BzlaNodeMapIterator *it)
{
  return bzla_iter_hashptr_next(&it->it);
}

BzlaHashTableData *
bzla_iter_nodemap_next_data(BzlaNodeMapIterator *it)
{
  return bzla_iter_hashptr_next_data(&it->it);
}

/*------------------------------------------------------------------------*/
