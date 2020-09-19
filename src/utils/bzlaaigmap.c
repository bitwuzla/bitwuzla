/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2014 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "utils/bzlaaigmap.h"

#include "bzlacore.h"
#include "utils/bzlahashptr.h"

/*------------------------------------------------------------------------*/

BzlaAIGMap *
bzla_aigmap_new(Bzla *bzla, BzlaAIGMgr *amgr_src, BzlaAIGMgr *amgr_dst)
{
  assert(bzla);
  assert(amgr_src);
  assert(amgr_dst);

  BzlaAIGMap *res;

  BZLA_NEW(bzla->mm, res);
  res->bzla     = bzla;
  res->amgr_src = amgr_src;
  res->amgr_dst = amgr_dst;
  res->table    = bzla_hashptr_table_new(bzla->mm, 0, 0);
  return res;
}

BzlaAIG *
bzla_aigmap_mapped(BzlaAIGMap *map, BzlaAIG *aig)
{
  assert(map);
  assert(aig);

  BzlaPtrHashBucket *bucket;
  BzlaAIG *real_aig, *res;

  real_aig = BZLA_REAL_ADDR_AIG(aig);
  bucket   = bzla_hashptr_table_get(map->table, real_aig);
  if (!bucket) return 0;
  assert(bucket->key == real_aig);
  res = bucket->data.as_ptr;
  if (BZLA_IS_INVERTED_AIG(aig)) res = BZLA_INVERT_AIG(res);
  return res;
}

void
bzla_aigmap_map(BzlaAIGMap *map, BzlaAIG *src, BzlaAIG *dst)
{
  assert(map);
  assert(src);
  assert(dst);

  BzlaPtrHashBucket *bucket;

  if (BZLA_IS_INVERTED_AIG(src))
  {
    assert(BZLA_IS_INVERTED_AIG(dst));
    src = BZLA_INVERT_AIG(src);
    dst = BZLA_INVERT_AIG(dst);
  }
  assert(!bzla_hashptr_table_get(map->table, src));
  bucket = bzla_hashptr_table_add(map->table, src);
  assert(bucket);
  assert(bucket->key == src);
  bucket->key = bzla_aig_copy(map->amgr_src, src);
  assert(!bucket->data.as_ptr);
  bucket->data.as_ptr = bzla_aig_copy(map->amgr_dst, dst);
}

void
bzla_aigmap_delete(BzlaAIGMap *map)
{
  assert(map);

  Bzla *bzla;
  BzlaPtrHashTableIterator it;

  bzla = map->bzla;

  bzla_iter_hashptr_init(&it, map->table);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_aig_release(map->amgr_dst, it.bucket->data.as_ptr);
    bzla_aig_release(map->amgr_src, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(map->table);
  BZLA_DELETE(bzla->mm, map);
}
