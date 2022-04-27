/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlarwcache.h"

#include "bzlacore.h"

static uint32_t hash_primes[] = {
    333444569u, 76891121u, 456790003u, 2654435761u};

static int32_t
compare_rw_cache_tuple(const BzlaRwCacheTuple *t0, const BzlaRwCacheTuple *t1)
{
  assert(t0);
  assert(t1);

  if (t0->kind == t1->kind && t0->n[0] == t1->n[0] && t0->n[1] == t1->n[1]
      && t0->n[2] == t1->n[2] && t0->n[3] == t1->n[3])
  {
    return 0;
  }
  return 1;
}

static uint32_t
hash_rw_cache_tuple(const BzlaRwCacheTuple *t)
{
  uint32_t hash;
  hash = hash_primes[0] * (uint32_t) t->kind;
  hash += hash_primes[1] * (uint32_t) t->n[0];
  hash += hash_primes[2] * (uint32_t) t->n[1];
  hash += hash_primes[3] * (uint32_t) t->n[2];
  hash += hash_primes[0] * (uint32_t) t->n[3];
  return hash;
}

static bool
is_valid_node(Bzla *bzla, int32_t id)
{
  BzlaNode *n = bzla_node_get_by_id(bzla, id);
  if (!n || bzla_node_is_proxy(n))
  {
    return false;
  }
  return true;
}

int32_t
bzla_rw_cache_get(BzlaRwCache *rwc,
                  BzlaNodeKind kind,
                  int32_t nid0,
                  int32_t nid1,
                  int32_t nid2,
                  int32_t nid3)
{
#ifndef NDEBUG
  assert(!nid0 || is_valid_node(rwc->bzla, nid0));
  if (kind != BZLA_BV_SLICE_NODE)
  {
    /* For slice nodes nid1 and nid2 correspond to the upper/lower indices. */
    assert(!nid1 || is_valid_node(rwc->bzla, nid1));
    /* For to_fp nodes, nid2 correspond to the sort of the conversion. */
    if (!bzla_node_is_fp_to_fp_kind(kind))
    {
      assert(!nid2 || is_valid_node(rwc->bzla, nid2));
    }
  }
  assert(!nid3 || is_valid_node(rwc->bzla, nid3));
#endif

  BzlaRwCacheTuple t   = {.kind = kind, .n = {nid0, nid1, nid2, nid3}};
  BzlaPtrHashBucket *b = bzla_hashptr_table_get(rwc->cache, &t);
  if (b)
  {
    BzlaRwCacheTuple *cached = b->key;
    return cached->result;
  }
  return 0;
}

void
bzla_rw_cache_add(BzlaRwCache *rwc,
                  BzlaNodeKind kind,
                  int32_t nid0,
                  int32_t nid1,
                  int32_t nid2,
                  int32_t nid3,
                  int32_t result)
{
  assert(result);

#ifndef NDEBUG
  assert(is_valid_node(rwc->bzla, result));
  assert(!nid0 || is_valid_node(rwc->bzla, nid0));
  if (kind != BZLA_BV_SLICE_NODE)
  {
    /* For slice nodes nid1 and nid2 correspond to the upper/lower indices. */
    assert(!nid1 || is_valid_node(rwc->bzla, nid1));
    /* For to_fp nodes, nid2 correspond to the sort of the conversion. */
    if (!bzla_node_is_fp_to_fp_kind(kind))
    {
      assert(!nid2 || is_valid_node(rwc->bzla, nid2));
    }
    assert(!nid3 || is_valid_node(rwc->bzla, nid3));
  }
#endif

  /* The bruttomesso benchmark family produces extremely many distinct slice
   * nodes that let's the cache grow to several GB in some cases. For now, we
   * will disable caching of slice nodes until we find a better solution.
   * Note: Calling bzla_rw_cache_gc(...) does not help here. */
  if (kind == BZLA_BV_SLICE_NODE)
  {
    return;
  }

  int32_t cached_result_id;
  if ((cached_result_id = bzla_rw_cache_get(rwc, kind, nid0, nid1, nid2, nid3)))
  {
    /* This can only happen if the node corresponding to cached_result_id does
     * not exist anymore (= deallocated). */
    if (cached_result_id != result)
    {
      assert(bzla_node_get_by_id(rwc->bzla, cached_result_id) == 0);
      BzlaRwCacheTuple t   = {.kind = kind, .n = {nid0, nid1, nid2, nid3}};
      BzlaPtrHashBucket *b = bzla_hashptr_table_get(rwc->cache, &t);
      assert(b);
      BzlaRwCacheTuple *cached = b->key;
      cached->result           = result;  // Update the result
      rwc->num_update++;
    }
    return;
  }

  BzlaRwCacheTuple *t;
  BZLA_CNEW(rwc->bzla->mm, t);
  t->kind   = kind;
  t->n[0]   = nid0;
  t->n[1]   = nid1;
  t->n[2]   = nid2;
  t->n[3]   = nid3;
  t->result = result;
  rwc->num_add++;

  bzla_hashptr_table_add(rwc->cache, t);

  if (rwc->num_add % 100000 == 0)
  {
    bzla_rw_cache_gc(rwc);
  }
}

void
bzla_rw_cache_init(BzlaRwCache *rwc, Bzla *bzla)
{
  assert(rwc);
  rwc->bzla       = bzla;
  rwc->cache      = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) hash_rw_cache_tuple,
                                      (BzlaCmpPtr) compare_rw_cache_tuple);
  rwc->num_add    = 0;
  rwc->num_get    = 0;
  rwc->num_update = 0;
  rwc->num_remove = 0;
}

void
bzla_rw_cache_delete(BzlaRwCache *rwc)
{
  assert(rwc);

  BzlaPtrHashTableIterator it;
  BzlaRwCacheTuple *t;

  bzla_iter_hashptr_init(&it, rwc->cache);
  while (bzla_iter_hashptr_has_next(&it))
  {
    t = bzla_iter_hashptr_next(&it);
    BZLA_DELETE(rwc->bzla->mm, t);
  }
  bzla_hashptr_table_delete(rwc->cache);
}

void
bzla_rw_cache_reset(BzlaRwCache *rwc)
{
  assert(rwc);
  assert(rwc->bzla->mm);
  assert(rwc->cache);

  Bzla *bzla = rwc->bzla;
  bzla_rw_cache_delete(rwc);
  bzla_rw_cache_init(rwc, bzla);
}

void
bzla_rw_cache_gc(BzlaRwCache *rwc)
{
  assert(rwc->bzla->mm);
  assert(rwc->cache);

  bool remove;
  BzlaPtrHashTableIterator it;
  BzlaRwCacheTuple *t;
  BzlaNodeKind kind;

  Bzla *bzla            = rwc->bzla;
  BzlaPtrHashTable *old = rwc->cache;

  rwc->cache = bzla_hashptr_table_new(bzla->mm, old->hash, old->cmp);

  /* We remove all cache entries that store invalid children node ids. An
   * invalid node is either a node that does not exist anymore (deallocated) or
   * if the node id belongs to a proxy node. Proxy nodes are never used to
   * query the cache and are therefore useless cache entries. */
  bzla_iter_hashptr_init(&it, old);
  while (bzla_iter_hashptr_has_next(&it))
  {
    t    = bzla_iter_hashptr_next(&it);
    kind = t->kind;

    remove = !is_valid_node(bzla, t->n[0]);

    if (!remove && kind != BZLA_BV_SLICE_NODE)
    {
      if (t->n[1])
      {
        remove = remove || !is_valid_node(bzla, t->n[1]);
      }
      if (!remove && t->n[2])
      {
        remove = remove || !is_valid_node(bzla, t->n[2]);
      }

      remove = remove || !bzla_node_get_by_id(bzla, t->result);
    }

    if (remove)
    {
      BZLA_DELETE(bzla->mm, t);
      rwc->num_remove++;
    }
    else
    {
      bzla_hashptr_table_add(rwc->cache, t);
    }
  }
  bzla_hashptr_table_delete(old);
}
