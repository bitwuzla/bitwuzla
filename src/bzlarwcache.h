/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLARWCACHE_H_INCLUDED
#define BZLARWCACHE_H_INCLUDED

#include "bzlanode.h"
#include "utils/bzlahashptr.h"

/* Cache entry that stores the result of rewriting a node with kind 'kind' and
 * it's children 'n'.
 *
 * Note:
 * - BZLA_SLICE_NODE: n[1] and n[2] are the upper and lower indices.
 * - BZLA_FP_TO_FP_*_NODE: n[2] is the sort of the conversion.
 */
struct BzlaRwCacheTuple
{
  BzlaNodeKind kind;
  int32_t n[4];
  int32_t result;
};

typedef struct BzlaRwCacheTuple BzlaRwCacheTuple;

/* Stores all cache entries and some statistics. Note that the statistics are
 * not reset if bzla_rw_cache_reset() or bzla_rw_cache_gc() is called. */
struct BzlaRwCache
{
  Bzla *bzla;
  BzlaPtrHashTable *cache; /* Hash table of BzlaRwCacheTuple. */
  uint64_t num_add;        /* Number of cached rewrite rules. */
  uint64_t num_get;        /* Number of cache checks. */
  uint64_t num_update;     /* Number of updated cache entries. */
  uint64_t num_remove;     /* Number of removed cache entries (GC). */
};

typedef struct BzlaRwCache BzlaRwCache;

/* Add a new entry to the rewrite cache. */
void bzla_rw_cache_add(BzlaRwCache *cache,
                       BzlaNodeKind kind,
                       int32_t nid0,
                       int32_t nid1,
                       int32_t nid2,
                       int32_t nid3,
                       int32_t result_nid);

/* Check if we already cached a rewritten node. */
int32_t bzla_rw_cache_get(BzlaRwCache *cache,
                          BzlaNodeKind kind,
                          int32_t nid0,
                          int32_t nid1,
                          int32_t nid2,
                          int32_t nid3);

/* Initialize the rewrite cache. */
void bzla_rw_cache_init(BzlaRwCache *cache, Bzla *mm);

/* Delete the rewrite cache. */
void bzla_rw_cache_delete(BzlaRwCache *cache);

/* Reset the rewrite cache. */
void bzla_rw_cache_reset(BzlaRwCache *cache);

/* Remove all cache entries that contain invalid nodes (= deallocated) or
 * proxies as children. */
void bzla_rw_cache_gc(BzlaRwCache *cache);

#endif
