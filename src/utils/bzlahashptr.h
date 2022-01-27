/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLA_PTR_HASH_H_INCLUDED
#define BZLA_PTR_HASH_H_INCLUDED

#include <assert.h>
#include <stdbool.h>
#include <string.h>

#include "utils/bzlahash.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaPtrHashTable BzlaPtrHashTable;
typedef struct BzlaPtrHashBucket BzlaPtrHashBucket;

typedef void *(*BzlaCloneKeyPtr)(BzlaMemMgr *mm,
                                 const void *map,
                                 const void *key);
typedef void (*BzlaCloneDataPtr)(BzlaMemMgr *mm,
                                 const void *map,
                                 BzlaHashTableData *data,
                                 BzlaHashTableData *cloned_data);

struct BzlaPtrHashBucket
{
  /* public:
   */
  void *key;

  BzlaHashTableData data;

  BzlaPtrHashBucket *next; /* chronologically */
  BzlaPtrHashBucket *prev; /* chronologically */

  /* private:
   */
  BzlaPtrHashBucket *chain; /* collision chain */
};

struct BzlaPtrHashTable
{
  BzlaMemMgr *mm;

  uint32_t size;
  uint32_t count;
  BzlaPtrHashBucket **table;

  BzlaHashPtr hash;
  BzlaCmpPtr cmp;

  BzlaPtrHashBucket *first; /* chronologically */
  BzlaPtrHashBucket *last;  /* chronologically */
};

/*------------------------------------------------------------------------*/

BzlaPtrHashTable *bzla_hashptr_table_new(BzlaMemMgr *, BzlaHashPtr, BzlaCmpPtr);

/* Clone hash table. 'ckey' is a function mapping key to cloned key,
 * 'cdata' is a function mapping data to cloned data (note: as_ptr vs.
 * as_int!). 'key_map' represents a map mapping key to cloned key values.
 * 'data_map' represents a map mapping data to cloned data values. */
BzlaPtrHashTable *bzla_hashptr_table_clone(BzlaMemMgr *mm,
                                           BzlaPtrHashTable *table,
                                           BzlaCloneKeyPtr ckey,
                                           BzlaCloneDataPtr cdata,
                                           const void *key_map,
                                           const void *data_map);

void bzla_hashptr_table_delete(BzlaPtrHashTable *p2iht);

BzlaPtrHashBucket *bzla_hashptr_table_get(BzlaPtrHashTable *p2iht,
                                          const void *key);

BzlaPtrHashBucket *bzla_hashptr_table_add(BzlaPtrHashTable *p2iht, void *key);

/* Remove from hash table the bucket with the key.  The key has to be an
 * element of the hash table.  If 'stored_data_ptr' is non zero, then data
 * to which the given key was mapped is copied to this location.   The same
 * applies to 'stored_key_ptr'.  If you traverse/iterate a hash table
 * through the chronological chains, then you can remove elements while
 * traversing the hash table.
 */
void bzla_hashptr_table_remove(BzlaPtrHashTable *,
                               void *key,
                               void **stored_key_ptr,
                               BzlaHashTableData *stored_data_ptr);

uint32_t bzla_hash_str(const void *str);

#define bzla_compare_str ((BzlaCmpPtr) strcmp)

/*------------------------------------------------------------------------*/
/* iterators     		                                          */
/*------------------------------------------------------------------------*/

#define BZLA_PTR_HASH_TABLE_ITERATOR_STACK_SIZE 8

typedef struct BzlaPtrHashTableIterator
{
  BzlaPtrHashBucket *bucket;
  void *cur;
  bool reversed;
  uint8_t num_queued;
  uint8_t pos;
  const BzlaPtrHashTable *stack[BZLA_PTR_HASH_TABLE_ITERATOR_STACK_SIZE];
} BzlaPtrHashTableIterator;

void bzla_iter_hashptr_init(BzlaPtrHashTableIterator *it,
                            const BzlaPtrHashTable *t);
void bzla_iter_hashptr_init_reversed(BzlaPtrHashTableIterator *it,
                                     const BzlaPtrHashTable *t);
void bzla_iter_hashptr_queue(BzlaPtrHashTableIterator *it,
                             const BzlaPtrHashTable *t);
bool bzla_iter_hashptr_has_next(const BzlaPtrHashTableIterator *it);
void *bzla_iter_hashptr_next(BzlaPtrHashTableIterator *it);
BzlaHashTableData *bzla_iter_hashptr_next_data(BzlaPtrHashTableIterator *it);

/*------------------------------------------------------------------------*/
#endif
