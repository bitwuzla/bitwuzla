/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlahashptr.h"

static uint32_t
bzla_hash_ptr(const void *p)
{
  return 1183477 * (uint32_t)(uintptr_t) p;
}

static int32_t
bzla_compare_ptr(const void *p, const void *q)
{
  return ((uintptr_t) p) != ((uintptr_t) q);
}

static void
bzla_enlarge_ptr_hash_table(BzlaPtrHashTable *p2iht)
{
  BzlaPtrHashBucket *p, *chain, **old_table, **new_table;
  uint32_t old_size, new_size, i, h;
  BzlaHashPtr hash;

  old_size  = p2iht->size;
  old_table = p2iht->table;

  new_size = old_size ? 2 * old_size : 1;
  BZLA_CNEWN(p2iht->mm, new_table, new_size);

  hash = p2iht->hash;

  for (i = 0; i < old_size; i++)
    for (p = old_table[i]; p; p = chain)
    {
      chain = p->chain;
      h     = hash(p->key);
      h &= new_size - 1;
      p->chain     = new_table[h];
      new_table[h] = p;
    }

  BZLA_DELETEN(p2iht->mm, old_table, old_size);

  p2iht->size  = new_size;
  p2iht->table = new_table;
}

BzlaPtrHashTable *
bzla_hashptr_table_new(BzlaMemMgr *mm, BzlaHashPtr hash, BzlaCmpPtr cmp)
{
  BzlaPtrHashTable *res;

  BZLA_NEW(mm, res);
  BZLA_CLR(res);

  res->mm   = mm;
  res->hash = hash ? hash : bzla_hash_ptr;
  res->cmp  = cmp ? cmp : bzla_compare_ptr;

  bzla_enlarge_ptr_hash_table(res);

  return res;
}

BzlaPtrHashTable *
bzla_hashptr_table_clone(BzlaMemMgr *mm,
                         BzlaPtrHashTable *table,
                         BzlaCloneKeyPtr ckey,
                         BzlaCloneDataPtr cdata,
                         const void *key_map,
                         const void *data_map)
{
  assert(mm);
  assert(ckey);

  BzlaPtrHashTable *res;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashBucket *b, *cloned_b;
  void *key, *cloned_key;

  if (!table) return NULL;

  res = bzla_hashptr_table_new(mm, table->hash, table->cmp);
  while (res->size < table->size) bzla_enlarge_ptr_hash_table(res);
  assert(res->size == table->size);

  bzla_iter_hashptr_init(&it, table);
  while (bzla_iter_hashptr_has_next(&it))
  {
    b          = it.bucket;
    key        = bzla_iter_hashptr_next(&it);
    cloned_key = ckey(mm, key_map, key);
    assert(cloned_key);
    cloned_b            = bzla_hashptr_table_add(res, cloned_key);
    cloned_b->data.flag = b->data.flag;
    if (!cdata)
      assert(b->data.as_ptr == 0);
    else
      cdata(mm, data_map, &b->data, &cloned_b->data);
  }

  assert(table->count == res->count);

  return res;
}

void
bzla_hashptr_table_delete(BzlaPtrHashTable *p2iht)
{
  BzlaPtrHashBucket *p, *next;

  for (p = p2iht->first; p; p = next)
  {
    next = p->next;
    BZLA_DELETE(p2iht->mm, p);
  }

  BZLA_DELETEN(p2iht->mm, p2iht->table, p2iht->size);
  BZLA_DELETE(p2iht->mm, p2iht);
}

BzlaPtrHashBucket *
bzla_hashptr_table_get(BzlaPtrHashTable *p2iht, const void *key)
{
  BzlaPtrHashBucket *res, **p, *b;
  uint32_t i, h;

  assert(p2iht->size > 0);

  res = 0;
  h   = p2iht->hash(key);
  h &= p2iht->size - 1;

  for (i = 0, p = p2iht->table + h; i < p2iht->count; i++, p = &b->chain)
  {
    if (!(b = *p)) break;
    if (!p2iht->cmp(b->key, key))
    {
      res = b;
      break;
    }
  }

  return res;
}

static BzlaPtrHashBucket **
bzla_findpos_in_ptr_hash_table_pos(BzlaPtrHashTable *p2iht, void *key)
{
  BzlaPtrHashBucket **p, *b;
  uint32_t h;

  if (p2iht->count == p2iht->size) bzla_enlarge_ptr_hash_table(p2iht);

  assert(p2iht->size > 0);

  h = p2iht->hash(key);
  h &= p2iht->size - 1;

  for (p = p2iht->table + h; (b = *p) && p2iht->cmp(b->key, key); p = &b->chain)
    ;

  return p;
}

BzlaPtrHashBucket *
bzla_hashptr_table_add(BzlaPtrHashTable *p2iht, void *key)
{
  BzlaPtrHashBucket **p, *res;
  p = bzla_findpos_in_ptr_hash_table_pos(p2iht, key);
  assert(!*p);
  BZLA_CNEW(p2iht->mm, res);
  res->key = key;
  *p       = res;
  p2iht->count++;

  res->prev = p2iht->last;

  if (p2iht->first)
    p2iht->last->next = res;
  else
    p2iht->first = res;

  p2iht->last = res;

  return res;
}

/*
 * Uses djb2 string hash function from [1].
 *
 * [1] http://www.cse.yorku.ca/~oz/hash.html
 */
uint32_t
bzla_hash_str(const void *str)
{
  const char *p = (const char *) str;
  uint32_t c, hash = 5381;

  while ((c = *p++))
  {
    hash = ((hash << 5) + hash) + c;
  }

  return hash;
}

void
bzla_hashptr_table_remove(BzlaPtrHashTable *table,
                          void *key,
                          void **stored_key_ptr,
                          BzlaHashTableData *stored_data_ptr)
{
  BzlaPtrHashBucket **p, *bucket;

  p      = bzla_findpos_in_ptr_hash_table_pos(table, key);
  bucket = *p;

  assert(bucket);
  *p = bucket->chain;

  if (bucket->prev)
    bucket->prev->next = bucket->next;
  else
    table->first = bucket->next;

  if (bucket->next)
    bucket->next->prev = bucket->prev;
  else
    table->last = bucket->prev;

  assert(table->count > 0);
  table->count--;

  if (stored_key_ptr) *stored_key_ptr = bucket->key;

  if (stored_data_ptr) *stored_data_ptr = bucket->data;

  BZLA_DELETE(table->mm, bucket);
}

/*------------------------------------------------------------------------*/
/* iterators     		                                          */
/*------------------------------------------------------------------------*/

void
bzla_iter_hashptr_init(BzlaPtrHashTableIterator *it, const BzlaPtrHashTable *t)
{
  assert(it);
  assert(t);

  it->bucket                  = t->first;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = false;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
bzla_iter_hashptr_init_reversed(BzlaPtrHashTableIterator *it,
                                const BzlaPtrHashTable *t)
{
  assert(it);
  assert(t);

  it->bucket                  = t->last;
  it->cur                     = it->bucket ? it->bucket->key : 0;
  it->reversed                = true;
  it->num_queued              = 0;
  it->pos                     = 0;
  it->stack[it->num_queued++] = t;
}

void
bzla_iter_hashptr_queue(BzlaPtrHashTableIterator *it, const BzlaPtrHashTable *t)
{
  assert(it);
  assert(t);
  assert(it->num_queued < BZLA_PTR_HASH_TABLE_ITERATOR_STACK_SIZE);

  /* if initial table is empty, initialize with queued table */
  if (!it->bucket)
  {
    it->bucket = it->reversed ? t->last : t->first;
    it->cur    = it->bucket ? it->bucket->key : 0;
    it->pos += 1;
  }
  it->stack[it->num_queued++] = t;
}

bool
bzla_iter_hashptr_has_next(const BzlaPtrHashTableIterator *it)
{
  assert(it);
  return it->cur != 0;
}

void *
bzla_iter_hashptr_next(BzlaPtrHashTableIterator *it)
{
  assert(it);
  assert(it->bucket);
  assert(it->cur);

  void *res;
  res = it->cur;
  if (it->bucket)
    it->bucket = it->reversed ? it->bucket->prev : it->bucket->next;

  while (!it->bucket)
  {
    it->pos += 1;
    if (it->pos >= it->num_queued) break;
    it->bucket =
        it->reversed ? it->stack[it->pos]->last : it->stack[it->pos]->first;
  }

  it->cur = it->bucket ? it->bucket->key : 0;
  return res;
}

BzlaHashTableData *
bzla_iter_hashptr_next_data(BzlaPtrHashTableIterator *it)
{
  assert(it);
  assert(it->bucket);
  assert(it->cur);

  void *res;

  res = &it->bucket->data;
  bzla_iter_hashptr_next(it);
  return res;
}

/*------------------------------------------------------------------------*/
