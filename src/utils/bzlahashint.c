/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlahashint.h"

#include <assert.h>

/*----------------------------------------------------------------------------*/

#define HOP_RANGE 32
#define ADD_RANGE 8 * HOP_RANGE

/*----------------------------------------------------------------------------*/

static inline uint32_t
hash(uint32_t h)
{
  return h;
  return h * 2654435761;
}

static inline size_t
pow2size(size_t size)
{
  return size;  // - HOP_RANGE;
}

static inline size_t
initsize(size_t size)
{
  return size;  // + HOP_RANGE;
}

#if 0
#ifndef NDEBUG
#include <stdio.h>
static void
print_int_hash_table (BzlaIntHashTable * t)
{
  size_t i;

  printf ("keys: ");
  for (i = 0; i < t->size; i++)
    {
      if (i % HOP_RANGE == 0)
	printf ("|");
      printf ("%d[%d]", t->keys[i], t->hop_info[i]);
      if (i < t->size - 1)
	printf (".");
    }
  printf ("|\n");
}
#endif
#endif

#if 0
static void
print_density (BzlaIntHashTable *t, int32_t key)
{
  size_t j, insert_pos = hash (key) & (pow2size (t->size) - 1);
  for (j = 0; j < t->size; j++)
    if (j % 20 == 0)
      printf ("|");
    else
      printf (" ");
  printf ("\n");
  for (j = 0; j < t->size; j++)
    if (j == insert_pos)
      printf ("%c", t->keys[j] ? 'O' : 'F');
    else
      printf ("%c", t->keys[j] ? 'x' : '.'); 
  printf ("\n");
}
#endif

/*
 * try to add 'key' to 't'.
 * if adding 'key' succeeds 'key' is stored in 't->keys' and the function
 * returns the position of 'key' in 't->keys'.
 * if adding 'key' does not succeed, the function return 't->size'.
 */
static size_t
add(BzlaIntHashTable *t, int32_t key)
{
  bool found, moved;
  size_t i, j, size, pos, move_pos, rem_move_dist;
  uint32_t h;
  uint8_t move_hop_info, *hop_info;
  int32_t *keys;
  BzlaHashTableData *data;

  keys     = t->keys;
  hop_info = t->hop_info;
  size     = t->size;
  data     = t->data;
  h        = hash(key);
  i        = h & (pow2size(size) - 1);

  /* search a free position within the ADD_RANGE window */
  found = false;
  for (j = 0, pos = i + j; j < ADD_RANGE && pos < size; j++, pos = i + j)
  {
    if (!keys[pos])
    {
      found = true;
      break;
    }
    /* already in hash table */
    else if (keys[pos] == key)
    {
      assert(pos < i + HOP_RANGE);
      return pos;
    }
  }

  /* no suitable index found for moving key, needs resizing */
  if (!found) return size;

  found = false;
  moved = true;
  do
  {
    assert(!keys[pos]);
    if (pos - i < HOP_RANGE)
    {
      found = true;
      break;
    }

    /* needs resizing */
    if (!moved) return size;

    /* 'pos' contains a free index */
    move_pos = pos - (HOP_RANGE - 1);
    moved    = false;
    for (j = HOP_RANGE - 1; j > 0; j--)
    {
      move_hop_info = hop_info[move_pos];
      rem_move_dist = HOP_RANGE - 1 - move_hop_info;

      /* not suitable for moving as remaining move distance 'rem_move_dist'
       * is smaller than the required move distance 'j' */
      if (rem_move_dist < j)
      {
        move_pos++;
        continue;
      }

      /* move key to free position 'pos' */
      keys[pos]     = keys[move_pos];
      hop_info[pos] = move_hop_info + j; /* update hop info */
      assert(hop_info[pos] < HOP_RANGE);
      keys[move_pos]     = 0;
      hop_info[move_pos] = 0;
      if (data)
      {
        data[pos] = data[move_pos];
        memset(&data[move_pos], 0, sizeof(*data));
        data[move_pos].as_ptr = 0;
      }
      pos   = move_pos;
      moved = true;
      break;
    }
  } while (true);

  assert(found);
  keys[pos]     = key;
  hop_info[pos] = pos - i; /* store number of hops */
  assert(hop_info[pos] < HOP_RANGE);
  t->count += 1;
  return pos;
}

static void
resize(BzlaIntHashTable *t)
{
#ifndef NDEBUG
  size_t old_count;
#endif
  size_t i, new_pos, old_size, new_size;
  int32_t key, *old_keys;
  uint8_t *old_hop_info;
  BzlaHashTableData *old_data;

  old_size     = t->size;
  old_keys     = t->keys;
  old_hop_info = t->hop_info;
  old_data     = t->data;
#ifndef NDEBUG
  old_count = t->count;
#endif
  assert(old_size > 0);
  new_size = initsize((pow2size(old_size)) * 2);
  BZLA_CNEWN(t->mm, t->keys, new_size);
  BZLA_CLRN(t->keys, new_size);
  BZLA_CNEWN(t->mm, t->hop_info, new_size);
  BZLA_CLRN(t->hop_info, new_size);
  if (old_data)
  {
    BZLA_CNEWN(t->mm, t->data, new_size);
    BZLA_CLRN(t->data, new_size);
  }
  t->count = 0;
  t->size  = new_size;

  for (i = 0; i < old_size; i++)
  {
    key = old_keys[i];
    if (!key) continue;
    new_pos = add(t, key);
    if (old_data) t->data[new_pos] = old_data[i];
    /* after resizing it should always be possible to find a new position */
    assert(new_pos < new_size);
  }

  BZLA_DELETEN(t->mm, old_keys, old_size);
  BZLA_DELETEN(t->mm, old_hop_info, old_size);
  if (old_data) BZLA_DELETEN(t->mm, old_data, old_size);
  assert(old_count == t->count);
}

/*----------------------------------------------------------------------------*/
/* hash table                                                                 */
/*----------------------------------------------------------------------------*/

BzlaIntHashTable *
bzla_hashint_table_new(BzlaMemMgr *mm)
{
  BzlaIntHashTable *res;

  BZLA_CNEW(mm, res);
  res->mm   = mm;
  res->size = initsize(HOP_RANGE);
  BZLA_CNEWN(mm, res->keys, res->size);
  BZLA_CLRN(res->keys, res->size);
  BZLA_CNEWN(mm, res->hop_info, res->size);
  BZLA_CLRN(res->hop_info, res->size);
  return res;
}

void
bzla_hashint_table_delete(BzlaIntHashTable *t)
{
  assert(!t->data);
  BZLA_DELETEN(t->mm, t->keys, t->size);
  BZLA_DELETEN(t->mm, t->hop_info, t->size);
  BZLA_DELETE(t->mm, t);
}

size_t
bzla_hashint_table_size(BzlaIntHashTable *t)
{
  return sizeof(BzlaIntHashTable)
         + t->size * (sizeof(*t->keys) + sizeof(*t->hop_info));
}

size_t
bzla_hashint_table_add(BzlaIntHashTable *t, int32_t key)
{
  assert(key);

  size_t pos;

  //  print_density (t, key);
  pos = add(t, key);
  /* 'add(...)' returns 't->size' if 'key' could not be added to 't'. hence,
   * we need to resize 't'. */
  while (pos == t->size)  // TODO: loop may be obsolete
  {
    resize(t);
    pos = add(t, key);
  }
  return pos;
}

bool
bzla_hashint_table_contains(BzlaIntHashTable *t, int32_t key)
{
  return bzla_hashint_table_get_pos(t, key) != t->size;
}

void
bzla_hashint_table_clear(BzlaIntHashTable *t)
{
  assert(t);
  t->count = 0;
  memset(t->keys, 0, sizeof(*t->keys) * t->size);
  memset(t->hop_info, 0, sizeof(*t->hop_info) * t->size);
}

size_t
bzla_hashint_table_remove(BzlaIntHashTable *t, int32_t key)
{
  size_t pos;

  pos = bzla_hashint_table_get_pos(t, key);

  if (pos == t->size) return pos;

  assert(t->keys[pos] == key);
  t->keys[pos]     = 0;
  t->hop_info[pos] = 0;
  t->count -= 1;
  return pos;
}

size_t
bzla_hashint_table_get_pos(BzlaIntHashTable *t, int32_t key)
{
  size_t i, size, end;
  uint32_t h;
  int32_t *keys;

  keys = t->keys;
  size = t->size;
  h    = hash(key);
  i    = h & (pow2size(size) - 1);
  end  = i + HOP_RANGE;
  //  assert (end < size);
  if (end > size) end = size;

  for (; i < end; i++)
  {
    if (keys[i] == key) return i;
  }
  return size;
}

BzlaIntHashTable *
bzla_hashint_table_clone(BzlaMemMgr *mm, BzlaIntHashTable *table)
{
  assert(mm);

  BzlaIntHashTable *res;

  if (!table) return NULL;

  res = bzla_hashint_table_new(mm);
  while (res->size < table->size) resize(res);
  assert(res->size == table->size);
  memcpy(res->keys, table->keys, table->size * sizeof(*table->keys));
  memcpy(
      res->hop_info, table->hop_info, table->size * sizeof(*table->hop_info));
  res->count = table->count;
  return res;
}

/*----------------------------------------------------------------------------*/
/* hash map                                                                   */
/*----------------------------------------------------------------------------*/

BzlaIntHashTable *
bzla_hashint_map_new(BzlaMemMgr *mm)
{
  BzlaIntHashTable *res;

  res = bzla_hashint_table_new(mm);
  BZLA_CNEWN(mm, res->data, res->size);
  BZLA_CLRN(res->data, res->size);
  return res;
}

bool
bzla_hashint_map_contains(BzlaIntHashTable *t, int32_t key)
{
  assert(t->data);
  return bzla_hashint_table_contains(t, key);
}

void
bzla_hashint_map_clear(BzlaIntHashTable *t)
{
  memset(t->data, 0, sizeof(*t->data) * t->size);
  bzla_hashint_table_clear(t);
}

void
bzla_hashint_map_remove(BzlaIntHashTable *t,
                        int32_t key,
                        BzlaHashTableData *stored_data)
{
  assert(t->data);
  assert(bzla_hashint_map_contains(t, key));

  size_t pos;

  pos = bzla_hashint_table_remove(t, key);

  if (stored_data) *stored_data = t->data[pos];
  memset(&t->data[pos], 0, sizeof(BzlaHashTableData));
}

BzlaHashTableData *
bzla_hashint_map_add(BzlaIntHashTable *t, int32_t key)
{
  assert(t->data);

  size_t pos;
  pos = bzla_hashint_table_add(t, key);
  return &t->data[pos];
}

BzlaHashTableData *
bzla_hashint_map_get(BzlaIntHashTable *t, int32_t key)
{
  assert(t->data);

  size_t pos;

  pos = bzla_hashint_table_get_pos(t, key);
  if (pos == t->size) return 0;
  return &t->data[pos];
}

void
bzla_hashint_map_delete(BzlaIntHashTable *t)
{
  assert(t->data);

  BZLA_DELETEN(t->mm, t->data, t->size);
  t->data = 0;
  bzla_hashint_table_delete(t);
}

BzlaIntHashTable *
bzla_hashint_map_clone(BzlaMemMgr *mm,
                       BzlaIntHashTable *table,
                       BzlaCloneHashTableData cdata,
                       const void *data_map)
{
  assert(mm);

  size_t i;
  BzlaIntHashTable *res;

  if (!table) return NULL;

  res = bzla_hashint_table_clone(mm, table);
  BZLA_CNEWN(mm, res->data, res->size);
  if (cdata)
  {
    for (i = 0; i < res->size; i++)
    {
      if (!table->keys[i]) continue;
      cdata(mm, data_map, &table->data[i], &res->data[i]);
    }
  }
  else /* as_ptr does not have to be cloned */
  {
    memcpy(res->data, table->data, table->size * sizeof(*table->data));
  }

  assert(table->count == res->count);

  return res;
}

/*----------------------------------------------------------------------------*/
/* iterators                                                                  */
/*----------------------------------------------------------------------------*/

void
bzla_iter_hashint_init(BzlaIntHashTableIterator *it, const BzlaIntHashTable *t)
{
  assert(it);
  assert(t);

  it->cur_pos = 0;
  it->t       = t;
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
}

bool
bzla_iter_hashint_has_next(const BzlaIntHashTableIterator *it)
{
  assert(it);
  return it->cur_pos < it->t->size;
}

int32_t
bzla_iter_hashint_next(BzlaIntHashTableIterator *it)
{
  assert(it);

  int32_t res;

  res = it->t->keys[it->cur_pos++];
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
  return res;
}

BzlaHashTableData *
bzla_iter_hashint_next_data(BzlaIntHashTableIterator *it)
{
  assert(it);
  assert(it->t->data);

  BzlaHashTableData *res;

  res = &it->t->data[it->cur_pos++];
  while (it->cur_pos < it->t->size && !it->t->keys[it->cur_pos])
    it->cur_pos += 1;
  return res;
}

/*------------------------------------------------------------------------*/
