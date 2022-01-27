/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlasort.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>

#include "bzlacore.h"
#include "bzlanode.h"
#include "utils/bzlaabort.h"
#include "utils/bzlautil.h"

#define BZLA_SORT_UNIQUE_TABLE_LIMIT 30

#define BZLA_FULL_SORT_UNIQUE_TABLE(table) \
  ((table)->num_elements >= (table)->size  \
   && bzla_util_log_2((table)->size) < BZLA_SORT_UNIQUE_TABLE_LIMIT)

static void
inc_sort_ref_counter(BzlaSort *sort)
{
  assert(sort);
  BZLA_ABORT(sort->refs == INT32_MAX, "Sort reference counter overflow");
  sort->refs++;
}

static uint32_t
compute_hash_sort(const BzlaSort *sort, uint32_t table_size)
{
  assert(sort);
  assert(table_size);
  assert(bzla_util_is_power_of_2(table_size));

  uint32_t i, res, tmp;

  tmp = 0;

  switch (sort->kind)
  {
    default:
#if 0
      case BZLA_BOOL_SORT:
	assert (sort->kind == BZLA_BOOL_SORT);
        res = 0;
	break;
#endif
    case BZLA_BV_SORT: res = sort->bitvec.width; break;
#if 0
      case BZLA_ARRAY_SORT:
        res = sort->array.index->id;
        tmp = sort->array.element->id;
	break;

      case BZLA_LST_SORT:
        res = sort->lst.head->id;
        tmp = sort->lst.tail->id;
        break;
#endif
    case BZLA_FP_SORT:
      res = sort->fp.width_exp;
      tmp = sort->fp.width_sig;
      break;

    case BZLA_FUN_SORT:
      res = sort->fun.domain->id;
      tmp = sort->fun.codomain->id;
      break;

    case BZLA_TUPLE_SORT:
      res = 0;
      for (i = 0; i < sort->tuple.num_elements; i++)
      {
        if ((i & 1) == 0)
          res += sort->tuple.elements[i]->id;
        else
          tmp += sort->tuple.elements[i]->id;
      }
      break;
  }

  res *= 444555667u;

  if (tmp)
  {
    res += tmp;
    res *= 123123137u;
  }

  res &= table_size - 1;

  return res;
}

static void
remove_from_sorts_unique_table_sort(BzlaSortUniqueTable *table, BzlaSort *sort)
{
  assert(table);
  assert(sort);
  assert(!sort->refs);
  assert(table->num_elements > 0);

  uint32_t hash;
  BzlaSort *prev, *cur;

  hash = compute_hash_sort(sort, table->size);
  prev = 0;
  cur  = table->chains[hash];

  while (cur != sort)
  {
    assert(cur);
    prev = cur;
    cur  = cur->next;
  }

  assert(cur);
  if (!prev)
    table->chains[hash] = cur->next;
  else
    prev->next = cur->next;

  table->num_elements--;
}

static int32_t
equal_sort(const BzlaSort *a, const BzlaSort *b)
{
  assert(a);
  assert(b);

  uint32_t i;

  if (a->kind != b->kind) return 0;

  switch (a->kind)
  {
    case BZLA_BV_SORT:
      if (a->bitvec.width != b->bitvec.width) return 0;
      break;

    case BZLA_FP_SORT:
      if (a->fp.width_exp != b->fp.width_exp) return 0;
      if (a->fp.width_sig != b->fp.width_sig) return 0;
      break;

    case BZLA_RM_SORT:
      // Always equal;
      break;

    case BZLA_FUN_SORT:
      if (a->fun.domain->id != b->fun.domain->id) return 0;
      if (a->fun.codomain->id != b->fun.codomain->id) return 0;
      if (a->fun.is_array != b->fun.is_array) return 0;
      break;

    case BZLA_TUPLE_SORT:
      if (a->tuple.num_elements != b->tuple.num_elements) return 0;
      for (i = 0; i < a->tuple.num_elements; i++)
        if (a->tuple.elements[i]->id != b->tuple.elements[i]->id) return 0;
      break;

    default:
      assert(0);
  }

  return 1;
}

static BzlaSort **
find_sort(BzlaSortUniqueTable *table, const BzlaSort *pattern)
{
  assert(table);
  assert(pattern);

  BzlaSort **res, *sort;
  uint32_t hash;
  hash = compute_hash_sort(pattern, table->size);
  assert(hash < (uint32_t) table->size);
  for (res = table->chains + hash; (sort = *res) && !equal_sort(sort, pattern);
       res = &sort->next)
  {
    assert(sort->refs > 0);
  }
  return res;
}

static void
enlarge_sorts_unique_table(BzlaSortUniqueTable *table)
{
  assert(table);

  BzlaSort *cur, *temp, **new_chains;
  uint32_t size, new_size, i, hash;
  BzlaMemMgr *mm;

  mm       = table->mm;
  size     = table->size;
  new_size = size << 1;
  assert(new_size / size == 2);
  BZLA_CNEWN(mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = table->chains[i];
    while (cur)
    {
      temp             = cur->next;
      hash             = compute_hash_sort(cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BZLA_DELETEN(mm, table->chains, size);
  table->size   = new_size;
  table->chains = new_chains;
}

static void
release_sort(BzlaSortUniqueTable *table, BzlaSort *sort)
{
  assert(table);
  assert(sort);
  assert(sort->refs > 0);

  uint32_t i;

  if (--sort->refs > 0) return;

  remove_from_sorts_unique_table_sort(table, sort);

  switch (sort->kind)
  {
    default: break;
#if 0
      case BZLA_LST_SORT:
#ifndef NDEBUG
	sort->lst.head->parents--;
	sort->lst.tail->parents--;
#endif
        release_sort (table, sort->lst.head);
        release_sort (table, sort->lst.tail);
        break;

      case BZLA_ARRAY_SORT:
#ifndef NDEBUG
	sort->array.index->parents--;
	sort->array.element->parents--;
#endif
        release_sort (table, sort->array.index);
        release_sort (table, sort->array.element);
        break;
#endif
    case BZLA_FUN_SORT:
#ifndef NDEBUG
      sort->fun.domain->parents--;
      sort->fun.codomain->parents--;
#endif
      release_sort(table, sort->fun.domain);
      release_sort(table, sort->fun.codomain);
      break;

    case BZLA_TUPLE_SORT:
      for (i = 0; i < sort->tuple.num_elements; i++)
      {
#ifndef NDEBUG
        sort->tuple.elements[i]->parents--;
#endif
        release_sort(table, sort->tuple.elements[i]);
      }
      BZLA_DELETEN(table->mm, sort->tuple.elements, sort->tuple.num_elements);
      break;
  }

  assert(BZLA_PEEK_STACK(table->id2sort, sort->id) == sort);
  BZLA_POKE_STACK(table->id2sort, sort->id, 0);
  BZLA_DELETE(table->mm, sort);
}

BzlaSort *
bzla_sort_get_by_id(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  assert(id < BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort));
  return BZLA_PEEK_STACK(bzla->sorts_unique_table.id2sort, id);
}

BzlaSortId
bzla_sort_copy(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  inc_sort_ref_counter(sort);
  return id;
}

void
bzla_sort_release(Bzla *bzla, BzlaSortId id)
{
  assert(bzla);

  BzlaSort *sort;

  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  assert(sort->refs > 0);
  release_sort(&bzla->sorts_unique_table, sort);
}

static BzlaSort *
copy_sort(BzlaSort *sort)
{
  inc_sort_ref_counter(sort);
  return sort;
}

static BzlaSort *
create_sort(Bzla *bzla, BzlaSortUniqueTable *table, BzlaSort *pattern)
{
  assert(table);
  assert(pattern);

  uint32_t i;
  BzlaSort *res;

  BZLA_CNEW(table->mm, res);

#ifndef NDEBUG
  res->bzla = bzla;
#else
  (void) bzla;
#endif

  switch (pattern->kind)
  {
    case BZLA_BV_SORT:
      res->kind         = BZLA_BV_SORT;
      res->bitvec.width = pattern->bitvec.width;
      break;

    case BZLA_FP_SORT:
      res->kind         = BZLA_FP_SORT;
      res->fp.width_exp = pattern->fp.width_exp;
      res->fp.width_sig = pattern->fp.width_sig;
      break;

    case BZLA_FUN_SORT:
      res->kind         = BZLA_FUN_SORT;
      res->fun.domain   = copy_sort(pattern->fun.domain);
      res->fun.codomain = copy_sort(pattern->fun.codomain);
      res->fun.is_array = pattern->fun.is_array;
#ifndef NDEBUG
      res->fun.domain->parents++;
      res->fun.codomain->parents++;
#endif
      break;

    case BZLA_RM_SORT: res->kind = BZLA_RM_SORT; break;

    case BZLA_TUPLE_SORT:
      res->kind               = BZLA_TUPLE_SORT;
      res->tuple.num_elements = pattern->tuple.num_elements;
      BZLA_NEWN(table->mm, res->tuple.elements, res->tuple.num_elements);
      for (i = 0; i < res->tuple.num_elements; i++)
      {
        res->tuple.elements[i] = copy_sort(pattern->tuple.elements[i]);
#ifndef NDEBUG
        res->tuple.elements[i]->parents++;
#endif
      }
      break;

    default: break;
  }
  assert(res->kind);
  res->id = BZLA_COUNT_STACK(table->id2sort);
  BZLA_PUSH_STACK(table->id2sort, res);
  assert(BZLA_COUNT_STACK(table->id2sort) == res->id + 1);
  assert(BZLA_PEEK_STACK(table->id2sort, res->id) == res);

  table->num_elements++;
  res->table = table;

  return res;
}

BzlaSortId
bzla_sort_bool(Bzla *bzla)
{
  return bzla_sort_bv(bzla, 1);
}

BzlaSortId
bzla_sort_bv(Bzla *bzla, uint32_t width)
{
  assert(bzla);
  assert(width > 0);

  BzlaSort *res, **pos, pattern;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  BZLA_CLR(&pattern);
  pattern.kind         = BZLA_BV_SORT;
  pattern.bitvec.width = width;
  pos                  = find_sort(table, &pattern);
  assert(pos);
  res = *pos;
  if (!res)
  {
    if (BZLA_FULL_SORT_UNIQUE_TABLE(table))
    {
      enlarge_sorts_unique_table(table);
      pos = find_sort(table, &pattern);
      assert(pos);
      res = *pos;
      assert(!res);
    }
    res  = create_sort(bzla, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter(res);
  return res->id;
}

static BzlaSortId
sort_fun_aux(Bzla *bzla,
             BzlaSortId domain_id,
             BzlaSortId codomain_id,
             bool is_array)
{
  assert(bzla);
  assert(domain_id);

  BzlaSort *domain, *codomain, *res, **pos, pattern;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  domain = bzla_sort_get_by_id(bzla, domain_id);
  assert(domain);
  assert(domain->refs > 0);
  assert(domain->table == table);
  assert(domain->kind == BZLA_TUPLE_SORT);
  codomain = bzla_sort_get_by_id(bzla, codomain_id);
  assert(codomain);
  assert(codomain->refs > 0);
  assert(codomain->table == table);

  BZLA_CLR(&pattern);
  pattern.kind         = BZLA_FUN_SORT;
  pattern.fun.domain   = domain;
  pattern.fun.codomain = codomain;
  pattern.fun.is_array = is_array;
  pos                  = find_sort(table, &pattern);
  assert(pos);
  res = *pos;
  if (!res)
  {
    if (BZLA_FULL_SORT_UNIQUE_TABLE(table))
    {
      enlarge_sorts_unique_table(table);
      pos = find_sort(table, &pattern);
      assert(pos);
      res = *pos;
      assert(!res);
    }
    res            = create_sort(bzla, table, &pattern);
    res->fun.arity = domain->tuple.num_elements;
    *pos           = res;
  }
  inc_sort_ref_counter(res);

  return res->id;
}

BzlaSortId
bzla_sort_array(Bzla *bzla, BzlaSortId index_id, BzlaSortId element_id)
{
  assert(bzla);
  assert(index_id < BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort));
  assert(element_id < BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort));

  BzlaSortId tup, res;

  tup = bzla_sort_tuple(bzla, &index_id, 1);
  res = sort_fun_aux(bzla, tup, element_id, true);
  bzla_sort_release(bzla, tup);
  return res;
}

#if 0
BzlaSortId
bzla_sort_lst (Bzla * bzla,
	       BzlaSortId head_id,
	       BzlaSortId tail_id)
{
  assert (bzla);
  assert (head_id < BZLA_COUNT_STACK (bzla->sorts_unique_table.id2sort));
  assert (tail_id < BZLA_COUNT_STACK (bzla->sorts_unique_table.id2sort));

  BzlaSort * res, ** pos, pattern, *head, *tail;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  head = bzla_sort_get_by_id (bzla, head_id);
  assert (head);
  assert (head->refs > 0);
  assert (head->table == table);
  tail = bzla_sort_get_by_id (bzla, tail_id);
  assert (tail);
  assert (tail->refs > 0);
  assert (tail->table == table);

  BZLA_CLR (&pattern);
  pattern.kind = BZLA_LST_SORT;
  pattern.lst.head = head;
  pattern.lst.tail = tail;
  pos = find_sort (table, &pattern);
  assert (pos);
  res = *pos;
  if (!res) 
    {
      if (BZLA_FULL_SORT_UNIQUE_TABLE (table))
	{
	  enlarge_sorts_unique_table (table);
	  pos = find_sort (table, &pattern);
	  assert (pos);
	  res = *pos;
	  assert (!res);
	}
      res = create_sort (bzla, table, &pattern);
      *pos = res;
    }
  inc_sort_ref_counter (res);
  return res->id;
}
#endif

BzlaSortId
bzla_sort_fp(Bzla *bzla, uint32_t ewidth, uint32_t swidth)
{
  assert(bzla);
  assert(ewidth > 0);
  assert(swidth > 0);

  BzlaSort *res, **pos, pattern;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  BZLA_CLR(&pattern);
  pattern.kind         = BZLA_FP_SORT;
  pattern.fp.width_exp = ewidth;
  pattern.fp.width_sig = swidth;
  pos                  = find_sort(table, &pattern);
  assert(pos);

  res = *pos;
  if (!res)
  {
    if (BZLA_FULL_SORT_UNIQUE_TABLE(table))
    {
      enlarge_sorts_unique_table(table);
      pos = find_sort(table, &pattern);
      assert(pos);
      res = *pos;
      assert(!res);
    }
    res  = create_sort(bzla, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter(res);
  return res->id;
}

BzlaSortId
bzla_sort_rm(Bzla *bzla)
{
  assert(bzla);

  assert(bzla);

  BzlaSort *res, **pos, pattern;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  BZLA_CLR(&pattern);
  pattern.kind = BZLA_RM_SORT;
  pos          = find_sort(table, &pattern);
  assert(pos);

  res = *pos;
  if (!res)
  {
    if (BZLA_FULL_SORT_UNIQUE_TABLE(table))
    {
      enlarge_sorts_unique_table(table);
      pos = find_sort(table, &pattern);
      assert(pos);
      res = *pos;
      assert(!res);
    }
    res  = create_sort(bzla, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter(res);
  return res->id;
}

BzlaSortId
bzla_sort_fun(Bzla *bzla, BzlaSortId domain_id, BzlaSortId codomain_id)
{
  return sort_fun_aux(bzla, domain_id, codomain_id, false);
}

BzlaSortId
bzla_sort_tuple(Bzla *bzla, BzlaSortId *element_ids, size_t num_elements)
{
  assert(bzla);
  assert(element_ids);
  assert(num_elements > 0);

  size_t i;
  BzlaSort *elements[num_elements], *res, **pos, pattern;
  BzlaSortUniqueTable *table;

  table = &bzla->sorts_unique_table;

  for (i = 0; i < num_elements; i++)
  {
    elements[i] = bzla_sort_get_by_id(bzla, element_ids[i]);
    assert(elements[i]);
    assert(elements[i]->table == table);
  }

  BZLA_CLR(&pattern);
  pattern.kind               = BZLA_TUPLE_SORT;
  pattern.tuple.num_elements = num_elements;
  pattern.tuple.elements     = elements;
  pos                        = find_sort(table, &pattern);
  assert(pos);
  res = *pos;
  if (!res)
  {
    if (BZLA_FULL_SORT_UNIQUE_TABLE(table))
    {
      enlarge_sorts_unique_table(table);
      pos = find_sort(table, &pattern);
      assert(pos);
      res = *pos;
      assert(!res);
    }
    res  = create_sort(bzla, table, &pattern);
    *pos = res;
  }
  inc_sort_ref_counter(res);
  return res->id;
}

uint32_t
bzla_sort_bv_get_width(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind != BZLA_BOOL_SORT);
#if 0
  /* special case for Bitwuzla as boolean are treated as bv of width 1 */
  if (sort->kind == BZLA_BOOL_SORT)
    return 1;
#endif
  assert(sort->kind == BZLA_BV_SORT);
  return sort->bitvec.width;
}

uint32_t
bzla_sort_fp_get_exp_width(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(bzla_sort_is_fp(bzla, id));
  return sort->fp.width_exp;
}

uint32_t
bzla_sort_fp_get_sig_width(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(bzla_sort_is_fp(bzla, id));
  return sort->fp.width_sig;
}

uint32_t
bzla_sort_fp_get_bv_width(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(bzla_sort_is_fp(bzla, id));
  return sort->fp.width_exp + sort->fp.width_sig;
}

uint32_t
bzla_sort_tuple_get_arity(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind == BZLA_TUPLE_SORT);
  return sort->tuple.num_elements;
}

BzlaSortId
bzla_sort_fun_get_codomain(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind == BZLA_FUN_SORT);
  return sort->fun.codomain->id;
}

BzlaSortId
bzla_sort_fun_get_domain(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind == BZLA_FUN_SORT);
  return sort->fun.domain->id;
}

uint32_t
bzla_sort_fun_get_arity(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind == BZLA_FUN_SORT);
  assert(sort->fun.domain->kind == BZLA_TUPLE_SORT);
  return sort->fun.domain->tuple.num_elements;
}

BzlaSortId
bzla_sort_array_get_index(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind != BZLA_ARRAY_SORT);
#if 0
  if (sort->kind == BZLA_ARRAY_SORT)
    return sort->array.index->id;
#endif
  assert(sort->kind == BZLA_FUN_SORT);
  assert(sort->fun.domain->tuple.num_elements == 1);
  return sort->fun.domain->tuple.elements[0]->id;
}

BzlaSortId
bzla_sort_array_get_element(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort->kind != BZLA_ARRAY_SORT);
#if 0
  if (sort->kind == BZLA_ARRAY_SORT)
    return sort->array.element->id;
#endif
  assert(sort->kind == BZLA_FUN_SORT);
  return sort->fun.codomain->id;
}

bool
bzla_sort_is_valid(Bzla *bzla, BzlaSortId id)
{
  return id < BZLA_COUNT_STACK(bzla->sorts_unique_table.id2sort)
         && BZLA_PEEK_STACK(bzla->sorts_unique_table.id2sort, id) != 0;
}

bool
bzla_sort_is_bool(Bzla *bzla, BzlaSortId id)
{
  return bzla_sort_is_bv(bzla, id) && bzla_sort_bv_get_width(bzla, id) == 1;
}

bool
bzla_sort_is_bv(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return sort->kind == BZLA_BV_SORT;
}

bool
bzla_sort_is_fp(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return sort->kind == BZLA_FP_SORT;
}

bool
bzla_sort_is_rm(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return sort->kind == BZLA_RM_SORT;
}

bool
bzla_sort_is_array(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return bzla_sort_is_fun(bzla, id) && sort->fun.is_array;
}

bool
bzla_sort_is_tuple(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return sort->kind == BZLA_TUPLE_SORT;
}

bool
bzla_sort_is_fun(Bzla *bzla, BzlaSortId id)
{
  BzlaSort *sort;
  sort = bzla_sort_get_by_id(bzla, id);
  assert(sort);
  return sort->kind == BZLA_FUN_SORT;
}

void
bzla_iter_tuple_sort_init(BzlaTupleSortIterator *it, Bzla *bzla, BzlaSortId id)
{
  assert(it);
  assert(bzla);
  assert(bzla_sort_is_tuple(bzla, id));
  it->pos   = 0;
  it->tuple = bzla_sort_get_by_id(bzla, id);
}

bool
bzla_iter_tuple_sort_has_next(const BzlaTupleSortIterator *it)
{
  assert(it);
  return it->pos < it->tuple->tuple.num_elements;
}

BzlaSortId
bzla_iter_tuple_sort_next(BzlaTupleSortIterator *it)
{
  assert(it);
  assert(it->pos < it->tuple->tuple.num_elements);

  BzlaSortId result;
  result = it->tuple->tuple.elements[it->pos]->id;
  it->pos += 1;
  return result;
}
