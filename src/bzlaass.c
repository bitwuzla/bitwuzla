/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaass.h"

#include <assert.h>
#include <stdbool.h>

/*------------------------------------------------------------------------*/

BzlaBVAssList *
bzla_ass_new_bv_list(BzlaMemMgr *mm)
{
  assert(mm);

  BzlaBVAssList *res;

  BZLA_CNEW(mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BzlaBVAssList *
bzla_ass_clone_bv_list(BzlaMemMgr *mm, BzlaBVAssList *list)
{
  assert(mm);
  assert(list);

  BzlaBVAssList *res;
  BzlaBVAss *bvass;

  res = bzla_ass_new_bv_list(mm);
  for (bvass = list->first; bvass; bvass = bvass->next)
    (void) bzla_ass_new_bv(res, (char *) bzla_ass_get_bv_str(bvass));

  return res;
}

void
bzla_ass_delete_bv_list(BzlaBVAssList *list, bool auto_cleanup)
{
  assert(list);

  BzlaBVAss *bvass, *tmp;

  assert(auto_cleanup || list->count == 0);

  if (auto_cleanup)
  {
    bvass = list->first;
    while (bvass)
    {
      tmp   = bvass;
      bvass = bvass->next;
      bzla_ass_release_bv(list, (char *) bzla_ass_get_bv_str(tmp));
    }
  }
  BZLA_DELETE(list->mm, list);
}

BzlaBVAss *
bzla_ass_get_bv(const char *ass)
{
  assert(ass);
  return (BzlaBVAss *) (ass - sizeof(BzlaBVAss));
}

const char *
bzla_ass_get_bv_str(BzlaBVAss *ass)
{
  return (const char *) ((char *) ass + sizeof(BzlaBVAss));
}

BzlaBVAss *
bzla_ass_new_bv(BzlaBVAssList *list, char *ass)
{
  assert(list);
  assert(ass);

  BzlaBVAss *res;
  uint32_t len;

  len = strlen(ass) + 1;
  res = bzla_mem_calloc(list->mm, sizeof(BzlaBVAss) + len, sizeof(char));
  strcpy((char *) res + sizeof(BzlaBVAss), ass);
  res->prev = list->last;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;
  list->count += 1;

  return res;
}

bool
bzla_find_bv_assignment_dbg(BzlaBVAssList *list, BzlaBVAss *ass)
{
  assert(list);
  assert(ass);

  bool res;
  BzlaBVAss *b;

  for (res = false, b = list->first; b; b = b->next)
    if ((res = (b == ass))) break;
  return res;
}

void
bzla_ass_release_bv(BzlaBVAssList *list, const char *ass)
{
  assert(list);
  assert(ass);

  BzlaBVAss *bvass;

  assert(list->count);
  list->count -= 1;

  bvass = bzla_ass_get_bv(ass);
  assert(bzla_find_bv_assignment_dbg(list, bvass));

  if (bvass->prev)
    bvass->prev->next = bvass->next;
  else
    list->first = bvass->next;

  if (bvass->next)
    bvass->next->prev = bvass->prev;
  else
    list->last = bvass->prev;
  bzla_mem_free(list->mm, bvass, sizeof(BzlaBVAss) + strlen(ass) + 1);
}

/*------------------------------------------------------------------------*/

BzlaFunAssList *
bzla_ass_new_fun_list(BzlaMemMgr *mm)
{
  assert(mm);

  BzlaFunAssList *res;

  BZLA_CNEW(mm, res);
  res->mm   = mm;
  res->last = res->first;
  return res;
}

BzlaFunAssList *
bzla_ass_clone_fun_list(BzlaMemMgr *mm, BzlaFunAssList *list)
{
  assert(mm);
  assert(list);

  BzlaFunAssList *res;
  BzlaFunAss *funass;
  char **ind, **val, **cind, **cval;

  res = bzla_ass_new_fun_list(mm);
  for (funass = list->first; funass; funass = funass->next)
  {
    bzla_ass_get_fun_indices_values(funass, &ind, &val, funass->size);
    bzla_ass_get_fun_indices_values(
        bzla_ass_new_fun(res, ind, val, funass->size),
        &cind,
        &cval,
        funass->size);
    funass->cloned_indices = cind;
    funass->cloned_values  = cval;
  }

  return res;
}

void
bzla_ass_delete_fun_list(BzlaFunAssList *list, bool auto_cleanup)
{
  assert(list);

  BzlaFunAss *funass, *next;
  char **ind, **val;

  assert(auto_cleanup || list->count == 0);

  if (auto_cleanup)
  {
    for (funass = list->first, next = 0; funass; funass = next)
    {
      next = funass->next;
      bzla_ass_get_fun_indices_values(funass, &ind, &val, funass->size);
      bzla_ass_release_fun(list, ind, val, funass->size);
    }
  }
  BZLA_DELETE(list->mm, list);
}

BzlaFunAss *
bzla_ass_get_fun(const char **indices, const char **values, uint32_t size)
{
  assert(indices);
  assert(values);
  (void) values;
  assert(size);
  (void) size;

  BzlaFunAss *funass;

  funass = (BzlaFunAss *) ((char *) indices - sizeof(BzlaFunAss));
  assert(funass->size == size);
  return funass;
}

void
bzla_ass_get_fun_indices_values(BzlaFunAss *ass,
                                char ***indices,
                                char ***values,
                                uint32_t size)
{
  assert(ass);
  assert(indices);
  assert(values);
  assert(size);
  (void) size;

  assert(size == ass->size);
  *indices = (char **) ((char *) ass + sizeof(BzlaFunAss));
  *values  = (char **) ((char *) ass + sizeof(BzlaFunAss)
                       + ass->size * sizeof(char *));
}

BzlaFunAss *
bzla_ass_new_fun(BzlaFunAssList *list,
                 char **indices,
                 char **values,
                 uint32_t size)
{
  assert(list);
  assert(indices);
  assert(values);

  BzlaFunAss *res;
  char **ind, **val;
  uint32_t i;

  res = bzla_mem_calloc(
      list->mm, sizeof(BzlaFunAss) + 2 * size * sizeof(char *), sizeof(char));
  res->size = size;
  if (list->first)
    list->last->next = res;
  else
    list->first = res;
  list->last = res;

  bzla_ass_get_fun_indices_values(res, &ind, &val, size);
  for (i = 0; i < size; i++)
  {
    ind[i] = bzla_mem_strdup(list->mm, indices[i]);
    val[i] = bzla_mem_strdup(list->mm, values[i]);
  }

  list->count += 1;

  return res;
}

bool
bzla_find_array_assignment_dbg(BzlaFunAssList *list, BzlaFunAss *ass)
{
  assert(list);
  assert(ass);

  bool res;
  BzlaFunAss *a;

  for (res = 0, a = list->first; a; a = a->next)
    if ((res = (a == ass))) break;
  return res;
}

void
bzla_ass_release_fun(BzlaFunAssList *list,
                     char **indices,
                     char **values,
                     uint32_t size)

{
  assert(list);
  assert(indices);
  assert(values);
  assert(size);

  uint32_t i;
  BzlaFunAss *funass;

  assert(list->count);
  list->count -= 1;

  funass =
      bzla_ass_get_fun((const char **) indices, (const char **) values, size);
  assert(size == funass->size);
  assert(bzla_find_array_assignment_dbg(list, funass));

  if (funass->prev)
    funass->prev->next = funass->next;
  else
    list->first = funass->next;

  if (funass->next)
    funass->next->prev = funass->prev;
  else
    list->last = funass->prev;

  for (i = 0; i < size; i++)
  {
    bzla_mem_freestr(list->mm, indices[i]);
    bzla_mem_freestr(list->mm, values[i]);
  }
  bzla_mem_free(
      list->mm, funass, sizeof(BzlaFunAss) + 2 * size * sizeof(char *));
}
