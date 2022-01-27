/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAASS_H_INCLUDED
#define BZLAASS_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "utils/bzlamem.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaBVAss BzlaBVAss;
typedef struct BzlaBVAssList BzlaBVAssList;

struct BzlaBVAss
{
#ifndef NDEBUG
  const char *cloned_assignment; /* needed for shadow clone only */
#endif
  BzlaBVAss *prev;
  BzlaBVAss *next;
};

struct BzlaBVAssList
{
  BzlaMemMgr *mm;
  uint32_t count;
  BzlaBVAss *first;
  BzlaBVAss *last;
};

/* Create new bv assignment list. */
BzlaBVAssList *bzla_ass_new_bv_list(BzlaMemMgr *mm);

/* Clone bv assignment list. */
BzlaBVAssList *bzla_ass_clone_bv_list(BzlaMemMgr *mm, BzlaBVAssList *list);

/* Delete bv assignment list. */
void bzla_ass_delete_bv_list(BzlaBVAssList *list, bool auto_cleanup);

/* Get BzlaBVAss bucket reference from bv assignment string. */
BzlaBVAss *bzla_ass_get_bv(const char *ass);

/* Get bv assignment string from BzlaBVAss bucket. */
const char *bzla_ass_get_bv_str(BzlaBVAss *ass);

/* Create new bv assignment and add it to the list. */
BzlaBVAss *bzla_ass_new_bv(BzlaBVAssList *list, char *ass);

/* Release bv assignment and remove it from the list. */
void bzla_ass_release_bv(BzlaBVAssList *list, const char *ass);

/*------------------------------------------------------------------------*/

typedef struct BzlaFunAss BzlaFunAss;
typedef struct BzlaFunAssList BzlaFunAssList;

struct BzlaFunAss
{
  char **cloned_indices;
  char **cloned_values;
  uint32_t size;
  BzlaFunAss *prev;
  BzlaFunAss *next;
};

struct BzlaFunAssList
{
  BzlaMemMgr *mm;
  uint32_t count;
  BzlaFunAss *first;
  BzlaFunAss *last;
};

/* Create new array assignment list. */
BzlaFunAssList *bzla_ass_new_fun_list(BzlaMemMgr *mm);

/* Clone array assignment list. */
BzlaFunAssList *bzla_ass_clone_fun_list(BzlaMemMgr *mm, BzlaFunAssList *list);

/* Delete array assignment list. */
void bzla_ass_delete_fun_list(BzlaFunAssList *list, bool auto_cleanup);

/* Get BzlaFunAss bucket reference from indices reference. */
BzlaFunAss *bzla_ass_get_fun(const char **indices,
                             const char **values,
                             uint32_t size);

/* Get indices and values references from BzlaFunAss bucket. */
void bzla_ass_get_fun_indices_values(BzlaFunAss *ass,
                                     char ***indices,
                                     char ***values,
                                     uint32_t size);

/* Create new array assignment and add it to the list. */
BzlaFunAss *bzla_ass_new_fun(BzlaFunAssList *list,
                             char **indices,
                             char **values,
                             uint32_t size);

/* Release array assignment and remove it from the list. */
void bzla_ass_release_fun(BzlaFunAssList *list,
                          char **indices,
                          char **values,
                          uint32_t size);

#endif
