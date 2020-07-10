/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2013-2015 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */
#ifndef BZLACHKCLONE_H_INCLUDED
#define BZLACHKCLONE_H_INCLUDED

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

#include "bzlacore.h"
#include "bzlaopt.h"
#include "bzlasat.h"

void bzla_chkclone(Bzla *bzla, Bzla *clone);

void bzla_chkclone_exp(Bzla *bzla,
                       Bzla *clone,
                       const BzlaNode *exp,
                       const BzlaNode *cexp);

void bzla_chkclone_sort(Bzla *bzla,
                        Bzla *clone,
                        const BzlaSort *sort,
                        const BzlaSort *cexp);

#define BZLA_CHKCLONE_NORES(fun, args...) \
  do                                      \
  {                                       \
    if (!bzla->clone) break;              \
    boolector_##fun(bzla->clone, ##args); \
    bzla_chkclone(bzla, bzla->clone);     \
  } while (0)

#define BZLA_CHKCLONE_RES_INT(res, fun, args...)             \
  do                                                         \
  {                                                          \
    if (!bzla->clone) break;                                 \
    int32_t cloneres = boolector_##fun(bzla->clone, ##args); \
    (void) cloneres;                                         \
    assert(cloneres == res);                                 \
    bzla_chkclone(bzla, bzla->clone);                        \
  } while (0)

#define BZLA_CHKCLONE_RES_UINT(res, fun, args...)             \
  do                                                          \
  {                                                           \
    if (!bzla->clone) break;                                  \
    uint32_t cloneres = boolector_##fun(bzla->clone, ##args); \
    (void) cloneres;                                          \
    assert(cloneres == res);                                  \
    bzla_chkclone(bzla, bzla->clone);                         \
  } while (0)

#define BZLA_CHKCLONE_RES_BOOL(res, fun, args...)         \
  do                                                      \
  {                                                       \
    if (!bzla->clone) break;                              \
    bool cloneres = boolector_##fun(bzla->clone, ##args); \
    (void) cloneres;                                      \
    assert(cloneres == res);                              \
    bzla_chkclone(bzla, bzla->clone);                     \
  } while (0)

#define BZLA_CHKCLONE_RES_PTR(res, fun, args...)                          \
  do                                                                      \
  {                                                                       \
    if (!bzla->clone) break;                                              \
    BzlaNode *cloneres =                                                  \
        BZLA_IMPORT_BOOLECTOR_NODE(boolector_##fun(bzla->clone, ##args)); \
    (void) cloneres;                                                      \
    bzla_chkclone_exp(bzla, bzla->clone, res, cloneres);                  \
    bzla_chkclone(bzla, bzla->clone);                                     \
  } while (0)

#define BZLA_CHKCLONE_RES_STR(res, fun, args...)                 \
  do                                                             \
  {                                                              \
    if (!bzla->clone) break;                                     \
    const char *cloneres = boolector_##fun(bzla->clone, ##args); \
    (void) cloneres;                                             \
    if (!res)                                                    \
      assert(!cloneres);                                         \
    else                                                         \
      assert(!strcmp(cloneres, res));                            \
    bzla_chkclone(bzla, bzla->clone);                            \
  } while (0)

#define BZLA_CHKCLONE_RES_SORT(res, fun, args...)                         \
  do                                                                      \
  {                                                                       \
    if (!bzla->clone) break;                                              \
    const BzlaSortId cloneres =                                           \
        BZLA_IMPORT_BOOLECTOR_SORT(boolector_##fun(bzla->clone, ##args)); \
    const BzlaSort *s0, *s1;                                              \
    s0 = bzla_sort_get_by_id(bzla, res);                                  \
    s1 = bzla_sort_get_by_id(bzla->clone, cloneres);                      \
    bzla_chkclone_sort(bzla, bzla->clone, s0, s1);                        \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
