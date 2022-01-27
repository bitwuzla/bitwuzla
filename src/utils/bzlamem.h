/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAMEM_H_INCLUDED
#define BZLAMEM_H_INCLUDED

#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#define BZLA_NEWN(mm, ptr, nelems)                                         \
  do                                                                       \
  {                                                                        \
    (ptr) = (typeof(ptr)) bzla_mem_malloc((mm), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BZLA_CNEWN(mm, ptr, nelems)                                       \
  do                                                                      \
  {                                                                       \
    (ptr) = (typeof(ptr)) bzla_mem_calloc((mm), (nelems), sizeof *(ptr)); \
  } while (0)

#define BZLA_CLRN(ptr, nelems)                  \
  do                                            \
  {                                             \
    memset((ptr), 0, (nelems) * sizeof *(ptr)); \
  } while (0)

#define BZLA_DELETEN(mm, ptr, nelems)                     \
  do                                                      \
  {                                                       \
    bzla_mem_free((mm), (ptr), (nelems) * sizeof *(ptr)); \
  } while (0)

#define BZLA_REALLOC(mm, p, o, n)                             \
  do                                                          \
  {                                                           \
    (p) = (typeof(p)) bzla_mem_realloc(                       \
        (mm), (p), ((o) * sizeof *(p)), ((n) * sizeof *(p))); \
  } while (0)

#define BZLA_NEW(mm, ptr) BZLA_NEWN((mm), (ptr), 1)

#define BZLA_CNEW(mm, ptr) BZLA_CNEWN((mm), (ptr), 1)

#define BZLA_CLR(ptr) BZLA_CLRN((ptr), 1)

#define BZLA_DELETE(mm, ptr) BZLA_DELETEN((mm), (ptr), 1)

#define BZLA_ENLARGE(mm, p, o, n)            \
  do                                         \
  {                                          \
    size_t internaln = (o) ? 2 * (o) : 1;    \
    BZLA_REALLOC((mm), (p), (o), internaln); \
    (n) = internaln;                         \
  } while (0)

/*------------------------------------------------------------------------*/

struct BzlaMemMgr
{
  size_t allocated;
  size_t maxallocated;
  size_t sat_allocated;
  size_t sat_maxallocated;
};

typedef struct BzlaMemMgr BzlaMemMgr;

/*------------------------------------------------------------------------*/

BzlaMemMgr *bzla_mem_mgr_new(void);

void bzla_mem_mgr_delete(BzlaMemMgr *mm);

void *bzla_mem_sat_malloc(BzlaMemMgr *mm, size_t size);

void *bzla_mem_sat_realloc(BzlaMemMgr *mm, void *, size_t oldsz, size_t newsz);

void bzla_mem_sat_free(BzlaMemMgr *mm, void *p, size_t freed);

void *bzla_mem_malloc(BzlaMemMgr *mm, size_t size);

void *bzla_mem_realloc(BzlaMemMgr *mm, void *, size_t oldsz, size_t newsz);

void *bzla_mem_calloc(BzlaMemMgr *mm, size_t nobj, size_t size);

void bzla_mem_free(BzlaMemMgr *mm, void *p, size_t freed);

char *bzla_mem_strdup(BzlaMemMgr *mm, const char *str);

void bzla_mem_freestr(BzlaMemMgr *mm, char *str);

size_t bzla_mem_parse_error_msg_length(const char *name,
                                       const char *fmt,
                                       va_list ap);

char *bzla_mem_parse_error_msg(BzlaMemMgr *,
                               const char *name,
                               int32_t lineno,
                               int32_t columnno,
                               const char *fmt,
                               va_list,
                               size_t bytes);
#endif
