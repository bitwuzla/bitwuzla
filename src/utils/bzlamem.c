/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlamem.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "utils/bzlaabort.h"

/*------------------------------------------------------------------------*/

#define ADJUST()                                                            \
  do                                                                        \
  {                                                                         \
    if (mm->maxallocated < mm->allocated) mm->maxallocated = mm->allocated; \
  } while (0)

#define SAT_ADJUST()                              \
  do                                              \
  {                                               \
    if (mm->sat_maxallocated < mm->sat_allocated) \
      mm->sat_maxallocated = mm->sat_allocated;   \
  } while (0)

/*------------------------------------------------------------------------*/
/* This enables logging of all memory allocations.
 */
#if 0
#define BZLA_LOG_MEM(FMT, ARGS...)  \
  do                                \
  {                                 \
    fputs("[bzlalogmem] ", stdout); \
    printf(FMT, ##ARGS);            \
    fflush(stdout);                 \
  } while (0)
#else
#define BZLA_LOG_MEM(...) \
  do                      \
  {                       \
  } while (0)
#endif

/*------------------------------------------------------------------------*/

BzlaMemMgr *
bzla_mem_mgr_new(void)
{
  BzlaMemMgr *mm = (BzlaMemMgr *) malloc(sizeof(BzlaMemMgr));
  BZLA_ABORT(!mm, "out of memory in 'bzla_mem_mgr_new'");
  mm->allocated        = 0;
  mm->maxallocated     = 0;
  mm->sat_allocated    = 0;
  mm->sat_maxallocated = 0;
  return mm;
}

void *
bzla_mem_malloc(BzlaMemMgr *mm, size_t size)
{
  void *result;
  if (!size) return 0;
  assert(mm);
  result = malloc(size);
  BZLA_ABORT(!result, "out of memory in 'bzla_mem_malloc'");
  mm->allocated += size;
  ADJUST();
  BZLA_LOG_MEM("%p malloc %10ld\n", result, size);
  return result;
}

void *
bzla_mem_sat_malloc(BzlaMemMgr *mm, size_t size)
{
  void *result;
  if (!size) return 0;
  assert(mm);
  result = malloc(size);
  BZLA_ABORT(!result, "out of memory in 'bzla_mem_sat_malloc'");
  mm->sat_allocated += size;
  SAT_ADJUST();
  return result;
}

void *
bzla_mem_realloc(BzlaMemMgr *mm, void *p, size_t old_size, size_t new_size)
{
  void *result;
  assert(mm);
  assert(!p == !old_size);
  assert(mm->allocated >= old_size);
  BZLA_LOG_MEM("%p free   %10ld (realloc)\n", p, old_size);
  result = realloc(p, new_size);
  BZLA_ABORT(!result, "out of memory in 'bzla_mem_realloc'");
  mm->allocated -= old_size;
  mm->allocated += new_size;
  ADJUST();
  BZLA_LOG_MEM("%p malloc %10ld (realloc)\n", result, new_size);
  return result;
}

void *
bzla_mem_sat_realloc(BzlaMemMgr *mm, void *p, size_t old_size, size_t new_size)
{
  void *result;
  assert(mm);
  assert(!p == !old_size);
  assert(mm->sat_allocated >= old_size);
  result = realloc(p, new_size);
  BZLA_ABORT(!result, "out of memory in 'bzla_mem_sat_realloc'");
  mm->sat_allocated -= old_size;
  mm->sat_allocated += new_size;
  SAT_ADJUST();
  return result;
}

void *
bzla_mem_calloc(BzlaMemMgr *mm, size_t nobj, size_t size)
{
  size_t bytes = nobj * size;
  void *result;
  assert(mm);
  result = calloc(nobj, size);
  BZLA_ABORT(!result, "out of memory in 'bzla_mem_calloc'");
  mm->allocated += bytes;
  ADJUST();
  BZLA_LOG_MEM("%p malloc %10ld (calloc)\n", result, bytes);
  return result;
}

void
bzla_mem_free(BzlaMemMgr *mm, void *p, size_t freed)
{
  assert(mm);
  assert(!p == !freed);
  assert(mm->allocated >= freed);
  mm->allocated -= freed;
  BZLA_LOG_MEM("%p free   %10ld\n", p, freed);
  free(p);
}

void
bzla_mem_sat_free(BzlaMemMgr *mm, void *p, size_t freed)
{
  assert(mm);
  if (p) mm->sat_allocated -= freed;
  free(p);
}

char *
bzla_mem_strdup(BzlaMemMgr *mm, const char *str)
{
  char *res;

  if (str)
  {
    res = bzla_mem_malloc(mm, strlen(str) + 1);
    strcpy(res, str);
  }
  else
    res = 0;

  return res;
}

void
bzla_mem_freestr(BzlaMemMgr *mm, char *str)
{
  if (str) bzla_mem_free(mm, str, strlen(str) + 1);
}

void
bzla_mem_mgr_delete(BzlaMemMgr *mm)
{
  assert(mm);
  assert(getenv("BZLALEAK") || getenv("BZLALEAKMEM") || !mm->allocated);
  free(mm);
}

size_t
bzla_mem_parse_error_msg_length(const char *name, const char *fmt, va_list ap)
{
  /* Additional characters for:

  "<name>:<lineno>:[<columno>:] "

  */
  size_t bytes = strlen(name) + 25;
  const char *p;

  for (p = fmt; *p; p++)
  {
    if (*p == '%')
    {
      p++;
      assert(*p);
      if (*p == 'c')
      {
        (void) va_arg(ap, int32_t);
        bytes += 1;
      }
      else if (*p == 'd' || *p == 'u')
      {
        (void) va_arg(ap, uint32_t);
        bytes += 12;
      }
      else
      {
        assert(*p == 's');
        bytes += strlen(va_arg(ap, const char *));
      }
    }
    else
      bytes++;
  }

  return bytes;
}

char *
bzla_mem_parse_error_msg(BzlaMemMgr *mem,
                         const char *name,
                         int32_t lineno,
                         int32_t columno,
                         const char *fmt,
                         va_list ap,
                         size_t bytes)
{
  char *res;
  char *tmp;

  tmp = bzla_mem_malloc(mem, bytes);
  if (columno > 0)
    sprintf(tmp, "%s:%d:%d: ", name, lineno, columno);
  else
    sprintf(tmp, "%s:%d: ", name, lineno);
  assert(strlen(tmp) + 1 < bytes);
  vsprintf(tmp + strlen(tmp), fmt, ap);
  res = bzla_mem_strdup(mem, tmp);
  bzla_mem_free(mem, tmp, bytes);

  return res;
}
