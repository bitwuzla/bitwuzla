/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "utils/bzlaabort.h"

#include <assert.h>
#include <stdio.h>

#include "bzlaexit.h"
#include "bzlatypes.h"
#include "utils/bzlamem.h"

#define BUFFER_LEN 255

void
bzla_abort_fun(const char *msg)
{
  fflush(stdout);
  fflush(stderr);
  fprintf(stderr, "%s", msg);
  fflush(stderr);
  exit(BZLA_ERR_EXIT);
}

void
bzla_abort_warn(
    bool abort, const char *filename, const char *fun, const char *fmt, ...)
{
  size_t i;
  const char *warning = "WARNING: ";
  char *s, *e, *p;
  /* do not allocate on heap, since in case of an abort due to mem out heap
   * allocation might fail */
  char buffer[BUFFER_LEN];
  va_list list;

  e = strrchr(filename, '.');
  s = strrchr(filename, '/');
  s = s ? s + 1 : (char *) filename;

  i           = 0;
  buffer[i++] = '[';
  for (p = s; p < e && i < BUFFER_LEN; p++) buffer[i++] = *p;

  assert(i <= BUFFER_LEN);
  i += snprintf(buffer + i, BUFFER_LEN - i, "] %s: ", fun);

  if (!abort)
  {
    assert(i <= BUFFER_LEN);
    i += snprintf(buffer + i, BUFFER_LEN - i, "%s", warning);
  }
  va_start(list, fmt);
  assert(i <= BUFFER_LEN);
  i += vsnprintf(buffer + i, BUFFER_LEN - i, fmt, list);
  va_end(list);

  assert(i <= BUFFER_LEN);
  snprintf(buffer + i, BUFFER_LEN - i, "\n");
  if (abort)
  {
    bzla_abort_callback.abort_fun(buffer);
  }
  else
  {
    fflush(stdout);
    fflush(stderr);
    fprintf(stderr, "%s\n", buffer);
    fflush(stderr);
  }
}
