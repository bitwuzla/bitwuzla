/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlamsg.h"

#include <stdio.h>

#include "assert.h"
#include "bzlacore.h"

BzlaMsg *
bzla_msg_new(Bzla *bzla)
{
  assert(bzla);

  BzlaMsg *res;

  BZLA_CNEW(bzla->mm, res);
  res->bzla = bzla;
  return res;
}

void
bzla_msg_delete(BzlaMsg *msg)
{
  assert(msg);

  bzla_mem_freestr(msg->bzla->mm, msg->prefix);
  BZLA_DELETE(msg->bzla->mm, msg);
}

void
bzla_msg(BzlaMsg *msg, bool log, const char *filename, const char *fmt, ...)
{
  va_list ap;
  char *path, *fname, *c, *p;
  uint32_t len;

  len = strlen(filename) + 1;
  BZLA_NEWN(msg->bzla->mm, path, len);
  strcpy(path, filename);
  /* cut-off file extension */
  if ((c = strrchr(path, '.'))) *c = 0;
  fname = strrchr(path, '/');
  if (!fname)
    fname = path;
  else
    fname += 1;

  fputs("[", stdout);
  if (log) fputs("log:", stdout);
  if (msg->prefix) fprintf(stdout, "%s>", msg->prefix);
  p = path;
  while ((c = strchr(p, '/')))
  {
    *c = 0;
    /* print at most 4 chars per directory */
    if (c - p > 4)
    {
      p[4] = 0;
      fprintf(stdout, "%s>", p);
    }
    p = c;
  }
  /* cut-off bzla prefix from file name */
  fputs(fname + 4, stdout);
  fputs("] ", stdout);
  BZLA_DELETEN(msg->bzla->mm, path, len);
  va_start(ap, fmt);
  vfprintf(stdout, fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}
