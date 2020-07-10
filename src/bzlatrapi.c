/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2013-2018 Aina Niemetz.
 *  Copyright (C) 2013-2014 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#include "bzlatrapi.h"

void
bzla_trapi_print(Bzla *bzla, const char *msg, ...)
{
  assert(bzla);
  assert(bzla->apitrace);

  va_list args;
  va_start(args, msg);
  vfprintf(bzla->apitrace, msg, args);
  va_end(args);
  fflush(bzla->apitrace);
}

void
bzla_trapi(Bzla *bzla, const char *fname, const char *msg, ...)
{
  assert(bzla);
  assert(bzla->apitrace);

  va_list args;

  if (fname)
  {
    /* skip boolector_ prefix */
    fprintf(bzla->apitrace, "%s", fname + 10);
    /* skip functions that do not have 'bzla' as argument */
    if (strcmp(fname, "boolector_new") && strcmp(fname, "boolector_get_btor"))
      fprintf(bzla->apitrace, " %p", bzla);
  }
  else
    fputs("return", bzla->apitrace);

  if (strlen(msg) > 0) fputc(' ', bzla->apitrace);

  va_start(args, msg);
  vfprintf(bzla->apitrace, msg, args);
  va_end(args);
  fputc('\n', bzla->apitrace);
  fflush(bzla->apitrace);
}

void
bzla_trapi_open_trace(Bzla *bzla, const char *name)
{
  assert(bzla);
  assert(name);

  FILE *file;
  char *cmd;
  uint32_t len = strlen(name);

  if (len >= 3 && !strcmp(name + len - 3, ".gz"))
  {
    len += 20;
    BZLA_NEWN(bzla->mm, cmd, len);
    sprintf(cmd, "gzip -c > %s", name);
    if ((file = popen(cmd, "w"))) bzla->close_apitrace = 2;
    BZLA_DELETEN(bzla->mm, cmd, len);
  }
  else
  {
    if ((file = fopen(name, "w"))) bzla->close_apitrace = 1;
  }

  if (file)
    bzla->apitrace = file;
  else
    printf("[boolector] WARNING failed to write API trace file to '%s'", name);
}
