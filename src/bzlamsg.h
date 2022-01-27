/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAMSG_H_INCLUDED
#define BZLAMSG_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "bzlaopt.h"
#include "bzlatypes.h"
#include "utils/bzlamem.h"

#define BZLA_MSG(bzlamsg, level, msg...)                                  \
  do                                                                      \
  {                                                                       \
    if (level && bzla_opt_get(bzlamsg->bzla, BZLA_OPT_VERBOSITY) < level) \
      break;                                                              \
    bzla_msg(bzlamsg, false, __FILE__, ##msg);                            \
  } while (0)

typedef struct
{
  Bzla *bzla;
  char *prefix;
} BzlaMsg;

BzlaMsg *bzla_msg_new(Bzla *bzla);

void bzla_msg_delete(BzlaMsg *msg);

void bzla_msg(
    BzlaMsg *msg, bool log, const char *filename, const char *fmt, ...);

#endif
