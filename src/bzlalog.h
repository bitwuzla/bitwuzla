/*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2012 Armin Biere.
 *  Copyright (C) 2013-2017 Aina Niemetz.
 *  Copyright (C) 2014-2015 Mathias Preiner.
 *
 *  This file is part of Bitwuzla.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLALOG_H_INCLUDED
#define BZLALOG_H_INCLUDED

#include "bzlacore.h"
#include "bzlamsg.h"
#include "bzlaopt.h"

/*------------------------------------------------------------------------*/
#ifndef NBZLALOG
/*------------------------------------------------------------------------*/

#define BZLALOG(LEVEL, FMT, ARGS...)                          \
  do                                                          \
  {                                                           \
    if (bzla_opt_get(bzla, BZLA_OPT_LOGLEVEL) < LEVEL) break; \
    bzla_msg(bzla->msg, true, __FILE__, FMT, ##ARGS);         \
  } while (0)

#define BZLALOG_TIMESTAMP(start)    \
  do                                \
  {                                 \
    start = bzla_util_time_stamp(); \
  } while (0)

/*------------------------------------------------------------------------*/
#else
/*------------------------------------------------------------------------*/

#define BZLALOG(...) \
  do                 \
  {                  \
    (void) bzla;     \
  } while (0)
#define BZLALOG_TIMESTAMP(start) \
  do                             \
  {                              \
    (void) start;                \
  } while (0)

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#endif
