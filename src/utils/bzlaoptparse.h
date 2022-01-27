/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAOPTPARSE_H_INCLUDED
#define BZLAOPTPARSE_H_INCLUDED

#include <stdbool.h>

#include "bzlaopt.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

enum BzlaArgRead
{
  BZLA_ARG_READ_NONE,
  BZLA_ARG_READ_NONE_VIA_EQ,
  BZLA_ARG_READ_STR,
  BZLA_ARG_READ_STR_VIA_EQ,
  BZLA_ARG_READ_INT,
  BZLA_ARG_READ_INT_VIA_EQ,
};
typedef enum BzlaArgRead BzlaArgRead;

enum BzlaArgExpected
{
  BZLA_ARG_EXPECT_NONE,
  BZLA_ARG_EXPECT_INT,
  BZLA_ARG_EXPECT_STR,
};
typedef enum BzlaArgExpected BzlaArgExpected;

/*------------------------------------------------------------------------*/

#define BZLA_ARG_READ_NO_VALUE(val) \
  (val == BZLA_ARG_READ_NONE || val == BZLA_ARG_READ_NONE_VIA_EQ)

#define BZLA_ARG_READ_IS_INT(val) \
  (val == BZLA_ARG_READ_INT || val == BZLA_ARG_READ_INT_VIA_EQ)

#define BZLA_ARG_IS_UNEXPECTED(arg, readval, isdisable)                       \
  ((arg == BZLA_ARG_EXPECT_NONE || (arg == BZLA_ARG_EXPECT_INT && isdisable)) \
   && (readval == BZLA_ARG_READ_STR_VIA_EQ                                    \
       || readval == BZLA_ARG_READ_INT_VIA_EQ                                 \
       || readval == BZLA_ARG_READ_INT))

#define BZLA_ARG_IS_MISSING(arg, candisable, readval)              \
  ((arg == BZLA_ARG_EXPECT_STR && BZLA_ARG_READ_NO_VALUE(readval)) \
   || (arg == BZLA_ARG_EXPECT_INT                                  \
       && (((!candisable                                           \
             && (BZLA_ARG_READ_NO_VALUE(readval)                   \
                 || !BZLA_ARG_READ_IS_INT(readval))))              \
           || (readval == BZLA_ARG_READ_NONE_VIA_EQ))))

#define BZLA_ARG_IS_INVALID(arg, candisable, readval) \
  (arg == BZLA_ARG_EXPECT_INT && readval == BZLA_ARG_READ_STR_VIA_EQ)

/*------------------------------------------------------------------------*/

struct BzlaParsedOpt
{
  BzlaMemMgr *mm;
  BzlaCharStack orig;  /* original option string without argument */
  BzlaCharStack name;  /* option name */
  uint32_t val;        /* option value (0 if not given) */
  char *valstr;        /* original option value string (0 if not given) */
  bool isshrt;         /* is short option? */
  bool isdisable;      /* is --no-* option? (disabling option) */
  BzlaArgRead readval; /* how did we read the passed option value? */
};
typedef struct BzlaParsedOpt BzlaParsedOpt;

BZLA_DECLARE_STACK(BzlaParsedOptPtr, BzlaParsedOpt *);

struct BzlaParsedInput
{
  BzlaMemMgr *mm;
  char *name;
};
typedef struct BzlaParsedInput BzlaParsedInput;

BZLA_DECLARE_STACK(BzlaParsedInputPtr, BzlaParsedInput *);

/*------------------------------------------------------------------------*/

void bzla_optparse_parse(BzlaMemMgr *mm,
                         int32_t argc,
                         char **argv,
                         BzlaParsedOptPtrStack *opts,
                         BzlaParsedInputPtrStack *infiles,
                         BzlaOpt *bzla_options,
                         bool (*has_str_arg)(const char *, BzlaOpt *));

#endif
