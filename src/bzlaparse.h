/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2009 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2013-2020 Mathias Preiner.
 *  Copyright (C) 2015-2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#ifndef BZLAPARSE_H_INCLUDED
#define BZLAPARSE_H_INCLUDED

#include <stdio.h>

#include "boolector.h"
#include "bzlalogic.h"
#include "bzlamsg.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaParser BzlaParser;
typedef struct BzlaParseResult BzlaParseResult;
typedef struct BzlaParserAPI BzlaParserAPI;

typedef BzlaParser *(*BzlaInitParser)(Bzla *);

typedef void (*BzlaResetParser)(void *);

typedef char *(*BzlaParse)(BzlaParser *,
                           BzlaCharStack *prefix,
                           FILE *,
                           const char *,
                           FILE *,
                           BzlaParseResult *);

struct BzlaParseResult
{
  BzlaLogic logic;
  int32_t status;
  int32_t result;
  uint32_t nsatcalls;
};

struct BzlaParserAPI
{
  BzlaInitParser init;
  BzlaResetParser reset;
  BzlaParse parse;
};

int32_t bzla_parse(Bzla *bzla,
                   FILE *infile,
                   const char *infile_name,
                   FILE *outfile,
                   char **error_msg,
                   int32_t *status,
                   bool *parsed_smt2);

int32_t bzla_parse_btor(Bzla *bzla,
                        FILE *infile,
                        const char *infile_name,
                        FILE *outfile,
                        char **error_msg,
                        int32_t *status);

int32_t bzla_parse_btor2(Bzla *bzla,
                         FILE *infile,
                         const char *infile_name,
                         FILE *outfile,
                         char **error_msg,
                         int32_t *status);

int32_t bzla_parse_smt1(Bzla *bzla,
                        FILE *infile,
                        const char *infile_name,
                        FILE *outfile,
                        char **error_msg,
                        int32_t *status);

int32_t bzla_parse_smt2(Bzla *bzla,
                        FILE *infile,
                        const char *infile_name,
                        FILE *outfile,
                        char **error_msg,
                        int32_t *status);

BzlaMsg *boolector_get_bzla_msg(Bzla *bzla);
#endif
