/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#ifndef BZLAPARSE_H_INCLUDED
#define BZLAPARSE_H_INCLUDED

#include <stdio.h>

#include "api/c/bitwuzla.h"
#include "bzlamsg.h"
#include "utils/bzlastack.h"

/*------------------------------------------------------------------------*/

typedef struct BzlaParser BzlaParser;
typedef struct BzlaParseResult BzlaParseResult;
typedef struct BzlaParserAPI BzlaParserAPI;

typedef BzlaParser *(*BzlaInitParser)(Bitwuzla *);

typedef void (*BzlaResetParser)(void *);

typedef char *(*BzlaParse)(BzlaParser *,
                           BzlaIntStack *prefix,
                           FILE *,
                           const char *,
                           FILE *,
                           BzlaParseResult *);

struct BzlaParseResult
{
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

int32_t bzla_parse(Bitwuzla *bitwuzla,
                   FILE *infile,
                   const char *infile_name,
                   FILE *outfile,
                   char **error_msg,
                   BitwuzlaResult *status,
                   bool *parsed_smt2);

int32_t bzla_parse_btor(Bitwuzla *bitwuzla,
                        FILE *infile,
                        const char *infile_name,
                        FILE *outfile,
                        char **error_msg,
                        BitwuzlaResult *status);

int32_t bzla_parse_btor2(Bitwuzla *bitwuzla,
                         FILE *infile,
                         const char *infile_name,
                         FILE *outfile,
                         char **error_msg,
                         BitwuzlaResult *status);

int32_t bzla_parse_smt2(Bitwuzla *bitwuzla,
                        FILE *infile,
                        const char *infile_name,
                        FILE *outfile,
                        char **error_msg,
                        BitwuzlaResult *status);

BzlaMsg *bitwuzla_get_bzla_msg(Bitwuzla *bitwuzla);
#endif
