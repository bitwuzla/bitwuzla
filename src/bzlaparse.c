/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaparse.h"

#include <ctype.h>

#include "bzlacore.h"
#include "bzlaopt.h"
#include "parser/bzlabtor.h"
#include "parser/bzlabtor2.h"
#include "parser/bzlasmt2.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"

static bool
has_compressed_suffix(const char *str, const char *suffix)
{
  int32_t l = strlen(str), k = strlen(suffix), d = l - k;
  if (d < 0) return 0;
  if (!strcmp(str + d, suffix)) return 1;
  if (d - 3 >= 0 && !strcmp(str + l - 3, ".gz") && !strcmp(str + l - 3, ".7z")
      && !strncmp(str + d - 3, suffix, k))
    return 1;
  return 0;
}

/* return BITWUZLA_(SAT|UNSAT|UNKNOWN|PARSE_ERROR) */
static int32_t
parse_aux(Bitwuzla *bitwuzla,
          FILE *infile,
          BzlaIntStack *prefix,
          const char *infile_name,
          FILE *outfile,
          const BzlaParserAPI *parser_api,
          char **error_msg,
          BitwuzlaResult *status,
          char *msg)
{
  assert(bitwuzla);
  assert(infile);
  assert(infile_name);
  assert(outfile);
  assert(parser_api);
  assert(error_msg);
  assert(status);

  BzlaParser *parser;
  BzlaParseResult parse_res;
  int32_t res;

  BzlaMsg *bmsg = bitwuzla_get_bzla_msg(bitwuzla);

  res        = BITWUZLA_UNKNOWN;
  *error_msg = 0;

  BZLA_MSG(bmsg, 1, "%s", msg);
  parser = parser_api->init(bitwuzla);

  *error_msg = parser_api->parse(
      parser, prefix, infile, infile_name, outfile, &parse_res);

  if (*error_msg)
  {
    /* duplicate, string returned by parser_api->parse is freed on reset */
    *error_msg = strdup(*error_msg);
  }
  else
  {
    res = parse_res.result;

    if (parse_res.logic == BZLA_LOGIC_QF_BV)
    {
      BZLA_MSG(bmsg, 1, "logic QF_BV");
    }
    else if (parse_res.logic == BZLA_LOGIC_BV)
    {
      BZLA_MSG(bmsg, 1, "logic BV");
    }
    else if (parse_res.logic == BZLA_LOGIC_UFBV)
    {
      BZLA_MSG(bmsg, 1, "logic UFBV");
    }
    else if (parse_res.logic == BZLA_LOGIC_FP)
    {
      BZLA_MSG(bmsg, 1, "logic FP");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_UFBV)
    {
      BZLA_MSG(bmsg, 1, "logic QF_UFBV");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_ABV)
    {
      BZLA_MSG(bmsg, 1, "logic QF_ABV");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_ABVFP)
    {
      BZLA_MSG(bmsg, 1, "logic QF_ABVFP");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_ABVFPLRA)
    {
      BZLA_MSG(bmsg, 1, "logic QF_ABVFPLRA");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_AUFBVFP)
    {
      BZLA_MSG(bmsg, 1, "logic QF_AUFBVFP");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_FP)
    {
      BZLA_MSG(bmsg, 1, "logic QF_FP");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_BVFP)
    {
      BZLA_MSG(bmsg, 1, "logic QF_BVFP");
    }
    else if (parse_res.logic == BZLA_LOGIC_QF_UFFP)
    {
      BZLA_MSG(bmsg, 1, "logic QF_UFFP");
    }
    else
    {
      assert(parse_res.logic == BZLA_LOGIC_QF_AUFBV);
      BZLA_MSG(bmsg, 1, "logic QF_AUFBV");
    }

    if (parse_res.status == BITWUZLA_SAT)
    {
      BZLA_MSG(bmsg, 1, "status sat");
    }
    else if (parse_res.status == BITWUZLA_UNSAT)
    {
      BZLA_MSG(bmsg, 1, "status unsat");
    }
    else
    {
      assert(parse_res.status == BITWUZLA_UNKNOWN);
      BZLA_MSG(bmsg, 1, "status unknown");
    }
  }

  if (status) *status = parse_res.status;

  /* cleanup */
  parser_api->reset(parser);

  return res;
}

int32_t
bzla_parse(Bitwuzla *bitwuzla,
           FILE *infile,
           const char *infile_name,
           FILE *outfile,
           char **error_msg,
           BitwuzlaResult *status,
           bool *parsed_smt2)
{
  assert(bitwuzla);
  assert(infile);
  assert(infile_name);
  assert(outfile);
  assert(error_msg);
  assert(status);
  assert(parsed_smt2);

  const BzlaParserAPI *parser_api;
  int32_t idx, first, second, res, ch;
  uint32_t len;
  char *msg;
  BzlaIntStack prefix;

  BzlaMemMgr *mem = bzla_mem_mgr_new();

  idx = 0;
  len = 40 + strlen(infile_name);
  BZLA_NEWN(mem, msg, len);
  BZLA_INIT_STACK(mem, prefix);
  *parsed_smt2 = false;

  if (has_compressed_suffix(infile_name, ".bitwuzla"))
  {
    parser_api = bzla_parsebzla_parser_api();
    sprintf(msg, "parsing '%s'", infile_name);
  }
  if (has_compressed_suffix(infile_name, ".btor2"))
  {
    parser_api = bzla_parsebtor2_parser_api();
    sprintf(msg, "parsing '%s'", infile_name);
  }
  else if (has_compressed_suffix(infile_name, ".smt2"))
  {
    parser_api = bzla_parsesmt2_parser_api();
    sprintf(msg, "parsing '%s'", infile_name);
    *parsed_smt2 = true;
  }
  else
  {
    first = second = 0;
    parser_api     = bzla_parsebzla_parser_api();
    sprintf(msg, "assuming BTOR input, parsing '%s'", infile_name);
    for (;;)
    {
      ch = getc(infile);
      BZLA_PUSH_STACK(prefix, ch);
      if (!ch || ch == EOF) break;
      if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n')
      {
        BZLA_PUSH_STACK(prefix, ch);
      }
      else if (ch == ';')
      {
        BZLA_PUSH_STACK(prefix, ';');
        do
        {
          ch = getc(infile);
          if (ch == EOF) break;
          BZLA_PUSH_STACK(prefix, ch);
        } while (ch != '\n');
        if (ch == EOF) break;
      }
      else if (!first)
      {
        first = ch;
        idx   = BZLA_COUNT_STACK(prefix) - 1;
      }
      else
      {
        second = ch;
        break;
      }
    }

    if (ch != EOF && ch)
    {
      assert(first && second);
      if (first == '(')
      {
        parser_api   = bzla_parsesmt2_parser_api();
        *parsed_smt2 = true;
        sprintf(msg, "assuming SMT-LIB v2 input,  parsing '%s'", infile_name);
      }
      else
      {
        do
        {
          ch = getc(infile);
          if (ch == EOF) break;
          BZLA_PUSH_STACK(prefix, ch);
        } while (ch != '\n');
        for (size_t i = idx; i < BZLA_COUNT_STACK(prefix); ++i)
        {
          /* check if input is BTOR2 */
          if (i < BZLA_COUNT_STACK(prefix) - 6)
          {
            if (BZLA_PEEK_STACK(prefix, i) == ' '
                && BZLA_PEEK_STACK(prefix, i + 1) == 's'
                && BZLA_PEEK_STACK(prefix, i + 2) == 'o'
                && BZLA_PEEK_STACK(prefix, i + 3) == 'r'
                && BZLA_PEEK_STACK(prefix, i + 4) == 't'
                && BZLA_PEEK_STACK(prefix, i + 5) == ' ')
            {
              parser_api = bzla_parsebtor2_parser_api();
              sprintf(msg, "assuming BTOR2 input,  parsing '%s'", infile_name);
            }
          }
        }
      }
    }
  }

  res = parse_aux(bitwuzla,
                  infile,
                  &prefix,
                  infile_name,
                  outfile,
                  parser_api,
                  error_msg,
                  status,
                  msg);

  /* cleanup */
  BZLA_RELEASE_STACK(prefix);
  BZLA_DELETEN(mem, msg, len);
  bzla_mem_mgr_delete(mem);

  return res;
}

int32_t
bzla_parse_btor(Bitwuzla *bitwuzla,
                FILE *infile,
                const char *infile_name,
                FILE *outfile,
                char **error_msg,
                BitwuzlaResult *status)
{
  assert(bitwuzla);
  assert(infile);
  assert(infile_name);
  assert(outfile);
  assert(error_msg);
  assert(status);

  const BzlaParserAPI *parser_api;
  parser_api = bzla_parsebzla_parser_api();
  return parse_aux(bitwuzla,
                   infile,
                   0,
                   infile_name,
                   outfile,
                   parser_api,
                   error_msg,
                   status,
                   0);
}

int32_t
bzla_parse_btor2(Bitwuzla *bitwuzla,
                 FILE *infile,
                 const char *infile_name,
                 FILE *outfile,
                 char **error_msg,
                 BitwuzlaResult *status)
{
  assert(bitwuzla);
  assert(infile);
  assert(infile_name);
  assert(outfile);
  assert(error_msg);
  assert(status);

  const BzlaParserAPI *parser_api;
  parser_api = bzla_parsebtor2_parser_api();
  return parse_aux(bitwuzla,
                   infile,
                   0,
                   infile_name,
                   outfile,
                   parser_api,
                   error_msg,
                   status,
                   0);
}

int32_t
bzla_parse_smt2(Bitwuzla *bitwuzla,
                FILE *infile,
                const char *infile_name,
                FILE *outfile,
                char **error_msg,
                BitwuzlaResult *status)
{
  assert(bitwuzla);
  assert(infile);
  assert(infile_name);
  assert(outfile);
  assert(error_msg);
  assert(status);

  const BzlaParserAPI *parser_api;
  parser_api = bzla_parsesmt2_parser_api();
  return parse_aux(bitwuzla,
                   infile,
                   0,
                   infile_name,
                   outfile,
                   parser_api,
                   error_msg,
                   status,
                   0);
}
