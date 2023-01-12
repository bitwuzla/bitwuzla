/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

extern "C" {
#include "bzlabtor.h"

#include "bzlaparse.h"
}

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

/*------------------------------------------------------------------------*/

typedef struct BzlaBTORParser BzlaBTORParser;

typedef BitwuzlaTerm (*BzlaOpParser)(BzlaBTORParser *, uint64_t width);

typedef struct Info Info;

struct Info
{
  uint32_t var : 1;
  uint32_t array : 1;
};

struct BzlaBTORParser
{
  BitwuzlaOptions *options;
  Bitwuzla *bitwuzla;

  // uint32_t nprefix;
  // BzlaIntStack *prefix;
  FILE *infile;
  const char *infile_name;
  uint32_t lineno;
  bool saved;
  int32_t saved_char;
  std::string error;

  std::vector<BitwuzlaTerm> exps;
  std::vector<Info> info;

  std::vector<BitwuzlaTerm> regs;
  std::vector<BitwuzlaTerm> lambdas;
  std::vector<BitwuzlaTerm> params;

  std::unordered_map<std::string, BzlaOpParser> parsers;

  uint64_t idx;
};

static Bitwuzla *
get_bitwuzla(BzlaBTORParser *parser)
{
  if (!parser->bitwuzla)
  {
    assert(parser->options);
    parser->bitwuzla = bitwuzla_new(parser->options);
  }
  return parser->bitwuzla;
}

/** Convert Boolean Term to bit-vector term of size 1. */
static BitwuzlaTerm
bool_term_to_bv(BitwuzlaTerm term)
{
  if (!bitwuzla_term_is_bool(term)) return term;
  BitwuzlaSort bv1 = bitwuzla_mk_bv_sort(1);
  return bitwuzla_mk_term3(BITWUZLA_KIND_ITE,
                           term,
                           bitwuzla_mk_bv_one(bv1),
                           bitwuzla_mk_bv_zero(bv1));
}
static BitwuzlaTerm
bv_term_to_bool(BitwuzlaTerm term)
{
  if (!bitwuzla_term_is_bv(term) || bitwuzla_term_bv_get_size(term) != 1)
  {
    return term;
  }
  return bitwuzla_mk_term2(
      BITWUZLA_KIND_EQUAL, term, bitwuzla_mk_bv_one(bitwuzla_mk_bv_sort(1)));
}

static BitwuzlaTerm
mk_term(BitwuzlaKind kind,
        const std::vector<BitwuzlaTerm> &args,
        const std::vector<uint64_t> &idxs = {})
{
  switch (kind)
  {
    case BITWUZLA_KIND_AND:
    case BITWUZLA_KIND_IFF:
    case BITWUZLA_KIND_IMPLIES:
    case BITWUZLA_KIND_OR:
    case BITWUZLA_KIND_XOR:
      assert(args.size() == 2);
      return bitwuzla_mk_term2(
          kind, bv_term_to_bool(args[0]), bv_term_to_bool(args[1]));

    case BITWUZLA_KIND_NOT:
      assert(args.size() == 1);
      return bitwuzla_mk_term1(kind, bv_term_to_bool(args[0]));

    case BITWUZLA_KIND_DISTINCT:
    case BITWUZLA_KIND_EQUAL:
      assert(args.size() == 2);
      return bitwuzla_mk_term2(
          kind, bv_term_to_bool(args[0]), bv_term_to_bool(args[1]));

    case BITWUZLA_KIND_ITE:
      assert(args.size() == 3);
      return bitwuzla_mk_term3(kind,
                               bv_term_to_bool(args[0]),
                               bv_term_to_bool(args[1]),
                               bv_term_to_bool(args[2]));

    case BITWUZLA_KIND_LAMBDA:
    case BITWUZLA_KIND_APPLY: {
      std::vector<BitwuzlaTerm> cargs;
      for (BitwuzlaTerm t : args)
      {
        cargs.push_back(bool_term_to_bv(t));
      }
      return bitwuzla_mk_term(kind, cargs.size(), cargs.data());
    }

    case BITWUZLA_KIND_ARRAY_SELECT:
      assert(args.size() == 2);
      return bitwuzla_mk_term2(kind, args[0], bool_term_to_bv(args[1]));

    case BITWUZLA_KIND_ARRAY_STORE:
      assert(args.size() == 3);
      return bitwuzla_mk_term3(
          kind, args[0], bool_term_to_bv(args[1]), bool_term_to_bv(args[2]));

    case BITWUZLA_KIND_BV_ADD:
    case BITWUZLA_KIND_BV_AND:
    case BITWUZLA_KIND_BV_ASHR:
    case BITWUZLA_KIND_BV_COMP:
    case BITWUZLA_KIND_BV_CONCAT:
    case BITWUZLA_KIND_BV_MUL:
    case BITWUZLA_KIND_BV_NAND:
    case BITWUZLA_KIND_BV_NOR:
    case BITWUZLA_KIND_BV_OR:
    case BITWUZLA_KIND_BV_ROL:
    case BITWUZLA_KIND_BV_ROR:
    case BITWUZLA_KIND_BV_SDIV:
    case BITWUZLA_KIND_BV_SGE:
    case BITWUZLA_KIND_BV_SGT:
    case BITWUZLA_KIND_BV_SHL:
    case BITWUZLA_KIND_BV_SHR:
    case BITWUZLA_KIND_BV_SLE:
    case BITWUZLA_KIND_BV_SLT:
    case BITWUZLA_KIND_BV_SMOD:
    case BITWUZLA_KIND_BV_SREM:
    case BITWUZLA_KIND_BV_SUB:
    case BITWUZLA_KIND_BV_UDIV:
    case BITWUZLA_KIND_BV_UGE:
    case BITWUZLA_KIND_BV_UGT:
    case BITWUZLA_KIND_BV_ULE:
    case BITWUZLA_KIND_BV_ULT:
    case BITWUZLA_KIND_BV_UREM:
    case BITWUZLA_KIND_BV_XNOR:
    case BITWUZLA_KIND_BV_XOR:
    case BITWUZLA_KIND_BV_SADD_OVERFLOW:
    case BITWUZLA_KIND_BV_SDIV_OVERFLOW:
    case BITWUZLA_KIND_BV_SMUL_OVERFLOW:
    case BITWUZLA_KIND_BV_SSUB_OVERFLOW:
    case BITWUZLA_KIND_BV_UADD_OVERFLOW:
    case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
    case BITWUZLA_KIND_BV_USUB_OVERFLOW:
      assert(args.size() == 2);
      return bitwuzla_mk_term2(
          kind, bool_term_to_bv(args[0]), bool_term_to_bv(args[1]));
    case BITWUZLA_KIND_BV_DEC:
    case BITWUZLA_KIND_BV_INC:
    case BITWUZLA_KIND_BV_NEG:
    case BITWUZLA_KIND_BV_NOT:
    case BITWUZLA_KIND_BV_REDAND:
    case BITWUZLA_KIND_BV_REDOR:
    case BITWUZLA_KIND_BV_REDXOR:
      assert(args.size() == 1);
      return bitwuzla_mk_term1(kind, bool_term_to_bv(args[0]));

    case BITWUZLA_KIND_BV_EXTRACT:
    case BITWUZLA_KIND_BV_REPEAT:
    case BITWUZLA_KIND_BV_ROLI:
    case BITWUZLA_KIND_BV_RORI:
    case BITWUZLA_KIND_BV_SIGN_EXTEND:
    case BITWUZLA_KIND_BV_ZERO_EXTEND: {
      assert(args.size() == 1);
      std::vector<BitwuzlaTerm> cargs{bool_term_to_bv(args[0])};
      return bitwuzla_mk_term_indexed(
          kind, cargs.size(), cargs.data(), idxs.size(), idxs.data());
    }

    default: assert(false);
  }
  return 0;
}

static uint64_t
term_get_bv_size(BitwuzlaTerm term)
{
  if (bitwuzla_term_is_bool(term)) return 1;
  assert(bitwuzla_term_is_bv(term));
  return bitwuzla_term_bv_get_size(term);
}

static uint64_t
sort_get_bv_size(BitwuzlaSort sort)
{
  if (bitwuzla_sort_is_bool(sort)) return 1;
  assert(bitwuzla_sort_is_bv(sort));
  return bitwuzla_sort_bv_get_size(sort);
}

/*------------------------------------------------------------------------*/

static std::string
parse_error_msg(BzlaBTORParser *parser, const std::string &msg)
{
  std::stringstream ss;
  ss << parser->infile_name << ":" << parser->lineno << ": " << msg;
  return ss.str();
}

static std::string
perr_btor(BzlaBTORParser *parser, const std::string &msg)
{
  if (parser->error.empty())
  {
    parser->error = parse_error_msg(parser, msg);
  }
  return parser->error;
}

/*------------------------------------------------------------------------*/

static int32_t
nextch_btor(BzlaBTORParser *parser)
{
  int32_t ch;

  if (parser->saved)
  {
    ch            = parser->saved_char;
    parser->saved = false;
  }
  // else if (parser->prefix
  //          && parser->nprefix < BZLA_COUNT_STACK(*parser->prefix))
  //{
  //   ch = parser->prefix->start[parser->nprefix++];
  // }
  else
    ch = getc(parser->infile);

  if (ch == '\n') parser->lineno++;

  return ch;
}

static void
savech_btor(BzlaBTORParser *parser, int32_t ch)
{
  assert(!parser->saved);

  parser->saved_char = ch;
  parser->saved      = true;

  if (ch == '\n')
  {
    assert(parser->lineno > 1);
    parser->lineno--;
  }
}

static std::string
parse_non_negative_int(BzlaBTORParser *parser, uint64_t *res_ptr)
{
  int64_t res;
  int32_t ch;

  ch = nextch_btor(parser);
  if (!isdigit(ch)) return perr_btor(parser, "expected digit");

  if (ch == '0')
  {
    res = 0;
    ch  = nextch_btor(parser);
    if (isdigit(ch)) return perr_btor(parser, "digit after '0'");
  }
  else
  {
    res = ch - '0';

    while (isdigit(ch = nextch_btor(parser))) res = 10 * res + (ch - '0');
  }

  savech_btor(parser, ch);
  *res_ptr = res;

  return "";
}

static std::string
parse_positive_int(BzlaBTORParser *parser, uint64_t *res_ptr)
{
  int64_t res;
  int32_t ch;

  ch = nextch_btor(parser);
  if (!isdigit(ch)) return perr_btor(parser, "expected digit");

  if (ch == '0') return perr_btor(parser, "expected non zero digit");

  res = ch - '0';

  while (isdigit(ch = nextch_btor(parser))) res = 10 * res + (ch - '0');

  savech_btor(parser, ch);
  *res_ptr = res;

  return "";
}

static std::string
parse_non_zero_int(BzlaBTORParser *parser, int32_t *res_ptr)
{
  int32_t res, sign, ch;

  ch = nextch_btor(parser);

  if (ch == '-')
  {
    sign = -1;
    ch   = nextch_btor(parser);

    if (!isdigit(ch) || ch == '0')
      return perr_btor(parser, "expected non zero digit after '-'");
  }
  else
  {
    sign = 1;
    if (!isdigit(ch) || ch == '0')
      return perr_btor(parser, "expected non zero digit or '-'");
  }

  res = ch - '0';

  while (isdigit(ch = nextch_btor(parser))) res = 10 * res + (ch - '0');

  savech_btor(parser, ch);

  res *= sign;
  *res_ptr = res;

  return "";
}

static BitwuzlaTerm
parse_exp(BzlaBTORParser *parser,
          uint64_t expected_width,
          bool can_be_array,
          bool can_be_inverted,
          int32_t *rlit)
{
  size_t idx;
  uint64_t width_res;
  BitwuzlaTerm res;

  int32_t lit         = 0;
  std::string err_msg = parse_non_zero_int(parser, &lit);
  if (!err_msg.empty()) return 0;
  if (rlit) *rlit = lit;

  if (!can_be_inverted && lit < 0)
  {
    (void) perr_btor(parser, "positive literal expected");
    return 0;
  }

  idx = abs(lit);
  assert(idx);

  if (idx >= parser->exps.size() || !(res = parser->exps[idx]))
  {
    (void) perr_btor(parser, "literal '" + std::to_string(lit) + "' undefined");
    return 0;
  }

  // if (bitwuzla_term_is_var(res) && bitwuzla_term_is_bound_var(res))
  //{
  //   (void) perr_btor(
  //       parser, "param '%d' cannot be used outside of its defined scope",
  //       lit);
  //   return 0;
  // }

  if (!can_be_array && bitwuzla_term_is_array(res))
  {
    (void) perr_btor(parser,
                     "literal '" + std::to_string(lit)
                         + "' refers to an unexpected array expression");
    return 0;
  }

  if (expected_width)
  {
    if (bitwuzla_term_is_fun(res))
    {
      BitwuzlaSort sort = bitwuzla_term_fun_get_codomain_sort(res);
      assert(bitwuzla_sort_is_bv(sort));
      width_res = bitwuzla_sort_bv_get_size(sort);
    }
    else if (bitwuzla_term_is_array(res))
    {
      BitwuzlaSort sort = bitwuzla_term_array_get_element_sort(res);
      assert(bitwuzla_sort_is_bv(sort));
      width_res = bitwuzla_sort_bv_get_size(sort);
    }
    else if (bitwuzla_term_is_bool(res))
    {
      width_res = 1;
    }
    else
    {
      assert(bitwuzla_term_is_bv(res));
      width_res = term_get_bv_size(res);
    }

    assert(expected_width == width_res);
    if (expected_width != width_res)
    {
      (void) perr_btor(parser,
                       "literal '" + std::to_string(lit) + "' has width '"
                           + std::to_string(width_res) + "' but expected '"
                           + std::to_string(expected_width) + "'");

      return 0;
    }
  }

  if (lit < 0)
  {
    if (bitwuzla_term_is_bool(res))
    {
      res = mk_term(BITWUZLA_KIND_NOT, {res});
    }
    else
    {
      res = mk_term(BITWUZLA_KIND_BV_NOT, {res});
    }
  }
  return res;
}

static int32_t
parse_space(BzlaBTORParser *parser)
{
  int32_t ch = nextch_btor(parser);
  if (ch != ' ' && ch != '\t')
    return perr_btor(parser, "expected space or tab").empty();

SKIP:
  ch = nextch_btor(parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return perr_btor(parser, "unexpected character").empty();

  savech_btor(parser, ch);

  return 1;
}

static std::pair<std::string, bool>
parse_symbol(BzlaBTORParser *parser)
{
  int32_t ch;

  while ((ch = nextch_btor(parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  {
  UNEXPECTED_EOF:
    (void) perr_btor(parser, "unexpected EOF");
    return std::make_pair("", false);
  }

  std::stringstream symbol;

  if (ch != '\n')
  {
    symbol << static_cast<char>(ch);

    while (!isspace(ch = nextch_btor(parser)))
    {
      if (!isprint(ch)) perr_btor(parser, "invalid character");
      if (ch == EOF) goto UNEXPECTED_EOF;
      symbol << static_cast<char>(ch);
    }
  }

  savech_btor(parser, ch);
  return std::make_pair(symbol.str(), true);
}

static BitwuzlaTerm
parse_var(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res;
  BitwuzlaSort s;

  auto [symbol, success] = parse_symbol(parser);
  if (!success) return 0;

  s = bitwuzla_mk_bv_sort(width);
  res = bitwuzla_mk_const(s, symbol[0] ? symbol.c_str() : 0);
  parser->info[parser->idx].var = 1;
  return res;
}

static BitwuzlaTerm
parse_param(BzlaBTORParser *parser, uint64_t width)
{
  auto [symbol, success] = parse_symbol(parser);
  if (!success) return 0;
  BitwuzlaSort s = bitwuzla_mk_bv_sort(width);
  BitwuzlaTerm res = bitwuzla_mk_var(s, symbol[0] ? symbol.c_str() : 0);
  parser->params.push_back(res);
  return res;
}

static BitwuzlaTerm
parse_param_exp(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res = parse_exp(parser, width, false, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_var(res)) return res;
  (void) perr_btor(parser, "expected parameter");
  return 0;
}

static BitwuzlaTerm
parse_array(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res;
  BitwuzlaSort s, is, es;
  uint64_t idx_width;

  if (!parse_space(parser)) return 0;
  if (!parse_positive_int(parser, &idx_width).empty()) return 0;
  auto [symbol, success] = parse_symbol(parser);
  if (!success) return 0;

  is = bitwuzla_mk_bv_sort(idx_width);
  es = bitwuzla_mk_bv_sort(width);
  s  = bitwuzla_mk_array_sort(is, es);
  res = bitwuzla_mk_const(s, symbol[0] ? symbol.c_str() : 0);
  parser->info[parser->idx].array = 1;
  return res;
}

static BitwuzlaTerm
parse_array_exp(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res = parse_exp(parser, width, true, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_array(res)) return res;
  (void) perr_btor(parser, "expected array expression");
  return 0;
}

static BitwuzlaTerm
parse_fun_exp(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res = parse_exp(parser, width, true, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_fun(res) || bitwuzla_term_is_array(res)) return res;
  (void) perr_btor(parser, "expected function expression");
  return 0;
}

static BitwuzlaTerm
parse_const(BzlaBTORParser *parser, uint64_t width)
{
  int32_t ch;
  uint64_t cwidth;

  if (!parse_space(parser)) return 0;

  std::stringstream constant;

  while (!isspace(ch = nextch_btor(parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) perr_btor(parser, "expected '0' or '1'");
      return 0;
    }

    constant << static_cast<char>(ch);
  }

  savech_btor(parser, ch);
  cwidth = constant.str().size();

  if (cwidth != width)
  {
    (void) perr_btor(parser,
                     "binary constant '" + constant.str()
                         + "' exceeds bit width " + std::to_string(width));
    return 0;
  }

  BitwuzlaSort sort = bitwuzla_mk_bv_sort(width);

  return bitwuzla_mk_bv_value(sort, constant.str().c_str(), 2);
}

static BitwuzlaTerm
parse_consth(BzlaBTORParser *parser, uint64_t width)
{
  int32_t ch;
  BitwuzlaTerm res;

  if (!parse_space(parser)) return 0;

  std::stringstream constant;
  while (!isspace(ch = nextch_btor(parser)) && ch != EOF && ch != ';')
  {
    if (!isxdigit(ch))
    {
      (void) perr_btor(parser, "expected hexidecimal digit");
      return 0;
    }
    constant << static_cast<char>(ch);
  }

  savech_btor(parser, ch);

  BitwuzlaSort sort = bitwuzla_mk_bv_sort(width);
  res               = bitwuzla_mk_bv_value(sort, constant.str().c_str(), 16);

  assert(term_get_bv_size(res) == width);

  return res;
}

static BitwuzlaTerm
parse_constd(BzlaBTORParser *parser, uint64_t width)
{
  int32_t ch;
  BitwuzlaTerm res;

  if (!parse_space(parser)) return 0;

  std::stringstream constant;
  ch = nextch_btor(parser);
  if (!isdigit(ch))
  {
    (void) perr_btor(parser, "expected digit");
    return 0;
  }
  constant << static_cast<char>(ch);

  if (ch == '0')
  {
    ch = nextch_btor(parser);

    if (isdigit(ch))
    {
      (void) perr_btor(parser, "digit after '0'");
      return 0;
    }
  }
  else
  {
    while (isdigit(ch = nextch_btor(parser))) constant << static_cast<char>(ch);
  }

  savech_btor(parser, ch);

  BitwuzlaSort sort = bitwuzla_mk_bv_sort(width);
  res               = bitwuzla_mk_bv_value(sort, constant.str().c_str(), 10);

  assert(term_get_bv_size(res) == width);

  return res;
}

static BitwuzlaTerm
parse_zero(BzlaBTORParser *parser, uint64_t width)
{
  (void) parser;
  BitwuzlaSort s = bitwuzla_mk_bv_sort(width);
  return bitwuzla_mk_bv_zero(s);
}

static BitwuzlaTerm
parse_one(BzlaBTORParser *parser, uint64_t width)
{
  (void) parser;
  BitwuzlaSort s = bitwuzla_mk_bv_sort(width);
  return bitwuzla_mk_bv_one(s);
}

static BitwuzlaTerm
parse_ones(BzlaBTORParser *parser, uint64_t width)
{
  (void) parser;
  BitwuzlaSort s = bitwuzla_mk_bv_sort(width);
  return bitwuzla_mk_bv_ones(s);
}

static BitwuzlaTerm
parse_root(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm res, tmp;

  if (!parse_space(parser)) return 0;
  if (!(res = parse_exp(parser, width, false, true, 0))) return 0;
  if (width > 1)
  {
    tmp = res;
    res = mk_term(BITWUZLA_KIND_BV_REDOR, {tmp});
  }
  bitwuzla_assert(get_bitwuzla(parser), bv_term_to_bool(res));
  return res;
}

static BitwuzlaTerm
parse_unary(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  assert(width);

  BitwuzlaTerm tmp, res;

  if (!parse_space(parser)) return 0;

  if (!(tmp = parse_exp(parser, width, false, true, 0))) return 0;

  res = mk_term(kind, {tmp});
  assert((bitwuzla_term_is_bool(tmp) && bitwuzla_term_is_bool(res))
         || term_get_bv_size(res) == width);

  return res;
}

static BitwuzlaTerm
parse_not(BzlaBTORParser *parser, uint64_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_NOT, width);
}

static BitwuzlaTerm
parse_neg(BzlaBTORParser *parser, uint64_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_NEG, width);
}

static BitwuzlaTerm
parse_inc(BzlaBTORParser *parser, uint64_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_INC, width);
}

static BitwuzlaTerm
parse_dec(BzlaBTORParser *parser, uint64_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_DEC, width);
}

static BitwuzlaTerm
parse_redunary(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  assert(width == 1);

  BitwuzlaTerm tmp, res;

  (void) width;

  if (!parse_space(parser)) return 0;

  if (!(tmp = parse_exp(parser, 0, false, true, 0))) return 0;

  if (term_get_bv_size(tmp) == 1)
  {
    (void) perr_btor(parser, "argument of reduction operation of width 1");
    return 0;
  }

  res = mk_term(kind, {tmp});
  assert(term_get_bv_size(res) == 1);

  return res;
}

static BitwuzlaTerm
parse_redand(BzlaBTORParser *parser, uint64_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDAND, width);
}

static BitwuzlaTerm
parse_redor(BzlaBTORParser *parser, uint64_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDOR, width);
}

static BitwuzlaTerm
parse_redxor(BzlaBTORParser *parser, uint64_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDXOR, width);
}

static BitwuzlaTerm
parse_binary(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  assert(width);

  BitwuzlaTerm l, r, res;

  if (!parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, width, false, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  res = mk_term(kind, {l, r});
  assert(bitwuzla_term_is_bool(res) || term_get_bv_size(res) == width);

  return res;
}

static BitwuzlaTerm
parse_add(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_ADD, width);
}

static BitwuzlaTerm
parse_and(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_AND, width);
}

static BitwuzlaTerm
parse_smod(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SMOD, width);
}

static BitwuzlaTerm
parse_srem(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SREM, width);
}

static BitwuzlaTerm
parse_mul(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_MUL, width);
}

static BitwuzlaTerm
parse_sub(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SUB, width);
}

static BitwuzlaTerm
parse_udiv(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_UDIV, width);
}

static BitwuzlaTerm
parse_urem(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_UREM, width);
}

static BitwuzlaTerm
parse_xor(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_XOR, width);
}

static BitwuzlaTerm
parse_xnor(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_XNOR, width);
}

static BitwuzlaTerm
parse_or(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_OR, width);
}

static BitwuzlaTerm
parse_nor(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_NOR, width);
}

static BitwuzlaTerm
parse_nand(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_NAND, width);
}

static BitwuzlaTerm
parse_sdiv(BzlaBTORParser *parser, uint64_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SDIV, width);
}

static BitwuzlaTerm
parse_logical(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  BitwuzlaTerm l, r, res;

  if (width != 1)
  {
    (void) perr_btor(
        parser, "logical operator bit width '" + std::to_string(width) + "'");
    return 0;
  }

  if (!parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, false, true, 0))) return 0;

  if (term_get_bv_size(l) != 1)
  {
  BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN:
    (void) perr_btor(parser, "expected argument of bit width '1'");
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!parse_space(parser)) goto RELEASE_L_AND_RETURN_ERROR;

  if (!(r = parse_exp(parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  if (term_get_bv_size(r) != 1)
  {
    goto BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN;
  }

  res = mk_term(kind, {l, r});
  assert(bitwuzla_term_is_bool(res));

  return res;
}

static BitwuzlaTerm
parse_implies(BzlaBTORParser *parser, uint64_t width)
{
  return parse_logical(parser, BITWUZLA_KIND_IMPLIES, width);
}

static BitwuzlaTerm
parse_iff(BzlaBTORParser *parser, uint64_t width)
{
  return parse_logical(parser, BITWUZLA_KIND_IFF, width);
}

static BitwuzlaTerm
parse_compare_and_overflow(BzlaBTORParser *parser,
                           BitwuzlaKind kind,
                           uint64_t width,
                           bool can_be_array)
{
  BitwuzlaTerm l, r, res;

  if (width != 1)
  {
    (void) perr_btor(parser,
                     "comparison or overflow operator returns "
                         + std::to_string(width) + "bits");
    return 0;
  }

  if (!parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, can_be_array, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, can_be_array, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  if (!bitwuzla_term_is_equal_sort(bool_term_to_bv(l), bool_term_to_bv(r)))
  {
    (void) perr_btor(parser, "operands have different sort");
  RELEASE_L_AND_R_AND_RETURN_ZERO:
    return 0;
  }

  if (can_be_array)
  {
    if (bitwuzla_term_is_array(l) && !bitwuzla_term_is_array(r))
    {
      (void) perr_btor(parser, "first operand is array and second not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }

    if (!bitwuzla_term_is_array(l) && bitwuzla_term_is_array(r))
    {
      (void) perr_btor(parser, "second operand is array and first not");
      goto RELEASE_L_AND_R_AND_RETURN_ZERO;
    }
  }

  res = mk_term(kind, {l, r});
  assert(bitwuzla_term_is_bool(res));
  return res;
}

static BitwuzlaTerm
parse_eq(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_EQUAL, width, 1);
}

static BitwuzlaTerm
parse_ne(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_DISTINCT, width, 1);
}

static BitwuzlaTerm
parse_sgt(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SGT, width, 0);
}

static BitwuzlaTerm
parse_sgte(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SGE, width, 0);
}

static BitwuzlaTerm
parse_slt(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SLT, width, 0);
}

static BitwuzlaTerm
parse_slte(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SLE, width, 0);
}

static BitwuzlaTerm
parse_ugt(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_UGT, width, 0);
}

static BitwuzlaTerm
parse_ugte(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_UGE, width, 0);
}

static BitwuzlaTerm
parse_ult(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_ULT, width, 0);
}

static BitwuzlaTerm
parse_ulte(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_ULE, width, 0);
}

static BitwuzlaTerm
parse_saddo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SADD_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_ssubo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SSUB_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_smulo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SMUL_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_sdivo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SDIV_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_uaddo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_UADD_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_usubo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_USUB_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_umulo(BzlaBTORParser *parser, uint64_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_UMUL_OVERFLOW, width, 0);
}

static BitwuzlaTerm
parse_concat(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm l, r, res;
  uint64_t lwidth, rwidth;

  if (!parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, false, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  lwidth = term_get_bv_size(l);
  rwidth = term_get_bv_size(r);

  if (lwidth + rwidth != width)
  {
    (void) perr_btor(parser,
                     "operands widths " + std::to_string(lwidth) + " and "
                         + std::to_string(rwidth) + " do not add up to "
                         + std::to_string(width));

    return 0;
  }

  res = mk_term(BITWUZLA_KIND_BV_CONCAT, {l, r});
  assert(term_get_bv_size(res) == width);
  return res;
}

static BitwuzlaTerm
parse_shift(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  BitwuzlaTerm l, r, res, tmp;
  int32_t lit;
  uint64_t rwidth, rw;

  for (rwidth = 1; rwidth <= 30u && width != (1u << rwidth); rwidth++)
    ;

  if (!parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, width, false, true, &lit))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, false, true, &lit)))
    goto RELEASE_L_AND_RETURN_ERROR;

  rw = term_get_bv_size(r);
  if (width != rw)
  {
    tmp = mk_term(BITWUZLA_KIND_BV_ZERO_EXTEND, {r}, {width - rw});
    r   = tmp;
  }
  res = mk_term(kind, {l, r});
  assert(term_get_bv_size(res) == width);
  return res;
}

static BitwuzlaTerm
parse_rol(BzlaBTORParser *parser, uint64_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ROL, width);
}

static BitwuzlaTerm
parse_ror(BzlaBTORParser *parser, uint64_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ROR, width);
}

static BitwuzlaTerm
parse_sll(BzlaBTORParser *parser, uint64_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_SHL, width);
}

static BitwuzlaTerm
parse_sra(BzlaBTORParser *parser, uint64_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ASHR, width);
}

static BitwuzlaTerm
parse_srl(BzlaBTORParser *parser, uint64_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_SHR, width);
}

static BitwuzlaTerm
parse_cond(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm c, t, e;

  if (!parse_space(parser)) return 0;

  if (!(c = parse_exp(parser, 1, false, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    return 0;
  }

  if (!(t = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_C_AND_RETURN_ERROR;

  if (!parse_space(parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  return mk_term(BITWUZLA_KIND_ITE, {c, t, e});
}

static BitwuzlaTerm
parse_acond(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm c, t, e;
  uint64_t idx_size = 0;

  if (!parse_space(parser)) return 0;

  if (!parse_positive_int(parser, &idx_size).empty()) return 0;

  if (!parse_space(parser)) return 0;

  if (!(c = parse_exp(parser, 1, false, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    return 0;
  }

  if (!(t = parse_array_exp(parser, width))) goto RELEASE_C_AND_RETURN_ERROR;

  if (idx_size != sort_get_bv_size(bitwuzla_term_array_get_index_sort(t)))
  {
    (void) perr_btor(parser, "mismatch of index bit width of 'then' array");
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!parse_space(parser)) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (!(e = parse_array_exp(parser, width)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (idx_size != sort_get_bv_size(bitwuzla_term_array_get_index_sort(e)))
  {
    (void) perr_btor(parser, "mismatch of index bit width of 'else' array");
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;
  }

  return mk_term(BITWUZLA_KIND_ITE, {c, t, e});
}

static BitwuzlaTerm
parse_slice(BzlaBTORParser *parser, uint64_t width)
{
  uint64_t argwidth, upper, lower, delta;
  BitwuzlaTerm arg;

  if (!parse_space(parser)) return 0;

  if (!(arg = parse_exp(parser, 0, false, true, 0))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    return 0;
  }

  argwidth = term_get_bv_size(arg);

  if (!parse_non_negative_int(parser, &upper).empty())
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper >= argwidth)
  {
    (void) perr_btor(parser,
                     "upper index '" + std::to_string(upper)
                         + "' >= argument width '" + std::to_string(argwidth));
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (!parse_space(parser)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (!parse_non_negative_int(parser, &lower).empty())
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) perr_btor(parser,
                     "upper index '" + std::to_string(upper)
                         + "' smaller than lower index '"
                         + std::to_string(lower) + "'");
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != width)
  {
    (void) perr_btor(parser,
                     "slice width '" + std::to_string(delta)
                         + "' not equal to expected width '"
                         + std::to_string(width) + "'");
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  return mk_term(BITWUZLA_KIND_BV_EXTRACT, {arg}, {upper, lower});
}

static BitwuzlaTerm
parse_read(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm array, idx;
  uint64_t idxwidth;

  if (!parse_space(parser)) return 0;

  if (!(array = parse_array_exp(parser, width))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    return 0;
  }

  idxwidth =
      bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_index_sort(array));
  if (!(idx = parse_exp(parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  return mk_term(BITWUZLA_KIND_ARRAY_SELECT, {array, idx});
}

static BitwuzlaTerm
parse_write(BzlaBTORParser *parser, uint64_t width)
{
  BitwuzlaTerm array, idx, val;
  uint64_t idxwidth, valwidth;

  idxwidth = 0;

  if (!parse_space(parser)) return 0;

  if (!parse_positive_int(parser, &idxwidth).empty()) return 0;

  if (!parse_space(parser)) return 0;

  if (!(array = parse_array_exp(parser, width))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    return 0;
  }

  if (!(idx = parse_exp(parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  if (!parse_space(parser))
  {
  RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR:
    goto RELEASE_ARRAY_AND_RETURN_ERROR;
  }

  valwidth =
      bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_element_sort(array));
  if (!(val = parse_exp(parser, valwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR;

  return mk_term(BITWUZLA_KIND_ARRAY_STORE, {array, idx, val});
}

static BitwuzlaTerm
parse_lambda(BzlaBTORParser *parser, uint64_t width)
{
  uint64_t paramwidth;
  std::vector<BitwuzlaTerm> args;
  BitwuzlaTerm exp, res;

  paramwidth = 0;

  if (!parse_space(parser)) return 0;

  if (!parse_positive_int(parser, &paramwidth).empty()) return 0;

  if (!parse_space(parser)) return 0;

  args.push_back(parse_param_exp(parser, paramwidth));
  if (args[0] == 0) return 0;

  // if (bitwuzla_term_is_bound_var(args[0]))
  //{
  //   perr_btor(parser, "param already bound by other lambda");
  //   goto RELEASE_PARAM_AND_RETURN_ERROR;
  // }

  if (!parse_space(parser))
  {
  RELEASE_PARAM_AND_RETURN_ERROR:
    return 0;
  }

  if (!(exp = parse_exp(parser, width, true, true, 0)))
    goto RELEASE_PARAM_AND_RETURN_ERROR;
  args.push_back(exp);

  res = mk_term(BITWUZLA_KIND_LAMBDA, {args[0], args[1]});

  parser->lambdas.push_back(res);
  return res;
}

static BitwuzlaTerm
parse_apply(BzlaBTORParser *parser, uint64_t width)
{
  uint64_t i, arity;
  BitwuzlaTerm res, fun, arg;
  std::vector<BitwuzlaTerm> args;

  if (!parse_space(parser)) return 0;

  if (!(fun = parse_fun_exp(parser, width))) return 0;

  if (!parse_space(parser))
  {
  RELEASE_FUN_AND_RETURN_ERROR:
    return 0;
  }

  arity = bitwuzla_sort_fun_get_arity(bitwuzla_term_get_sort(fun));
  args.push_back(fun);
  for (i = 0; i < arity; i++)
  {
    arg = parse_exp(parser, 0, false, true, 0);
    if (!arg) goto RELEASE_FUN_AND_RETURN_ERROR;

    if (i < arity - 1)
      if (!parse_space(parser)) goto RELEASE_FUN_AND_RETURN_ERROR;

    args.push_back(arg);
  }

  res = mk_term(BITWUZLA_KIND_APPLY, args);
  return res;
}

static BitwuzlaTerm
parse_ext(BzlaBTORParser *parser, BitwuzlaKind kind, uint64_t width)
{
  BitwuzlaTerm res, arg;
  uint64_t awidth, ewidth;

  if (!parse_space(parser)) return 0;

  if (!(arg = parse_exp(parser, 0, false, true, 0))) return 0;

  awidth = term_get_bv_size(arg);

  if (!parse_space(parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    return 0;
  }

  if (!parse_non_negative_int(parser, &ewidth).empty())
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (awidth + ewidth != width)
  {
    (void) perr_btor(parser,
                     "argument width of " + std::to_string(awidth) + " plus "
                         + std::to_string(ewidth) + " does not match "
                         + std::to_string(width));
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = mk_term(kind, {arg}, {ewidth});
  assert(term_get_bv_size(res) == width);
  return res;
}

static BitwuzlaTerm
parse_sext(BzlaBTORParser *parser, uint64_t width)
{
  return parse_ext(parser, BITWUZLA_KIND_BV_SIGN_EXTEND, width);
}

static BitwuzlaTerm
parse_uext(BzlaBTORParser *parser, uint64_t width)
{
  return parse_ext(parser, BITWUZLA_KIND_BV_ZERO_EXTEND, width);
}

static BzlaBTORParser *
new_btor_parser(BitwuzlaOptions *options)
{
  BzlaBTORParser *res = new BzlaBTORParser();

  res->options = options;

  res->parsers.emplace("add", parse_add);
  res->parsers.emplace("and", parse_and);
  res->parsers.emplace("array", parse_array);
  res->parsers.emplace("concat", parse_concat);
  res->parsers.emplace("cond", parse_cond);
  res->parsers.emplace("acond", parse_acond);
  res->parsers.emplace("const", parse_const);
  res->parsers.emplace("constd", parse_constd);
  res->parsers.emplace("consth", parse_consth);
  res->parsers.emplace("eq", parse_eq);
  res->parsers.emplace("iff", parse_iff);
  res->parsers.emplace("implies", parse_implies);
  res->parsers.emplace("mul", parse_mul);
  res->parsers.emplace("nand", parse_nand);
  res->parsers.emplace("neg", parse_neg);
  res->parsers.emplace("inc", parse_inc);
  res->parsers.emplace("dec", parse_dec);
  res->parsers.emplace("ne", parse_ne);
  res->parsers.emplace("nor", parse_nor);
  res->parsers.emplace("not", parse_not);
  res->parsers.emplace("one", parse_one);
  res->parsers.emplace("ones", parse_ones);
  res->parsers.emplace("or", parse_or);
  res->parsers.emplace("read", parse_read);
  res->parsers.emplace("redand", parse_redand);
  res->parsers.emplace("redor", parse_redor);
  res->parsers.emplace("redxor", parse_redxor);
  res->parsers.emplace("rol", parse_rol);
  res->parsers.emplace("root", parse_root); /* only in parser */
  res->parsers.emplace("ror", parse_ror);
  res->parsers.emplace("saddo", parse_saddo);
  res->parsers.emplace("sdivo", parse_sdivo);
  res->parsers.emplace("sdiv", parse_sdiv);
  res->parsers.emplace("sext", parse_sext);
  res->parsers.emplace("sgte", parse_sgte);
  res->parsers.emplace("sgt", parse_sgt);
  res->parsers.emplace("slice", parse_slice);
  res->parsers.emplace("sll", parse_sll);
  res->parsers.emplace("slte", parse_slte);
  res->parsers.emplace("slt", parse_slt);
  res->parsers.emplace("smod", parse_smod);
  res->parsers.emplace("smulo", parse_smulo);
  res->parsers.emplace("sra", parse_sra);
  res->parsers.emplace("srem", parse_srem);
  res->parsers.emplace("srl", parse_srl);
  res->parsers.emplace("ssubo", parse_ssubo);
  res->parsers.emplace("sub", parse_sub);
  res->parsers.emplace("uaddo", parse_uaddo);
  res->parsers.emplace("udiv", parse_udiv);
  res->parsers.emplace("uext", parse_uext);
  res->parsers.emplace("ugte", parse_ugte);
  res->parsers.emplace("ugt", parse_ugt);
  res->parsers.emplace("ulte", parse_ulte);
  res->parsers.emplace("ult", parse_ult);
  res->parsers.emplace("umulo", parse_umulo);
  res->parsers.emplace("urem", parse_urem);
  res->parsers.emplace("usubo", parse_usubo);
  res->parsers.emplace("var", parse_var);
  res->parsers.emplace("write", parse_write);
  res->parsers.emplace("xnor", parse_xnor);
  res->parsers.emplace("xor", parse_xor);
  res->parsers.emplace("zero", parse_zero);
  res->parsers.emplace("param", parse_param);
  res->parsers.emplace("lambda", parse_lambda);
  res->parsers.emplace("apply", parse_apply);

  res->parsers.at("var");
  return res;
}

static void
delete_bzla_parser(BzlaBTORParser *parser)
{
  delete parser;
}

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
parse_btor_parser(BzlaBTORParser *parser,
                  // BzlaIntStack *prefix,
                  FILE *infile,
                  const char *infile_name,
                  FILE *outfile,
                  BzlaParseResult *res)
{
  BzlaOpParser op_parser;
  int32_t ch;
  uint64_t width = 0;
  BitwuzlaTerm e;

  assert(infile);
  assert(infile_name);

  // BZLA_MSG(
  //     bitwuzla_get_bzla_msg(parser->bitwuzla), 1, "parsing %s", infile_name);

  // parser->nprefix     = 0;
  // parser->prefix      = prefix;
  parser->infile      = infile;
  parser->infile_name = infile_name;
  parser->lineno      = 1;
  parser->saved       = false;

  memset(res, 0, sizeof *(res));

NEXT:
  assert(parser->error.empty());
  ch = nextch_btor(parser);
  if (isspace(ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:

    if (res)
    {
      res->result = bitwuzla_check_sat(get_bitwuzla(parser));
      if (res->result == BITWUZLA_SAT)
      {
        fprintf(outfile, "sat\n");
      }
      else if (res->result == BITWUZLA_UNSAT)
      {
        fprintf(outfile, "unsat\n");
      }
      /* Do not print 'unknown' if we print DIMACS. 'unknown' is only returned
       * if SAT solver is used non-incremental. */
      // else if (!bitwuzla_get_option(parser->options,
      // BITWUZLA_OPT_PRINT_DIMACS))
      else
      {
        fprintf(outfile, "unknown\n");
      }
    }

    return 0;
  }

  if (ch == ';') /* skip comments */
  {
  COMMENTS:
    while ((ch = nextch_btor(parser)) != '\n')
      if (ch == EOF) goto DONE;

    goto NEXT;
  }

  if (!isdigit(ch))
  {
    (void) perr_btor(parser, "expected ';' or digit");
    return parser->error.c_str();
  }

  savech_btor(parser, ch);

  if (!parse_positive_int(parser, &parser->idx).empty())
  {
    return parser->error.c_str();
  }

  while (parser->exps.size() <= parser->idx)
  {
    Info info;
    memset(&info, 0, sizeof info);
    parser->info.push_back(info);
    parser->exps.push_back(0);
  }

  if (parser->exps[parser->idx])
  {
    (void) perr_btor(parser,
                     "'" + std::to_string(parser->idx) + "' defined twice");
    return parser->error.c_str();
  }

  if (!parse_space(parser))
  {
    return parser->error.c_str();
  }

  std::stringstream op;
  while (!isspace(ch = nextch_btor(parser)) && ch != EOF)
  {
    op << static_cast<char>(ch);
  }

  savech_btor(parser, ch);

  if (!parse_space(parser))
  {
    return parser->error.c_str();
  }

  if (!parse_positive_int(parser, &width).empty())
  {
    return parser->error.c_str();
  }

  if (!(op_parser = parser->parsers.at(op.str())))
  {
    (void) perr_btor(parser, "invalid operator '" + op.str() + "'");
    return parser->error.c_str();
  }

  if (!(e = op_parser(parser, width)))
  {
    assert(!parser->error.empty());
    return parser->error.c_str();
  }

  parser->exps[parser->idx] = e;

SKIP:
  ch = nextch_btor(parser);
  if (ch == ' ' || ch == '\t' || ch == '\r') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n')
  {
    (void) perr_btor(parser, "expected new line");
    return parser->error.c_str();
  }

  goto NEXT;
}

static BzlaParserAPI parsebtor_parser_api = {
    (BzlaInitParser) new_btor_parser,
    (BzlaResetParser) delete_bzla_parser,
    (BzlaParse) parse_btor_parser,
};

const BzlaParserAPI *
bzla_parsebtor_parser_api()
{
  return &parsebtor_parser_api;
}
