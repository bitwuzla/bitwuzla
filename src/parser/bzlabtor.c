/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlabtor.h"

#include <assert.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bzlabv.h"
#include "bzlamsg.h"
#include "bzlaparse.h"
#include "utils/bzlamem.h"
#include "utils/bzlastack.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

void bitwuzla_set_bzla_id(Bitwuzla *bitwuzla,
                          const BitwuzlaTerm *term,
                          int32_t id);

/*------------------------------------------------------------------------*/

typedef struct BzlaBZLAParser BzlaBZLAParser;

typedef const BitwuzlaTerm *(*BzlaOpParser)(BzlaBZLAParser *, uint32_t width);

#define SIZE_PARSERS 128

typedef struct Info Info;

struct Info
{
  uint32_t var : 1;
  uint32_t array : 1;
};

BZLA_DECLARE_STACK(BzlaInfo, Info);
BZLA_DECLARE_STACK(BitwuzlaTermPtr, BitwuzlaTerm *);
BZLA_DECLARE_STACK(BitwuzlaTermConstPtr, const BitwuzlaTerm *);

struct BzlaBZLAParser
{
  BzlaMemMgr *mem;
  Bitwuzla *bitwuzla;

  uint32_t nprefix;
  BzlaIntStack *prefix;
  FILE *infile;
  const char *infile_name;
  uint32_t lineno;
  bool saved;
  int32_t saved_char;
  char *error;

  BitwuzlaTermConstPtrStack exps;
  BzlaInfoStack info;

  BitwuzlaTermConstPtrStack regs;
  BitwuzlaTermConstPtrStack lambdas;
  BitwuzlaTermConstPtrStack params;

  BzlaCharStack op;
  BzlaCharStack constant;
  BzlaCharStack symbol;

  BzlaOpParser *parsers;
  const char **ops;

  uint32_t idx;
};

/*------------------------------------------------------------------------*/

static const char *
perr_btor(BzlaBZLAParser *parser, const char *fmt, ...)
{
  size_t bytes;
  va_list ap;

  if (!parser->error)
  {
    va_start(ap, fmt);
    bytes = bzla_mem_parse_error_msg_length(parser->infile_name, fmt, ap);
    va_end(ap);

    va_start(ap, fmt);
    parser->error = bzla_mem_parse_error_msg(
        parser->mem, parser->infile_name, parser->lineno, 0, fmt, ap, bytes);
    va_end(ap);
  }

  return parser->error;
}

/*------------------------------------------------------------------------*/

static uint32_t bzla_primes_btor[4] = {
    111130391, 22237357, 33355519, 444476887};

#define BZLA_PRIMES_BZLA \
  ((sizeof bzla_primes_btor) / sizeof bzla_primes_btor[0])

static uint32_t
hash_op(const char *str, uint32_t salt)
{
  uint32_t i, res;
  const char *p;

  assert(salt < BZLA_PRIMES_BZLA);

  res = 0;
  i   = salt;
  for (p = str; *p; p++)
  {
    res += bzla_primes_btor[i++] * (uint32_t) *p;
    if (i == BZLA_PRIMES_BZLA) i = 0;
  }

  res &= SIZE_PARSERS - 1;

  return res;
}

/*------------------------------------------------------------------------*/

static int32_t
nextch_btor(BzlaBZLAParser *parser)
{
  int32_t ch;

  if (parser->saved)
  {
    ch            = parser->saved_char;
    parser->saved = false;
  }
  else if (parser->prefix
           && parser->nprefix < BZLA_COUNT_STACK(*parser->prefix))
  {
    ch = parser->prefix->start[parser->nprefix++];
  }
  else
    ch = getc(parser->infile);

  if (ch == '\n') parser->lineno++;

  return ch;
}

static void
savech_btor(BzlaBZLAParser *parser, int32_t ch)
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

static const char *
parse_non_negative_int(BzlaBZLAParser *parser, uint32_t *res_ptr)
{
  int32_t res, ch;

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

  return 0;
}

static const char *
parse_positive_int(BzlaBZLAParser *parser, uint32_t *res_ptr)
{
  int32_t res, ch;

  ch = nextch_btor(parser);
  if (!isdigit(ch)) return perr_btor(parser, "expected digit");

  if (ch == '0') return perr_btor(parser, "expected non zero digit");

  res = ch - '0';

  while (isdigit(ch = nextch_btor(parser))) res = 10 * res + (ch - '0');

  savech_btor(parser, ch);
  *res_ptr = res;

  return 0;
}

static const char *
parse_non_zero_int(BzlaBZLAParser *parser, int32_t *res_ptr)
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

  return 0;
}

static const BitwuzlaTerm *
parse_exp(BzlaBZLAParser *parser,
          uint32_t expected_width,
          bool can_be_array,
          bool can_be_inverted,
          int32_t *rlit)
{
  size_t idx;
  int32_t lit;
  uint32_t width_res;
  const char *err_msg;
  const BitwuzlaTerm *res;

  lit     = 0;
  err_msg = parse_non_zero_int(parser, &lit);
  if (rlit) *rlit = lit;
  if (err_msg) return 0;

  if (!can_be_inverted && lit < 0)
  {
    (void) perr_btor(parser, "positive literal expected");
    return 0;
  }

  idx = abs(lit);
  assert(idx);

  if (idx >= BZLA_COUNT_STACK(parser->exps) || !(res = parser->exps.start[idx]))
  {
    (void) perr_btor(parser, "literal '%d' undefined", lit);
    return 0;
  }

  if (bitwuzla_term_is_var(res) && bitwuzla_term_is_bound_var(res))
  {
    (void) perr_btor(
        parser, "param '%d' cannot be used outside of its defined scope", lit);
    return 0;
  }

  if (!can_be_array && bitwuzla_term_is_array(res))
  {
    (void) perr_btor(
        parser, "literal '%d' refers to an unexpected array expression", lit);
    return 0;
  }

  if (expected_width)
  {
    if (bitwuzla_term_is_fun(res) || bitwuzla_term_is_array(res))
    {
      const BitwuzlaSort *sort = bitwuzla_term_fun_get_codomain_sort(res);
      assert(bitwuzla_sort_is_bv(sort));
      width_res = bitwuzla_sort_bv_get_size(sort);
    }
    else
    {
      assert(bitwuzla_term_is_bv(res));
      width_res = bitwuzla_term_bv_get_size(res);
    }

    assert(expected_width == width_res);
    if (expected_width != width_res)
    {
      (void) perr_btor(parser,
                       "literal '%d' has width '%d' but expected '%d'",
                       lit,
                       width_res,
                       expected_width);

      return 0;
    }
  }

  if (lit < 0)
  {
    res = bitwuzla_mk_term1(parser->bitwuzla, BITWUZLA_KIND_BV_NOT, res);
  }
  return res;
}

static const char *
parse_space(BzlaBZLAParser *parser)
{
  int32_t ch;

  ch = nextch_btor(parser);
  if (ch != ' ' && ch != '\t')
    return perr_btor(parser, "expected space or tab");

SKIP:
  ch = nextch_btor(parser);
  if (ch == ' ' || ch == '\t') goto SKIP;

  if (!ch) return perr_btor(parser, "unexpected character");

  savech_btor(parser, ch);

  return 0;
}

static int32_t
parse_symbol(BzlaBZLAParser *parser)
{
  int32_t ch;

  while ((ch = nextch_btor(parser)) == ' ' || ch == '\t')
    ;

  if (ch == EOF)
  {
  UNEXPECTED_EOF:
    (void) perr_btor(parser, "unexpected EOF");
    return 0;
  }

  assert(BZLA_EMPTY_STACK(parser->symbol));

  if (ch != '\n')
  {
    BZLA_PUSH_STACK(parser->symbol, ch);

    while (!isspace(ch = nextch_btor(parser)))
    {
      if (!isprint(ch)) perr_btor(parser, "invalid character");
      if (ch == EOF) goto UNEXPECTED_EOF;
      BZLA_PUSH_STACK(parser->symbol, ch);
    }
  }

  savech_btor(parser, ch);
  BZLA_PUSH_STACK(parser->symbol, 0);
  BZLA_RESET_STACK(parser->symbol);
  return 1;
}

static const BitwuzlaTerm *
parse_var(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res;
  const BitwuzlaSort *s;

  if (!parse_symbol(parser)) return 0;

  s   = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  res = bitwuzla_mk_const(
      parser->bitwuzla, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  bitwuzla_set_bzla_id(parser->bitwuzla, res, parser->idx);
  parser->info.start[parser->idx].var = 1;
  return res;
}

static const BitwuzlaTerm *
parse_param(BzlaBZLAParser *parser, uint32_t width)
{
  if (!parse_symbol(parser)) return 0;
  const BitwuzlaSort *s   = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  const BitwuzlaTerm *res = bitwuzla_mk_var(
      parser->bitwuzla, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  BZLA_PUSH_STACK(parser->params, res);
  return res;
}

static const BitwuzlaTerm *
parse_param_exp(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res = parse_exp(parser, width, false, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_var(res)) return res;
  (void) perr_btor(parser, "expected parameter");
  return 0;
}

static const BitwuzlaTerm *
parse_array(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res;
  const BitwuzlaSort *s, *is, *es;
  uint32_t idx_width;

  if (parse_space(parser)) return 0;
  if (parse_positive_int(parser, &idx_width)) return 0;
  if (!parse_symbol(parser)) return 0;

  is  = bitwuzla_mk_bv_sort(parser->bitwuzla, idx_width);
  es  = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  s   = bitwuzla_mk_array_sort(parser->bitwuzla, is, es);
  res = bitwuzla_mk_const(
      parser->bitwuzla, s, parser->symbol.start[0] ? parser->symbol.start : 0);
  bitwuzla_set_bzla_id(parser->bitwuzla, res, parser->idx);
  parser->info.start[parser->idx].array = 1;
  return res;
}

static const BitwuzlaTerm *
parse_array_exp(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res = parse_exp(parser, width, true, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_array(res)) return res;
  (void) perr_btor(parser, "expected array expression");
  return 0;
}

static const BitwuzlaTerm *
parse_fun_exp(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res = parse_exp(parser, width, true, false, 0);
  if (!res) return 0;
  if (bitwuzla_term_is_fun(res) || bitwuzla_term_is_array(res)) return res;
  (void) perr_btor(parser, "expected function expression");
  return 0;
}

static const BitwuzlaTerm *
parse_const(BzlaBZLAParser *parser, uint32_t width)
{
  int32_t ch;
  uint32_t cwidth;

  if (parse_space(parser)) return 0;

  assert(BZLA_EMPTY_STACK(parser->constant));
  while (!isspace(ch = nextch_btor(parser)) && ch != EOF && ch != ';')
  {
    if (ch != '0' && ch != '1')
    {
      (void) perr_btor(parser, "expected '0' or '1'");
      return 0;
    }

    BZLA_PUSH_STACK(parser->constant, ch);
  }

  savech_btor(parser, ch);
  cwidth = BZLA_COUNT_STACK(parser->constant);
  BZLA_PUSH_STACK(parser->constant, 0);
  BZLA_RESET_STACK(parser->constant);

  if (cwidth != width)
  {
    (void) perr_btor(parser,
                     "binary constant '%s' exceeds bit width %d",
                     parser->constant.start,
                     width);
    return 0;
  }

  const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(parser->bitwuzla, width);

  return bitwuzla_mk_bv_value(
      parser->bitwuzla, sort, parser->constant.start, BITWUZLA_BV_BASE_BIN);
}

static const BitwuzlaTerm *
parse_consth(BzlaBZLAParser *parser, uint32_t width)
{
  int32_t ch;
  uint32_t cwidth;
  char *tmp, *ext;
  BzlaBitVector *tmpbv, *extbv;
  const BitwuzlaTerm *res;

  if (parse_space(parser)) return 0;

  assert(BZLA_EMPTY_STACK(parser->constant));

  while (!isspace(ch = nextch_btor(parser)) && ch != EOF && ch != ';')
  {
    if (!isxdigit(ch))
    {
      (void) perr_btor(parser, "expected hexidecimal digit");
      return 0;
    }

    BZLA_PUSH_STACK(parser->constant, ch);
  }

  savech_btor(parser, ch);

  cwidth = BZLA_COUNT_STACK(parser->constant);
  BZLA_PUSH_STACK(parser->constant, 0);
  BZLA_RESET_STACK(parser->constant);

  tmp = bzla_util_hex_to_bin_str_n(parser->mem, parser->constant.start, cwidth);
  cwidth = strlen(tmp);

  if (cwidth > width)
  {
    (void) perr_btor(parser,
                     "hexadecimal constant '%s' exceeds bit width %d",
                     parser->constant.start,
                     width);
    bzla_mem_freestr(parser->mem, tmp);
    return 0;
  }

  if (cwidth < width)
  {
    tmpbv = 0;
    if (!strcmp(tmp, ""))
      extbv = bzla_bv_new(parser->mem, width - cwidth);
    else
    {
      tmpbv = bzla_bv_char_to_bv(parser->mem, tmp);
      extbv = bzla_bv_uext(parser->mem, tmpbv, width - cwidth);
    }
    ext = bzla_bv_to_char(parser->mem, extbv);
    bzla_mem_freestr(parser->mem, tmp);
    bzla_bv_free(parser->mem, extbv);
    if (tmpbv) bzla_bv_free(parser->mem, tmpbv);
    tmp = ext;
  }

  assert(width == strlen(tmp));
  const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  res = bitwuzla_mk_bv_value(parser->bitwuzla, sort, tmp, BITWUZLA_BV_BASE_BIN);
  bzla_mem_freestr(parser->mem, tmp);

  assert(bitwuzla_term_bv_get_size(res) == width);

  return res;
}

static const BitwuzlaTerm *
parse_constd(BzlaBZLAParser *parser, uint32_t width)
{
  int32_t ch;
  uint32_t cwidth;
  char *tmp, *ext;
  BzlaBitVector *tmpbv, *extbv;
  const BitwuzlaTerm *res;

  if (parse_space(parser)) return 0;

  assert(BZLA_EMPTY_STACK(parser->constant));

  ch = nextch_btor(parser);
  if (!isdigit(ch))
  {
    (void) perr_btor(parser, "expected digit");
    return 0;
  }

  BZLA_PUSH_STACK(parser->constant, ch);

  if (ch == '0')
  {
    ch = nextch_btor(parser);

    if (isdigit(ch))
    {
      (void) perr_btor(parser, "digit after '0'");
      return 0;
    }

    tmp = bzla_mem_strdup(parser->mem, "");
  }
  else
  {
    while (isdigit(ch = nextch_btor(parser)))
      BZLA_PUSH_STACK(parser->constant, ch);

    cwidth = BZLA_COUNT_STACK(parser->constant);

    tmp =
        bzla_util_dec_to_bin_str_n(parser->mem, parser->constant.start, cwidth);
  }

  BZLA_PUSH_STACK(parser->constant, 0);
  BZLA_RESET_STACK(parser->constant);

  savech_btor(parser, ch);

  cwidth = strlen(tmp);
  if (cwidth > width)
  {
    (void) perr_btor(parser,
                     "decimal constant '%s' exceeds bit width %d",
                     parser->constant.start,
                     width);
    bzla_mem_freestr(parser->mem, tmp);
    return 0;
  }

  if (cwidth < width)
  {
    tmpbv = 0;
    if (!strcmp(tmp, ""))
      extbv = bzla_bv_new(parser->mem, width - cwidth);
    else
    {
      tmpbv = bzla_bv_char_to_bv(parser->mem, tmp);
      extbv = bzla_bv_uext(parser->mem, tmpbv, width - cwidth);
    }
    ext = bzla_bv_to_char(parser->mem, extbv);
    bzla_mem_freestr(parser->mem, tmp);
    bzla_bv_free(parser->mem, extbv);
    if (tmpbv) bzla_bv_free(parser->mem, tmpbv);
    tmp = ext;
  }

  assert(width == strlen(tmp));
  const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  res = bitwuzla_mk_bv_value(parser->bitwuzla, sort, tmp, BITWUZLA_BV_BASE_BIN);
  bzla_mem_freestr(parser->mem, tmp);

  assert(bitwuzla_term_bv_get_size(res) == width);

  return res;
}

static const BitwuzlaTerm *
parse_zero(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaSort *s = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  return bitwuzla_mk_bv_zero(parser->bitwuzla, s);
}

static const BitwuzlaTerm *
parse_one(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaSort *s = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  return bitwuzla_mk_bv_one(parser->bitwuzla, s);
}

static const BitwuzlaTerm *
parse_ones(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaSort *s = bitwuzla_mk_bv_sort(parser->bitwuzla, width);
  return bitwuzla_mk_bv_ones(parser->bitwuzla, s);
}

static const BitwuzlaTerm *
parse_root(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *res, *tmp;

  if (parse_space(parser)) return 0;
  if (!(res = parse_exp(parser, width, false, true, 0))) return 0;
  if (width > 1)
  {
    tmp = res;
    res = bitwuzla_mk_term1(parser->bitwuzla, BITWUZLA_KIND_BV_REDOR, tmp);
  }
  bitwuzla_assert(parser->bitwuzla, res);
  return res;
}

static const BitwuzlaTerm *
parse_unary(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  assert(width);

  const BitwuzlaTerm *tmp, *res;

  if (parse_space(parser)) return 0;

  if (!(tmp = parse_exp(parser, width, false, true, 0))) return 0;

  res = bitwuzla_mk_term1(parser->bitwuzla, kind, tmp);
  assert(bitwuzla_term_bv_get_size(res) == width);

  return res;
}

static const BitwuzlaTerm *
parse_not(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_NOT, width);
}

static const BitwuzlaTerm *
parse_neg(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_NEG, width);
}

static const BitwuzlaTerm *
parse_inc(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_INC, width);
}

static const BitwuzlaTerm *
parse_dec(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_unary(parser, BITWUZLA_KIND_BV_DEC, width);
}

static const BitwuzlaTerm *
parse_redunary(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  assert(width == 1);

  const BitwuzlaTerm *tmp, *res;

  (void) width;

  if (parse_space(parser)) return 0;

  if (!(tmp = parse_exp(parser, 0, false, true, 0))) return 0;

  if (bitwuzla_term_bv_get_size(tmp) == 1)
  {
    (void) perr_btor(parser, "argument of reduction operation of width 1");
    return 0;
  }

  res = bitwuzla_mk_term1(parser->bitwuzla, kind, tmp);
  assert(bitwuzla_term_bv_get_size(res) == 1);

  return res;
}

static const BitwuzlaTerm *
parse_redand(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDAND, width);
}

static const BitwuzlaTerm *
parse_redor(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDOR, width);
}

static const BitwuzlaTerm *
parse_redxor(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_redunary(parser, BITWUZLA_KIND_BV_REDXOR, width);
}

static const BitwuzlaTerm *
parse_binary(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  assert(width);

  const BitwuzlaTerm *l, *r, *res;

  if (parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, width, false, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  res = bitwuzla_mk_term2(parser->bitwuzla, kind, l, r);
  assert(bitwuzla_term_bv_get_size(res) == width);

  return res;
}

static const BitwuzlaTerm *
parse_add(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_ADD, width);
}

static const BitwuzlaTerm *
parse_and(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_AND, width);
}

static const BitwuzlaTerm *
parse_smod(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SMOD, width);
}

static const BitwuzlaTerm *
parse_srem(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SREM, width);
}

static const BitwuzlaTerm *
parse_mul(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_MUL, width);
}

static const BitwuzlaTerm *
parse_sub(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SUB, width);
}

static const BitwuzlaTerm *
parse_udiv(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_UDIV, width);
}

static const BitwuzlaTerm *
parse_urem(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_UREM, width);
}

static const BitwuzlaTerm *
parse_xor(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_XOR, width);
}

static const BitwuzlaTerm *
parse_xnor(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_XNOR, width);
}

static const BitwuzlaTerm *
parse_or(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_OR, width);
}

static const BitwuzlaTerm *
parse_nor(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_NOR, width);
}

static const BitwuzlaTerm *
parse_nand(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_NAND, width);
}

static const BitwuzlaTerm *
parse_sdiv(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_binary(parser, BITWUZLA_KIND_BV_SDIV, width);
}

static const BitwuzlaTerm *
parse_logical(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  const BitwuzlaTerm *l, *r, *res;

  if (width != 1)
  {
    (void) perr_btor(parser, "logical operator bit width '%d'", width);
    return 0;
  }

  if (parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, false, true, 0))) return 0;

  if (bitwuzla_term_bv_get_size(l) != 1)
  {
  BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN:
    (void) perr_btor(parser, "expected argument of bit width '1'");
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (parse_space(parser)) goto RELEASE_L_AND_RETURN_ERROR;

  if (!(r = parse_exp(parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  if (bitwuzla_term_bv_get_size(r) != 1)
  {
    goto BIT_WIDTH_ERROR_RELEASE_L_AND_RETURN;
  }

  res = bitwuzla_mk_term2(parser->bitwuzla, kind, l, r);
  assert(bitwuzla_term_bv_get_size(res) == 1);

  return res;
}

static const BitwuzlaTerm *
parse_implies(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_logical(parser, BITWUZLA_KIND_IMPLIES, width);
}

static const BitwuzlaTerm *
parse_iff(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_logical(parser, BITWUZLA_KIND_IFF, width);
}

static const BitwuzlaTerm *
parse_compare_and_overflow(BzlaBZLAParser *parser,
                           BitwuzlaKind kind,
                           uint32_t width,
                           bool can_be_array)
{
  const BitwuzlaTerm *l, *r, *res;

  if (width != 1)
  {
    (void) perr_btor(
        parser, "comparison or overflow operator returns %d bits", width);
    return 0;
  }

  if (parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, can_be_array, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, can_be_array, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  if (!bitwuzla_term_is_equal_sort(l, r))
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

  res = bitwuzla_mk_term2(parser->bitwuzla, kind, l, r);
  assert(bitwuzla_term_bv_get_size(res) == 1);
  return res;
}

static const BitwuzlaTerm *
parse_eq(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_EQUAL, width, 1);
}

static const BitwuzlaTerm *
parse_ne(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_DISTINCT, width, 1);
}

static const BitwuzlaTerm *
parse_sgt(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SGT, width, 0);
}

static const BitwuzlaTerm *
parse_sgte(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SGE, width, 0);
}

static const BitwuzlaTerm *
parse_slt(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SLT, width, 0);
}

static const BitwuzlaTerm *
parse_slte(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_SLE, width, 0);
}

static const BitwuzlaTerm *
parse_ugt(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_UGT, width, 0);
}

static const BitwuzlaTerm *
parse_ugte(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_UGE, width, 0);
}

static const BitwuzlaTerm *
parse_ult(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_ULT, width, 0);
}

static const BitwuzlaTerm *
parse_ulte(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(parser, BITWUZLA_KIND_BV_ULE, width, 0);
}

static const BitwuzlaTerm *
parse_saddo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SADD_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_ssubo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SSUB_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_smulo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SMUL_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_sdivo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_SDIV_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_uaddo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_UADD_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_usubo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_USUB_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_umulo(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_compare_and_overflow(
      parser, BITWUZLA_KIND_BV_UMUL_OVERFLOW, width, 0);
}

static const BitwuzlaTerm *
parse_concat(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *l, *r, *res;
  uint32_t lwidth, rwidth;

  if (parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, 0, false, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, false, true, 0)))
    goto RELEASE_L_AND_RETURN_ERROR;

  lwidth = bitwuzla_term_bv_get_size(l);
  rwidth = bitwuzla_term_bv_get_size(r);

  if (lwidth + rwidth != width)
  {
    (void) perr_btor(parser,
                     "operands widths %d and %d do not add up to %d",
                     lwidth,
                     rwidth,
                     width);

    return 0;
  }

  res = bitwuzla_mk_term2(parser->bitwuzla, BITWUZLA_KIND_BV_CONCAT, l, r);
  assert(bitwuzla_term_bv_get_size(res) == width);
  return res;
}

static const BitwuzlaTerm *
parse_shift(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  const BitwuzlaTerm *l, *r, *res, *tmp;
  int32_t lit;
  uint32_t rwidth, rw;

  for (rwidth = 1; rwidth <= 30u && width != (1u << rwidth); rwidth++)
    ;

  if (parse_space(parser)) return 0;

  if (!(l = parse_exp(parser, width, false, true, &lit))) return 0;

  if (parse_space(parser))
  {
  RELEASE_L_AND_RETURN_ERROR:
    return 0;
  }

  if (!(r = parse_exp(parser, 0, false, true, &lit)))
    goto RELEASE_L_AND_RETURN_ERROR;

  rw = bitwuzla_term_bv_get_size(r);
  if (width != rw)
  {
    if (bzla_util_is_power_of_2(width))
    {
      if (rw != bzla_util_log_2(width))
      {
        (void) perr_btor(parser,
                         "literal '%d' has width '%d' but expected '%d'",
                         lit,
                         rw,
                         bzla_util_log_2(width));
        return 0;
      }
      tmp = bitwuzla_mk_term1_indexed1(
          parser->bitwuzla, BITWUZLA_KIND_BV_ZERO_EXTEND, r, width - rw);
      r = tmp;
    }
    else
    {
      (void) perr_btor(parser,
                       "literal '%d' has width '%d' but expected '%d'",
                       lit,
                       rw,
                       width);
      return 0;
    }
  }
  res = bitwuzla_mk_term2(parser->bitwuzla, kind, l, r);
  assert(bitwuzla_term_bv_get_size(res) == width);
  return res;
}

static const BitwuzlaTerm *
parse_rol(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ROL, width);
}

static const BitwuzlaTerm *
parse_ror(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ROR, width);
}

static const BitwuzlaTerm *
parse_sll(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_SHL, width);
}

static const BitwuzlaTerm *
parse_sra(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_ASHR, width);
}

static const BitwuzlaTerm *
parse_srl(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_shift(parser, BITWUZLA_KIND_BV_SHR, width);
}

static const BitwuzlaTerm *
parse_cond(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *c, *t, *e;

  if (parse_space(parser)) return 0;

  if (!(c = parse_exp(parser, 1, false, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    return 0;
  }

  if (!(t = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_C_AND_RETURN_ERROR;

  if (parse_space(parser))
  {
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (!(e = parse_exp(parser, width, false, true, 0)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  return bitwuzla_mk_term3(parser->bitwuzla, BITWUZLA_KIND_ITE, c, t, e);
}

static const BitwuzlaTerm *
parse_acond(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *c, *t, *e;
  uint32_t idxwidth;

  idxwidth = 0;

  if (parse_space(parser)) return 0;

  if (parse_positive_int(parser, &idxwidth)) return 0;

  if (parse_space(parser)) return 0;

  if (!(c = parse_exp(parser, 1, false, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_C_AND_RETURN_ERROR:
    return 0;
  }

  if (!(t = parse_array_exp(parser, width))) goto RELEASE_C_AND_RETURN_ERROR;

  if (idxwidth
      != bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_index_sort(t)))
  {
    (void) perr_btor(parser, "mismatch of index bit width of 'then' array");
  RELEASE_C_AND_T_AND_RETURN_ERROR:
    goto RELEASE_C_AND_RETURN_ERROR;
  }

  if (parse_space(parser)) goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (!(e = parse_array_exp(parser, width)))
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;

  if (idxwidth
      != bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_index_sort(e)))
  {
    (void) perr_btor(parser, "mismatch of index bit width of 'else' array");
    goto RELEASE_C_AND_T_AND_RETURN_ERROR;
  }

  return bitwuzla_mk_term3(parser->bitwuzla, BITWUZLA_KIND_ITE, c, t, e);
}

static const BitwuzlaTerm *
parse_slice(BzlaBZLAParser *parser, uint32_t width)
{
  uint32_t argwidth, upper, lower, delta;
  const BitwuzlaTerm *arg;

  if (parse_space(parser)) return 0;

  if (!(arg = parse_exp(parser, 0, false, true, 0))) return 0;

  if (parse_space(parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    return 0;
  }

  argwidth = bitwuzla_term_bv_get_size(arg);

  if (parse_non_negative_int(parser, &upper)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper >= argwidth)
  {
    (void) perr_btor(
        parser, "upper index '%d' >= argument width '%d", upper, argwidth);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  if (parse_space(parser)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (parse_non_negative_int(parser, &lower)) goto RELEASE_ARG_AND_RETURN_ERROR;

  if (upper < lower)
  {
    (void) perr_btor(
        parser, "upper index '%d' smaller than lower index '%d'", upper, lower);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  delta = upper - lower + 1;
  if (delta != width)
  {
    (void) perr_btor(parser,
                     "slice width '%d' not equal to expected width '%d'",
                     delta,
                     width);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  return bitwuzla_mk_term1_indexed2(
      parser->bitwuzla, BITWUZLA_KIND_BV_EXTRACT, arg, upper, lower);
}

static const BitwuzlaTerm *
parse_read(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *array, *idx;
  uint32_t idxwidth;

  if (parse_space(parser)) return 0;

  if (!(array = parse_array_exp(parser, width))) return 0;

  if (parse_space(parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    return 0;
  }

  idxwidth =
      bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_index_sort(array));
  if (!(idx = parse_exp(parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  return bitwuzla_mk_term2(
      parser->bitwuzla, BITWUZLA_KIND_ARRAY_SELECT, array, idx);
}

static const BitwuzlaTerm *
parse_write(BzlaBZLAParser *parser, uint32_t width)
{
  const BitwuzlaTerm *array, *idx, *val;
  uint32_t idxwidth, valwidth;

  idxwidth = 0;
  valwidth = 0;

  if (parse_space(parser)) return 0;

  if (parse_positive_int(parser, &idxwidth)) return 0;

  if (parse_space(parser)) return 0;

  if (!(array = parse_array_exp(parser, width))) return 0;

  if (parse_space(parser))
  {
  RELEASE_ARRAY_AND_RETURN_ERROR:
    return 0;
  }

  if (!(idx = parse_exp(parser, idxwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_RETURN_ERROR;

  if (parse_space(parser))
  {
  RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR:
    goto RELEASE_ARRAY_AND_RETURN_ERROR;
  }

  valwidth =
      bitwuzla_sort_bv_get_size(bitwuzla_term_array_get_element_sort(array));
  if (!(val = parse_exp(parser, valwidth, false, true, 0)))
    goto RELEASE_ARRAY_AND_IDX_AND_RETURN_ERROR;

  return bitwuzla_mk_term3(
      parser->bitwuzla, BITWUZLA_KIND_ARRAY_STORE, array, idx, val);
}

static const BitwuzlaTerm *
parse_lambda(BzlaBZLAParser *parser, uint32_t width)
{
  uint32_t paramwidth;
  const BitwuzlaTerm **args;
  const BitwuzlaTerm *exp, *res;

  paramwidth = 0;

  if (parse_space(parser)) return 0;

  if (parse_positive_int(parser, &paramwidth)) return 0;

  if (parse_space(parser)) return 0;

  BZLA_NEWN(parser->mem, args, 2);
  if (!(args[0] = parse_param_exp(parser, paramwidth))) return 0;

  if (bitwuzla_term_is_bound_var(args[0]))
  {
    perr_btor(parser, "param already bound by other lambda");
    goto RELEASE_PARAM_AND_RETURN_ERROR;
  }

  if (parse_space(parser))
  {
  RELEASE_PARAM_AND_RETURN_ERROR:
    return 0;
  }

  if (!(exp = parse_exp(parser, width, true, true, 0)))
    goto RELEASE_PARAM_AND_RETURN_ERROR;
  args[1] = exp;

  res = bitwuzla_mk_term(parser->bitwuzla, BITWUZLA_KIND_LAMBDA, 2, args);

  BZLA_DELETEN(parser->mem, args, 2);
  BZLA_PUSH_STACK(parser->lambdas, res);
  return res;
}

static const BitwuzlaTerm *
parse_apply(BzlaBZLAParser *parser, uint32_t width)
{
  uint32_t i, arity;
  const BitwuzlaTerm *res, *fun, *arg;
  BitwuzlaTermConstPtrStack args;

  if (parse_space(parser)) return 0;

  if (!(fun = parse_fun_exp(parser, width))) return 0;

  BZLA_INIT_STACK(parser->mem, args);

  if (parse_space(parser))
  {
  RELEASE_FUN_AND_RETURN_ERROR:
    BZLA_RELEASE_STACK(args);
    return 0;
  }

  arity = bitwuzla_sort_fun_get_arity(bitwuzla_term_get_sort(fun));
  BZLA_PUSH_STACK(args, fun);
  for (i = 0; i < arity; i++)
  {
    arg = parse_exp(parser, 0, false, true, 0);
    if (!arg) goto RELEASE_FUN_AND_RETURN_ERROR;

    if (i < arity - 1)
      if (parse_space(parser)) goto RELEASE_FUN_AND_RETURN_ERROR;

    BZLA_PUSH_STACK(args, arg);
  }

  res = bitwuzla_mk_term(parser->bitwuzla,
                         BITWUZLA_KIND_APPLY,
                         BZLA_COUNT_STACK(args),
                         args.start);
  BZLA_RELEASE_STACK(args);
  return res;
}

static const BitwuzlaTerm *
parse_ext(BzlaBZLAParser *parser, BitwuzlaKind kind, uint32_t width)
{
  const BitwuzlaTerm *res, *arg;
  uint32_t awidth, ewidth;

  if (parse_space(parser)) return 0;

  if (!(arg = parse_exp(parser, 0, false, true, 0))) return 0;

  awidth = bitwuzla_term_bv_get_size(arg);

  if (parse_space(parser))
  {
  RELEASE_ARG_AND_RETURN_ERROR:
    return 0;
  }

  if (parse_non_negative_int(parser, &ewidth))
    goto RELEASE_ARG_AND_RETURN_ERROR;

  if (awidth + ewidth != width)
  {
    (void) perr_btor(parser,
                     "argument width of %d plus %d does not match %d",
                     awidth,
                     ewidth,
                     width);
    goto RELEASE_ARG_AND_RETURN_ERROR;
  }

  res = bitwuzla_mk_term1_indexed1(parser->bitwuzla, kind, arg, ewidth);
  assert(bitwuzla_term_bv_get_size(res) == width);
  return res;
}

static const BitwuzlaTerm *
parse_sext(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_ext(parser, BITWUZLA_KIND_BV_SIGN_EXTEND, width);
}

static const BitwuzlaTerm *
parse_uext(BzlaBZLAParser *parser, uint32_t width)
{
  return parse_ext(parser, BITWUZLA_KIND_BV_ZERO_EXTEND, width);
}

static void
new_parser(BzlaBZLAParser *parser, BzlaOpParser op_parser, const char *op)
{
  uint32_t p, d;

  p = hash_op(op, 0);
  assert(p < SIZE_PARSERS);

  if (parser->ops[p])
  {
    d = hash_op(op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
      assert(p < SIZE_PARSERS);
    } while (parser->ops[p]);
  }

  parser->ops[p]     = op;
  parser->parsers[p] = op_parser;
}

static BzlaOpParser
find_parser(BzlaBZLAParser *parser, const char *op)
{
  const char *str;
  uint32_t p, d;

  p = hash_op(op, 0);
  if ((str = parser->ops[p]) && strcasecmp(str, op))
  {
    d = hash_op(op, 1);
    if (!(d & 1)) d++;

    do
    {
      p += d;
      if (p >= SIZE_PARSERS) p -= SIZE_PARSERS;
    } while ((str = parser->ops[p]) && strcasecmp(str, op));
  }

  return str ? parser->parsers[p] : 0;
}

static BzlaBZLAParser *
new_bzla_parser(Bitwuzla *bitwuzla)
{
  BzlaMemMgr *mem = bzla_mem_mgr_new();
  BzlaBZLAParser *res;

  BZLA_NEW(mem, res);
  BZLA_CLR(res);

  res->mem      = mem;
  res->bitwuzla = bitwuzla;

  BZLA_NEWN(mem, res->parsers, SIZE_PARSERS);
  BZLA_NEWN(mem, res->ops, SIZE_PARSERS);
  BZLA_CLRN(res->ops, SIZE_PARSERS);

  BZLA_INIT_STACK(mem, res->exps);
  BZLA_INIT_STACK(mem, res->info);
  BZLA_INIT_STACK(mem, res->regs);
  BZLA_INIT_STACK(mem, res->lambdas);
  BZLA_INIT_STACK(mem, res->params);
  BZLA_INIT_STACK(mem, res->op);
  BZLA_INIT_STACK(mem, res->constant);
  BZLA_INIT_STACK(mem, res->symbol);

  new_parser(res, parse_add, "add");
  new_parser(res, parse_and, "and");
  new_parser(res, parse_array, "array");
  new_parser(res, parse_concat, "concat");
  new_parser(res, parse_cond, "cond");
  new_parser(res, parse_acond, "acond");
  new_parser(res, parse_const, "const");
  new_parser(res, parse_constd, "constd");
  new_parser(res, parse_consth, "consth");
  new_parser(res, parse_eq, "eq");
  new_parser(res, parse_iff, "iff");
  new_parser(res, parse_implies, "implies");
  new_parser(res, parse_mul, "mul");
  new_parser(res, parse_nand, "nand");
  new_parser(res, parse_neg, "neg");
  new_parser(res, parse_inc, "inc");
  new_parser(res, parse_dec, "dec");
  new_parser(res, parse_ne, "ne");
  new_parser(res, parse_nor, "nor");
  new_parser(res, parse_not, "not");
  new_parser(res, parse_one, "one");
  new_parser(res, parse_ones, "ones");
  new_parser(res, parse_or, "or");
  new_parser(res, parse_read, "read");
  new_parser(res, parse_redand, "redand");
  new_parser(res, parse_redor, "redor");
  new_parser(res, parse_redxor, "redxor");
  new_parser(res, parse_rol, "rol");
  new_parser(res, parse_root, "root"); /* only in parser */
  new_parser(res, parse_ror, "ror");
  new_parser(res, parse_saddo, "saddo");
  new_parser(res, parse_sdivo, "sdivo");
  new_parser(res, parse_sdiv, "sdiv");
  new_parser(res, parse_sext, "sext");
  new_parser(res, parse_sgte, "sgte");
  new_parser(res, parse_sgt, "sgt");
  new_parser(res, parse_slice, "slice");
  new_parser(res, parse_sll, "sll");
  new_parser(res, parse_slte, "slte");
  new_parser(res, parse_slt, "slt");
  new_parser(res, parse_smod, "smod");
  new_parser(res, parse_smulo, "smulo");
  new_parser(res, parse_sra, "sra");
  new_parser(res, parse_srem, "srem");
  new_parser(res, parse_srl, "srl");
  new_parser(res, parse_ssubo, "ssubo");
  new_parser(res, parse_sub, "sub");
  new_parser(res, parse_uaddo, "uaddo");
  new_parser(res, parse_udiv, "udiv");
  new_parser(res, parse_uext, "uext");
  new_parser(res, parse_ugte, "ugte");
  new_parser(res, parse_ugt, "ugt");
  new_parser(res, parse_ulte, "ulte");
  new_parser(res, parse_ult, "ult");
  new_parser(res, parse_umulo, "umulo");
  new_parser(res, parse_urem, "urem");
  new_parser(res, parse_usubo, "usubo");
  new_parser(res, parse_var, "var");
  new_parser(res, parse_write, "write");
  new_parser(res, parse_xnor, "xnor");
  new_parser(res, parse_xor, "xor");
  new_parser(res, parse_zero, "zero");
  new_parser(res, parse_param, "param");
  new_parser(res, parse_lambda, "lambda");
  new_parser(res, parse_apply, "apply");

  return res;
}

static void
delete_bzla_parser(BzlaBZLAParser *parser)
{
  BzlaMemMgr *mm = parser->mem;

  BZLA_RELEASE_STACK(parser->exps);
  BZLA_RELEASE_STACK(parser->info);
  BZLA_RELEASE_STACK(parser->regs);
  BZLA_RELEASE_STACK(parser->lambdas);
  BZLA_RELEASE_STACK(parser->params);

  BZLA_RELEASE_STACK(parser->op);
  BZLA_RELEASE_STACK(parser->constant);
  BZLA_RELEASE_STACK(parser->symbol);

  BZLA_DELETEN(mm, parser->parsers, SIZE_PARSERS);
  BZLA_DELETEN(mm, parser->ops, SIZE_PARSERS);

  bzla_mem_freestr(mm, parser->error);
  BZLA_DELETE(mm, parser);
  bzla_mem_mgr_delete(mm);
}

/* Note: we need prefix in case of stdin as input (also applies to compressed
 * input files). */
static const char *
parse_bzla_parser(BzlaBZLAParser *parser,
                  BzlaIntStack *prefix,
                  FILE *infile,
                  const char *infile_name,
                  FILE *outfile,
                  BzlaParseResult *res)
{
  BzlaOpParser op_parser;
  int32_t ch;
  uint32_t width;
  const BitwuzlaTerm *e;

  assert(infile);
  assert(infile_name);
  (void) outfile;

  BZLA_MSG(
      bitwuzla_get_bzla_msg(parser->bitwuzla), 1, "parsing %s", infile_name);

  parser->nprefix     = 0;
  parser->prefix      = prefix;
  parser->infile      = infile;
  parser->infile_name = infile_name;
  parser->lineno      = 1;
  parser->saved       = false;

  BZLA_INIT_STACK(parser->mem, parser->lambdas);
  BZLA_INIT_STACK(parser->mem, parser->params);

  BZLA_CLR(res);

NEXT:
  assert(!parser->error);
  ch = nextch_btor(parser);
  if (isspace(ch)) /* also skip empty lines */
    goto NEXT;

  if (ch == EOF)
  {
  DONE:

    if (res)
    {
      res->status = BITWUZLA_UNKNOWN;
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

  if (!isdigit(ch)) return perr_btor(parser, "expected ';' or digit");

  savech_btor(parser, ch);

  if (parse_positive_int(parser, &parser->idx)) return parser->error;

  while (BZLA_COUNT_STACK(parser->exps) <= parser->idx)
  {
    Info info;
    memset(&info, 0, sizeof info);
    BZLA_PUSH_STACK(parser->info, info);
    BZLA_PUSH_STACK(parser->exps, 0);
  }

  if (parser->exps.start[parser->idx])
    return perr_btor(parser, "'%d' defined twice", parser->idx);

  if (parse_space(parser)) return parser->error;

  assert(BZLA_EMPTY_STACK(parser->op));
  while (!isspace(ch = nextch_btor(parser)) && ch != EOF)
    BZLA_PUSH_STACK(parser->op, ch);

  BZLA_PUSH_STACK(parser->op, 0);
  BZLA_RESET_STACK(parser->op);
  savech_btor(parser, ch);

  if (parse_space(parser)) return parser->error;

  if (parse_positive_int(parser, &width)) return parser->error;

  if (!(op_parser = find_parser(parser, parser->op.start)))
    return perr_btor(parser, "invalid operator '%s'", parser->op.start);

  if (!(e = op_parser(parser, width)))
  {
    assert(parser->error);
    return parser->error;
  }

  parser->exps.start[parser->idx] = e;

SKIP:
  ch = nextch_btor(parser);
  if (ch == ' ' || ch == '\t' || ch == '\r') goto SKIP;

  if (ch == ';') goto COMMENTS; /* ... and force new line */

  if (ch != '\n') return perr_btor(parser, "expected new line");

  goto NEXT;
}

static BzlaParserAPI parsebzla_parser_api = {
    (BzlaInitParser) new_bzla_parser,
    (BzlaResetParser) delete_bzla_parser,
    (BzlaParse) parse_bzla_parser,
};

const BzlaParserAPI *
bzla_parsebzla_parser_api()
{
  return &parsebzla_parser_api;
}
