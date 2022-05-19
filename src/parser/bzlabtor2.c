/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <assert.h>
#include <inttypes.h>
#include <limits.h>

#include "btor2parser.h"
#include "bzlamsg.h"
#include "bzlaparse.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

void bitwuzla_set_bzla_id(Bitwuzla *bitwuzla,
                          const BitwuzlaTerm *term,
                          int32_t id);
void bitwuzla_add_output(Bitwuzla *bitwuzla, const BitwuzlaTerm *term);

/*------------------------------------------------------------------------*/

struct BzlaBTOR2Parser
{
  BzlaMemMgr *mm;
  Bitwuzla *bitwuzla;
  char *error;
  const char *infile_name;
  Btor2Parser *bfr;
};

typedef struct BzlaBTOR2Parser BzlaBTOR2Parser;

/*------------------------------------------------------------------------*/

static void
perr_btor2(BzlaBTOR2Parser *parser, uint64_t lineno, const char *fmt, ...)
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
        parser->mm, parser->infile_name, lineno, 0, fmt, ap, bytes);
    va_end(ap);
  }
}

/*------------------------------------------------------------------------*/

static BzlaBTOR2Parser *
new_btor2_parser(Bitwuzla *bitwuzla)
{
  BzlaMemMgr *mm = bzla_mem_mgr_new();
  BzlaBTOR2Parser *res;

  BZLA_NEW(mm, res);
  BZLA_CLR(res);

  res->mm       = mm;
  res->bitwuzla = bitwuzla;
  res->bfr      = btor2parser_new();

  return res;
}

static void
delete_btor2_parser(BzlaBTOR2Parser *parser)
{
  BzlaMemMgr *mm;

  mm = parser->mm;
  btor2parser_delete(parser->bfr);
  bzla_mem_freestr(mm, parser->error);
  BZLA_DELETE(mm, parser);
  bzla_mem_mgr_delete(mm);
}

static const char *
parse_btor2_parser(BzlaBTOR2Parser *parser,
                   BzlaIntStack *prefix,
                   FILE *infile,
                   const char *infile_name,
                   FILE *outfile,
                   BzlaParseResult *res)
{
  assert(parser);
  assert(infile);
  assert(infile_name);
  (void) prefix;
  (void) outfile;

  uint32_t i;
  int64_t j, signed_arg, unsigned_arg;
  Btor2LineIterator lit;
  Btor2Line *line;
  BzlaIntHashTable *sortmap;
  BzlaIntHashTable *nodemap;
  BzlaIntHashTableIterator it;
  const BitwuzlaTerm *e[3], *term, *tmp;
  const BitwuzlaSort *sort, *sort_index, *sort_elem;
  BzlaMemMgr *mm;
  BzlaMsg *msg;

  Bitwuzla *bitwuzla = parser->bitwuzla;

  msg = bitwuzla_get_bzla_msg(bitwuzla);

  BZLA_MSG(msg, 1, "parsing %s", infile_name);

  BZLA_CLR(res);

  mm = parser->mm;

  nodemap = 0;
  sortmap = 0;

  parser->infile_name = infile_name;

  /* btor2parser doesn't allow to pass the prefix, we have to rewind to the
   * beginning of the input file instead. */
  if (fseek(infile, 0L, SEEK_SET))
  {
    perr_btor2(parser, 0, "error when rewinding input file");
    goto DONE;
  }

  if (!btor2parser_read_lines(parser->bfr, infile))
  {
    parser->error = bzla_mem_strdup(mm, btor2parser_error(parser->bfr));
    assert(parser->error);
    goto DONE;
  }

  sortmap = bzla_hashint_map_new(mm);
  nodemap = bzla_hashint_map_new(mm);

  lit = btor2parser_iter_init(parser->bfr);
  while ((line = btor2parser_iter_next(&lit)))
  {
    term = 0;
    sort = 0;

    if (line->id > INT32_MAX)
    {
      perr_btor2(parser,
                 line->id,
                 "given id '%" PRId64 "' exceeds INT32_MAX",
                 line->id);
      goto DONE;
    }

    /* sort ----------------------------------------------------------------  */

    if (line->tag != BTOR2_TAG_sort && line->sort.id)
    {
      if (line->sort.id > INT32_MAX)
      {
        perr_btor2(parser,
                   line->id,
                   "given id '%" PRId64 "' exceeds INT32_MAX",
                   line->sort.id);
        goto DONE;
      }
      assert(bzla_hashint_map_contains(sortmap, line->sort.id));
      sort =
          (BitwuzlaSort *) bzla_hashint_map_get(sortmap, line->sort.id)->as_ptr;
      assert(sort);
    }

    /* arguments -----------------------------------------------------------  */

    for (i = 0; i < line->nargs; i++)
    {
      signed_arg   = line->args[i];
      unsigned_arg = signed_arg < 0 ? -signed_arg : signed_arg;
      assert(bzla_hashint_map_contains(nodemap, unsigned_arg));
      tmp = bzla_hashint_map_get(nodemap, unsigned_arg)->as_ptr;
      if (signed_arg < 0)
      {
        e[i] = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_NOT, tmp);
      }
      else
      {
        e[i] = tmp;
      }
      assert(e[i]);
    }

    switch (line->tag)
    {
      case BTOR2_TAG_add:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ADD, e[0], e[1]);
        break;

      case BTOR2_TAG_and:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_AND, e[0], e[1]);
        break;

      case BTOR2_TAG_concat:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_CONCAT, e[0], e[1]);
        break;

      case BTOR2_TAG_const:
        assert(line->nargs == 0);
        assert(line->constant);
        if (!bzla_util_check_bin_to_bv(
                mm, line->constant, line->sort.bitvec.width))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'const' %sort of bw %u",
                     line->constant,
                     line->sort.bitvec.width);
          goto DONE;
        }
        term = bitwuzla_mk_bv_value(
            bitwuzla, sort, line->constant, BITWUZLA_BV_BASE_BIN);
        break;

      case BTOR2_TAG_constd:
        assert(line->nargs == 0);
        assert(line->constant);
        if (!bzla_util_check_dec_to_bv(
                mm, line->constant, line->sort.bitvec.width))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'constd' %sort of bw %u",
                     line->constant,
                     line->sort.bitvec.width);
          goto DONE;
        }
        term = bitwuzla_mk_bv_value(
            bitwuzla, sort, line->constant, BITWUZLA_BV_BASE_DEC);
        break;

      case BTOR2_TAG_consth:
        assert(line->nargs == 0);
        assert(line->constant);
        if (!bzla_util_check_hex_to_bv(
                mm, line->constant, line->sort.bitvec.width))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'consth' %sort of bw %u",
                     line->constant,
                     line->sort.bitvec.width);
          goto DONE;
        }
        term = bitwuzla_mk_bv_value(
            bitwuzla, sort, line->constant, BITWUZLA_BV_BASE_HEX);
        break;

      case BTOR2_TAG_constraint:
        assert(line->nargs == 1);
        bitwuzla_assert(bitwuzla, e[0]);
        break;

      case BTOR2_TAG_dec:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_DEC, e[0]);
        break;

      case BTOR2_TAG_eq:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_EQUAL, e[0], e[1]);
        break;

      case BTOR2_TAG_iff:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_IFF, e[0], e[1]);
        break;

      case BTOR2_TAG_implies:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_IMPLIES, e[0], e[1]);
        break;

      case BTOR2_TAG_inc:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_INC, e[0]);
        break;

      case BTOR2_TAG_input:
        assert(line->nargs == 0);
        term = bitwuzla_mk_const(bitwuzla, sort, line->symbol);
        bitwuzla_set_bzla_id(bitwuzla, term, line->id);
        break;

      case BTOR2_TAG_ite:
        assert(line->nargs == 3);
        term = bitwuzla_mk_term3(bitwuzla, BITWUZLA_KIND_ITE, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_mul:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_MUL, e[0], e[1]);
        break;

      case BTOR2_TAG_nand:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_NAND, e[0], e[1]);
        break;

      case BTOR2_TAG_neq:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_DISTINCT, e[0], e[1]);
        break;

      case BTOR2_TAG_neg:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_NEG, e[0]);
        break;

      case BTOR2_TAG_nor:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_NOR, e[0], e[1]);
        break;

      case BTOR2_TAG_not:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_NOT, e[0]);
        break;

      case BTOR2_TAG_one:
        assert(line->nargs == 0);
        term = bitwuzla_mk_bv_one(bitwuzla, sort);
        break;

      case BTOR2_TAG_ones:
        assert(line->nargs == 0);
        term = bitwuzla_mk_bv_ones(bitwuzla, sort);
        break;

      case BTOR2_TAG_or:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_OR, e[0], e[1]);
        break;

      case BTOR2_TAG_output: bitwuzla_add_output(bitwuzla, e[0]); break;

      case BTOR2_TAG_read:
        assert(line->nargs == 2);
        term =
            bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_ARRAY_SELECT, e[0], e[1]);
        break;

      case BTOR2_TAG_redand:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_REDAND, e[0]);
        break;

      case BTOR2_TAG_redor:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_REDOR, e[0]);
        break;

      case BTOR2_TAG_redxor:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1(bitwuzla, BITWUZLA_KIND_BV_REDXOR, e[0]);
        break;

      case BTOR2_TAG_rol:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ROL, e[0], e[1]);
        break;

      case BTOR2_TAG_ror:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ROR, e[0], e[1]);
        break;

      case BTOR2_TAG_saddo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_SADD_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_sdiv:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SDIV, e[0], e[1]);
        break;

      case BTOR2_TAG_sdivo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_SDIV_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_sext:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1_indexed1(
            bitwuzla, BITWUZLA_KIND_BV_SIGN_EXTEND, e[0], line->args[1]);
        break;

      case BTOR2_TAG_sgt:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SGT, e[0], e[1]);
        break;

      case BTOR2_TAG_sgte:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SGE, e[0], e[1]);
        break;

      case BTOR2_TAG_slice:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1_indexed2(bitwuzla,
                                          BITWUZLA_KIND_BV_EXTRACT,
                                          e[0],
                                          line->args[1],
                                          line->args[2]);
        break;

      case BTOR2_TAG_sll:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SHL, e[0], e[1]);
        break;

      case BTOR2_TAG_slt:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SLT, e[0], e[1]);
        break;

      case BTOR2_TAG_slte:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SLE, e[0], e[1]);
        break;

      case BTOR2_TAG_sort:
        if (line->sort.tag == BTOR2_TAG_SORT_bitvec)
        {
          assert(line->sort.bitvec.width);
          sort = bitwuzla_mk_bv_sort(bitwuzla, line->sort.bitvec.width);
        }
        else
        {
          assert(line->sort.tag == BTOR2_TAG_SORT_array);
          j = line->sort.array.index;
          assert(j);
          if (j > INT32_MAX)
          {
            perr_btor2(parser,
                       line->id,
                       "given id '%" PRId64 "' exceeds INT32_MAX",
                       j);
            goto DONE;
          }
          assert(bzla_hashint_map_contains(sortmap, j));
          sort_index =
              (BitwuzlaSort *) bzla_hashint_map_get(sortmap, j)->as_ptr;
          assert(sort_index);
          j = line->sort.array.element;
          assert(j);
          if (j > INT32_MAX)
          {
            perr_btor2(parser,
                       line->id,
                       "given id '%" PRId64 "' exceeds INT32_MAX",
                       j);
            goto DONE;
          }
          assert(bzla_hashint_map_contains(sortmap, j));
          sort_elem = (BitwuzlaSort *) bzla_hashint_map_get(sortmap, j)->as_ptr;
          assert(sort_elem);
          sort = bitwuzla_mk_array_sort(bitwuzla, sort_index, sort_elem);
        }
        assert(!bzla_hashint_map_contains(sortmap, line->id));
        bzla_hashint_map_add(sortmap, line->id)->as_ptr = (BitwuzlaSort *) sort;
        break;

      case BTOR2_TAG_smod:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SMOD, e[0], e[1]);
        break;

      case BTOR2_TAG_smulo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_SMUL_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_sra:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ASHR, e[0], e[1]);
        break;

      case BTOR2_TAG_srem:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SREM, e[0], e[1]);
        break;

      case BTOR2_TAG_srl:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SHR, e[0], e[1]);
        break;

      case BTOR2_TAG_ssubo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_SSUB_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_sub:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_SUB, e[0], e[1]);
        break;

      case BTOR2_TAG_uaddo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_UADD_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_udiv:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UDIV, e[0], e[1]);
        break;

      case BTOR2_TAG_uext:
        assert(line->nargs == 1);
        term = bitwuzla_mk_term1_indexed1(
            bitwuzla, BITWUZLA_KIND_BV_ZERO_EXTEND, e[0], line->args[1]);
        break;

      case BTOR2_TAG_ugt:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UGT, e[0], e[1]);
        break;

      case BTOR2_TAG_ugte:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UGE, e[0], e[1]);
        break;

      case BTOR2_TAG_ult:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ULT, e[0], e[1]);
        break;

      case BTOR2_TAG_ulte:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_ULE, e[0], e[1]);
        break;

      case BTOR2_TAG_umulo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_UMUL_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_urem:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_UREM, e[0], e[1]);
        break;

      case BTOR2_TAG_usubo:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(
            bitwuzla, BITWUZLA_KIND_BV_USUB_OVERFLOW, e[0], e[1]);
        break;

      case BTOR2_TAG_write:
        assert(line->nargs == 3);
        term = bitwuzla_mk_term3(
            bitwuzla, BITWUZLA_KIND_ARRAY_STORE, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_xnor:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_XNOR, e[0], e[1]);
        break;

      case BTOR2_TAG_xor:
        assert(line->nargs == 2);
        term = bitwuzla_mk_term2(bitwuzla, BITWUZLA_KIND_BV_XOR, e[0], e[1]);
        break;

      case BTOR2_TAG_zero:
        assert(line->nargs == 0);
        term = bitwuzla_mk_bv_zero(bitwuzla, sort);
        break;

      default:
        assert(line->tag == BTOR2_TAG_bad || line->tag == BTOR2_TAG_fair
               || line->tag == BTOR2_TAG_init || line->tag == BTOR2_TAG_justice
               || line->tag == BTOR2_TAG_next || line->tag == BTOR2_TAG_state);
        perr_btor2(parser,
                   line->id,
                   "model checking extensions not supported by bitwuzla, try "
                   "btormc instead");
        goto DONE;
    }

    assert(!sort || !term || bitwuzla_term_get_sort(term) == sort);
    if (term)
    {
      assert(!bzla_hashint_map_contains(nodemap, line->id));
      bzla_hashint_map_add(nodemap, line->id)->as_ptr = (BitwuzlaTerm *) term;
    }
  }
DONE:
  if (nodemap)
  {
    bzla_iter_hashint_init(&it, nodemap);
    while (bzla_iter_hashint_has_next(&it))
    {
      j    = it.cur_pos;
      term = bzla_iter_hashint_next_data(&it)->as_ptr;
    }
    bzla_hashint_map_delete(nodemap);
  }
  if (sortmap)
  {
    bzla_iter_hashint_init(&it, sortmap);
    bzla_hashint_map_delete(sortmap);
  }
  if (res)
  {
    res->status = BITWUZLA_UNKNOWN;
  }
  if (parser->error) return parser->error;
  return 0;
}

static BzlaParserAPI parsebtor2_parser_api = {
    (BzlaInitParser) new_btor2_parser,
    (BzlaResetParser) delete_btor2_parser,
    (BzlaParse) parse_btor2_parser,
};

const BzlaParserAPI *
bzla_parsebtor2_parser_api()
{
  return &parsebtor2_parser_api;
}
