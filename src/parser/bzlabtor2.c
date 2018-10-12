/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2018 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <assert.h>
#include <inttypes.h>
#include <limits.h>

#include "btor2parser/btor2parser.h"
#include "bzlamsg.h"
#include "bzlaparse.h"
#include "bzlatypes.h"
#include "utils/bzlahashint.h"
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

void boolector_set_bzla_id(Bzla *, BoolectorNode *, int32_t);

void boolector_add_output(Bzla *, BoolectorNode *);

/*------------------------------------------------------------------------*/

struct BzlaBTOR2Parser
{
  BzlaMemMgr *mm;
  Bzla *bzla;
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
new_btor2_parser(Bzla *bzla)
{
  BzlaMemMgr *mm = bzla_mem_mgr_new();
  BzlaBTOR2Parser *res;

  BZLA_NEW(mm, res);
  BZLA_CLR(res);

  res->mm   = mm;
  res->bzla = bzla;
  res->bfr  = btor2parser_new();

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
                   BzlaCharStack *prefix,
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

  uint32_t i, bw;
  int64_t j, signed_arg, unsigned_arg;
  Btor2LineIterator lit;
  Btor2Line *line;
  BzlaIntHashTable *sortmap;
  BzlaIntHashTable *nodemap;
  BzlaIntHashTableIterator it;
  BoolectorNode *e[3], *node, *tmp;
  BoolectorSort sort, sort_index, sort_elem;
  BzlaMemMgr *mm;
  BzlaMsg *msg;
  Bzla *bzla;
  bool found_arrays, found_lambdas;

  bzla = parser->bzla;
  msg  = boolector_get_bzla_msg(bzla);

  BZLA_MSG(msg, 1, "parsing %s", infile_name);

  BZLA_CLR(res);

  mm = parser->mm;

  found_arrays  = false;
  found_lambdas = false;

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
    node = 0;
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
      sort = bzla_hashint_map_get(sortmap, line->sort.id)->as_ptr;
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
        e[i] = boolector_bv_not(bzla, tmp);
        boolector_release(bzla, tmp);
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
        node = boolector_bv_add(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_and:
        assert(line->nargs == 2);
        node = boolector_bv_and(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_concat:
        assert(line->nargs == 2);
        node = boolector_concat(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_const:
        assert(line->nargs == 0);
        assert(line->constant);
        bw = line->sort.bitvec.width;
        if (!bzla_util_check_bin_to_bv(mm, line->constant, bw))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'const' %sort of bw %u",
                     line->constant,
                     bw);
          goto DONE;
        }
        node = boolector_const(bzla, line->constant);
        break;

      case BTOR2_TAG_constd:
        assert(line->nargs == 0);
        assert(line->constant);
        bw = line->sort.bitvec.width;
        if (!bzla_util_check_dec_to_bv(mm, line->constant, bw))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'constd' %sort of bw %u",
                     line->constant,
                     bw);
          goto DONE;
        }
        node = boolector_constd(bzla, sort, line->constant);
        break;

      case BTOR2_TAG_consth:
        assert(line->nargs == 0);
        assert(line->constant);
        bw = line->sort.bitvec.width;
        if (!bzla_util_check_hex_to_bv(mm, line->constant, bw))
        {
          perr_btor2(parser,
                     line->id,
                     "invalid 'consth' %sort of bw %u",
                     line->constant,
                     bw);
          goto DONE;
        }
        node = boolector_consth(bzla, sort, line->constant);
        break;

      case BTOR2_TAG_constraint:
        assert(line->nargs == 1);
        boolector_assert(bzla, e[0]);
        break;

      case BTOR2_TAG_dec:
        assert(line->nargs == 1);
        node = boolector_dec(bzla, e[0]);
        break;

      case BTOR2_TAG_eq:
        assert(line->nargs == 2);
        node = boolector_eq(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_iff:
        assert(line->nargs == 2);
        node = boolector_iff(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_implies:
        assert(line->nargs == 2);
        node = boolector_implies(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_inc:
        assert(line->nargs == 1);
        node = boolector_inc(bzla, e[0]);
        break;

      case BTOR2_TAG_input:
        assert(line->nargs == 0);
        if (boolector_is_bv_sort(bzla, sort))
          node = boolector_var(bzla, sort, line->symbol);
        else
        {
          node         = boolector_array(bzla, sort, line->symbol);
          found_arrays = true;
        }
        boolector_set_bzla_id(bzla, node, line->id);
        break;

      case BTOR2_TAG_ite:
        assert(line->nargs == 3);
        node = boolector_cond(bzla, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_mul:
        assert(line->nargs == 2);
        node = boolector_bv_mul(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_nand:
        assert(line->nargs == 2);
        node = boolector_bv_nand(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_neq:
        assert(line->nargs == 2);
        node = boolector_ne(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_neg:
        assert(line->nargs == 1);
        node = boolector_bv_neg(bzla, e[0]);
        break;

      case BTOR2_TAG_nor:
        assert(line->nargs == 2);
        node = boolector_bv_nor(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_not:
        assert(line->nargs == 1);
        node = boolector_bv_not(bzla, e[0]);
        break;

      case BTOR2_TAG_one:
        assert(line->nargs == 0);
        node = boolector_one(bzla, sort);
        break;

      case BTOR2_TAG_ones:
        assert(line->nargs == 0);
        node = boolector_ones(bzla, sort);
        break;

      case BTOR2_TAG_or:
        assert(line->nargs == 2);
        node = boolector_bv_or(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_output: boolector_add_output(bzla, e[0]); break;

      case BTOR2_TAG_read:
        assert(line->nargs == 2);
        node = boolector_read(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_redand:
        assert(line->nargs == 1);
        node = boolector_bv_redand(bzla, e[0]);
        break;

      case BTOR2_TAG_redor:
        assert(line->nargs == 1);
        node = boolector_bv_redor(bzla, e[0]);
        break;

      case BTOR2_TAG_redxor:
        assert(line->nargs == 1);
        node = boolector_bv_redxor(bzla, e[0]);
        break;

      case BTOR2_TAG_rol:
        assert(line->nargs == 2);
        node = boolector_bv_rol(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_ror:
        assert(line->nargs == 2);
        node = boolector_bv_ror(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_saddo:
        assert(line->nargs == 2);
        node = boolector_bv_saddo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sdiv:
        assert(line->nargs == 2);
        node = boolector_sdiv(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sdivo:
        assert(line->nargs == 2);
        node = boolector_sdivo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sext:
        assert(line->nargs == 1);
        node = boolector_bv_sext(bzla, e[0], line->args[1]);
        break;

      case BTOR2_TAG_sgt:
        assert(line->nargs == 2);
        node = boolector_bv_sgt(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sgte:
        assert(line->nargs == 2);
        node = boolector_bv_sgte(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_slice:
        assert(line->nargs == 1);
        node = boolector_bv_slice(bzla, e[0], line->args[1], line->args[2]);
        break;

      case BTOR2_TAG_sll:
        assert(line->nargs == 2);
        node = boolector_bv_sll(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_slt:
        assert(line->nargs == 2);
        node = boolector_bv_slt(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_slte:
        assert(line->nargs == 2);
        node = boolector_bv_slte(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sort:
        if (line->sort.tag == BTOR2_TAG_SORT_bitvec)
        {
          assert(line->sort.bitvec.width);
          sort = boolector_bv_sort(bzla, line->sort.bitvec.width);
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
          sort_index = (BoolectorSort) bzla_hashint_map_get(sortmap, j)->as_ptr;
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
          sort_elem = (BoolectorSort) bzla_hashint_map_get(sortmap, j)->as_ptr;
          assert(sort_elem);
          sort = boolector_array_sort(bzla, sort_index, sort_elem);
        }
        assert(!bzla_hashint_map_contains(sortmap, line->id));
        bzla_hashint_map_add(sortmap, line->id)->as_ptr = sort;
        break;

      case BTOR2_TAG_smod:
        assert(line->nargs == 2);
        node = boolector_smod(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_smulo:
        assert(line->nargs == 2);
        node = boolector_bv_smulo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sra:
        assert(line->nargs == 2);
        node = boolector_bv_sra(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_srem:
        assert(line->nargs == 2);
        node = boolector_srem(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_srl:
        assert(line->nargs == 2);
        node = boolector_bv_srl(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_ssubo:
        assert(line->nargs == 2);
        node = boolector_bv_ssubo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_sub:
        assert(line->nargs == 2);
        node = boolector_bv_sub(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_uaddo:
        assert(line->nargs == 2);
        node = boolector_bv_uaddo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_udiv:
        assert(line->nargs == 2);
        node = boolector_udiv(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_uext:
        assert(line->nargs == 1);
        node = boolector_bv_uext(bzla, e[0], line->args[1]);
        break;

      case BTOR2_TAG_ugt:
        assert(line->nargs == 2);
        node = boolector_bv_ugt(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_ugte:
        assert(line->nargs == 2);
        node = boolector_bv_ugte(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_ult:
        assert(line->nargs == 2);
        node = boolector_bv_ult(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_ulte:
        assert(line->nargs == 2);
        node = boolector_bv_ulte(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_umulo:
        assert(line->nargs == 2);
        node = boolector_bv_umulo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_urem:
        assert(line->nargs == 2);
        node = boolector_urem(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_usubo:
        assert(line->nargs == 2);
        node = boolector_bv_usubo(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_write:
        assert(line->nargs == 3);
        node = boolector_write(bzla, e[0], e[1], e[2]);
        break;

      case BTOR2_TAG_xnor:
        assert(line->nargs == 2);
        node = boolector_bv_xnor(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_xor:
        assert(line->nargs == 2);
        node = boolector_bv_xor(bzla, e[0], e[1]);
        break;

      case BTOR2_TAG_zero:
        assert(line->nargs == 0);
        node = boolector_zero(bzla, sort);
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
    assert(!sort || !node || boolector_get_sort(bzla, node) == sort);
    if (node)
    {
      assert(!bzla_hashint_map_contains(nodemap, line->id));
      bzla_hashint_map_add(nodemap, line->id)->as_ptr = node;
    }
  }
DONE:
  if (nodemap)
  {
    bzla_iter_hashint_init(&it, nodemap);
    while (bzla_iter_hashint_has_next(&it))
    {
      j    = it.cur_pos;
      node = bzla_iter_hashint_next_data(&it)->as_ptr;
      boolector_release(bzla, node);
    }
    bzla_hashint_map_delete(nodemap);
  }
  if (sortmap)
  {
    bzla_iter_hashint_init(&it, sortmap);
    while (bzla_iter_hashint_has_next(&it))
      boolector_release_sort(bzla, bzla_iter_hashint_next_data(&it)->as_ptr);
    bzla_hashint_map_delete(sortmap);
  }
  if (res)
  {
    if (found_arrays || found_lambdas)
      res->logic = BZLA_LOGIC_QF_AUFBV;
    else
      res->logic = BZLA_LOGIC_QF_BV;
    res->status = BOOLECTOR_UNKNOWN;
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
