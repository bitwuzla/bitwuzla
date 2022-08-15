/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlacore.h"
#include "bzlaexit.h"
#include "bzlaexp.h"
#include "bzlasort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#ifndef NDEBUG
#include "bzlaclone.h"
#endif
#include <ctype.h>
#include <limits.h>

#include "bzladumpsmt.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"

struct BzlaSMTDumpContext
{
  Bzla *bzla;
  BzlaPtrHashTable *dump;
  BzlaPtrHashTable *dumped;
  BzlaPtrHashTable *boolean;
  BzlaPtrHashTable *stores;
  BzlaPtrHashTable *idtab;
  BzlaPtrHashTable *roots;
  BzlaPtrHashTable *const_cache;
  FILE *file;
  uint32_t maxid;
  uint32_t pretty_print;
  uint32_t open_lets;
  uint32_t indent;
  bool newline;
};

typedef struct BzlaSMTDumpContext BzlaSMTDumpContext;

static BzlaSMTDumpContext *
new_smt_dump_context(Bzla *bzla, FILE *file)
{
  BzlaSMTDumpContext *sdc;
  BZLA_CNEW(bzla->mm, sdc);

  sdc->bzla        = bzla;
  sdc->dump        = bzla_hashptr_table_new(bzla->mm,
                                     (BzlaHashPtr) bzla_node_hash_by_id,
                                     (BzlaCmpPtr) bzla_node_compare_by_id);
  sdc->dumped      = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  sdc->boolean     = bzla_hashptr_table_new(bzla->mm,
                                        (BzlaHashPtr) bzla_node_hash_by_id,
                                        (BzlaCmpPtr) bzla_node_compare_by_id);
  sdc->stores      = bzla_hashptr_table_new(bzla->mm,
                                       (BzlaHashPtr) bzla_node_hash_by_id,
                                       (BzlaCmpPtr) bzla_node_compare_by_id);
  sdc->idtab       = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  sdc->const_cache = bzla_hashptr_table_new(
      bzla->mm, (BzlaHashPtr) bzla_bv_hash, (BzlaCmpPtr) bzla_bv_compare);
  /* use pointer for hashing and comparison */
  sdc->roots        = bzla_hashptr_table_new(bzla->mm, 0, 0);
  sdc->file         = file;
  sdc->maxid        = 1;
  sdc->pretty_print = bzla_opt_get(bzla, BZLA_OPT_PRETTY_PRINT);
  sdc->newline      = sdc->pretty_print == 1;
  return sdc;
}

static void
delete_smt_dump_context(BzlaSMTDumpContext *sdc)
{
  BzlaPtrHashTableIterator it;

  bzla_hashptr_table_delete(sdc->dump);
  bzla_hashptr_table_delete(sdc->dumped);
  bzla_hashptr_table_delete(sdc->boolean);
  bzla_hashptr_table_delete(sdc->stores);
  bzla_hashptr_table_delete(sdc->idtab);

  bzla_iter_hashptr_init(&it, sdc->roots);
  while (bzla_iter_hashptr_has_next(&it))
    bzla_node_release(sdc->bzla, bzla_iter_hashptr_next(&it));
  bzla_hashptr_table_delete(sdc->roots);

  bzla_iter_hashptr_init(&it, sdc->const_cache);
  while (bzla_iter_hashptr_has_next(&it))
  {
    assert(it.bucket->data.as_str);
    bzla_mem_freestr(sdc->bzla->mm, it.bucket->data.as_str);
    bzla_bv_free(sdc->bzla->mm, (BzlaBitVector *) bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(sdc->const_cache);
  BZLA_DELETE(sdc->bzla->mm, sdc);
}

static void
add_root_to_smt_dump_context(BzlaSMTDumpContext *sdc, BzlaNode *root)
{
  if (!bzla_hashptr_table_get(sdc->roots, root))
    bzla_hashptr_table_add(sdc->roots, bzla_node_copy(sdc->bzla, root));
}

static int32_t
cmp_node_id(const void *p, const void *q)
{
  BzlaNode *a = *(BzlaNode **) p;
  BzlaNode *b = *(BzlaNode **) q;
  return a->id - b->id;
}

static uint32_t
smt_id(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(sdc);
  assert(exp);
  assert(bzla_node_is_regular(exp));

  BzlaPtrHashBucket *b;
  int32_t id;

  if (sdc->pretty_print)
  {
    b = bzla_hashptr_table_get(sdc->idtab, exp);

    if (!b)
    {
      b              = bzla_hashptr_table_add(sdc->idtab, exp);
      b->data.as_int = sdc->maxid++;
    }
    return b->data.as_int;
  }
  id = bzla_node_get_bzla_id(exp);
  if (id) return id;
  return exp->id;
}

static bool
symbol_needs_quotes(const char *sym)
{
  char ch;
  size_t i, len;

  len = strlen(sym);

  /* already quoted */
  if (sym[0] == '|' && sym[len - 1] == '|') return false;

  for (i = 0; i < len; i++)
  {
    ch = sym[i];
    if ((ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122)
        || (ch >= 48 && ch <= 57) || ch == '~' || ch == '!' || ch == '@'
        || ch == '$' || ch == '%' || ch == '^' || ch == '&' || ch == '*'
        || ch == '_' || ch == '-' || ch == '+' || ch == '=' || ch == '<'
        || ch == '>' || ch == '.' || ch == '?' || ch == '/')
      continue;
    return true;
  }
  return false;
}

static void
dump_smt_id(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(sdc);
  assert(exp);

  const char *type, *sym;

  exp = bzla_node_real_addr(exp);

  switch (exp->kind)
  {
    case BZLA_VAR_NODE: type = "v"; goto DUMP_SYMBOL;

    case BZLA_PARAM_NODE:
      type = "x";
    DUMP_SYMBOL:
      sym = bzla_node_get_symbol(sdc->bzla, exp);
      if (sym && !isdigit((int32_t) sym[0]))
      {
        if (symbol_needs_quotes(sym))
          fprintf(sdc->file, "|%s|", sym);
        else
          fputs(sym, sdc->file);
        return;
      }
      break;

    case BZLA_UF_NODE: type = "uf"; goto DUMP_SYMBOL;

    case BZLA_LAMBDA_NODE: type = "f"; goto DUMP_SYMBOL;

    default: type = "$e";
  }

  fprintf(sdc->file, "%s%u", type, smt_id(sdc, exp));
}

static bool
is_const(const BzlaNode *exp)
{
  return bzla_node_is_bv_const(exp) || bzla_node_is_fp_const(exp)
         || bzla_node_is_rm_const(exp);
}

static bool
is_boolean(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  exp = bzla_node_real_addr(exp);
  return bzla_hashptr_table_get(sdc->boolean, exp) != 0;
}

void
bzla_dumpsmt_dump_const_rm_value(Bzla *bzla,
                                 const BzlaBitVector *bits,
                                 FILE *file)
{
  assert(bzla);
  assert(bits);
  (void) bzla;

  BzlaRoundingMode rm = bzla_bv_to_uint64(bits);
  assert(rm < BZLA_RM_MAX);

  switch (rm)
  {
    case BZLA_RM_RNA: fprintf(file, "RNA"); break;
    case BZLA_RM_RNE: fprintf(file, "RNE"); break;
    case BZLA_RM_RTN: fprintf(file, "RTN"); break;
    case BZLA_RM_RTP: fprintf(file, "RTP"); break;
    default: assert(rm == BZLA_RM_RTZ); fprintf(file, "RTZ");
  }
}

void
bzla_dumpsmt_dump_const_fp_value(Bzla *bzla,
                                 const BzlaBitVector *bits,
                                 uint32_t esize,
                                 uint32_t ssize,
                                 FILE *file)
{
  assert(bzla);
  assert(bits);
  (void) esize;

  BzlaBitVector *sign, *exp, *sig;
  char *sign_str, *exp_str, *sig_str;
  uint32_t msb = bzla_bv_get_width(bits) - 1;

  sign = bzla_bv_slice(bzla->mm, bits, msb, msb);
  exp  = bzla_bv_slice(bzla->mm, bits, msb - 1, ssize - 1);
  assert(bzla_bv_get_width(exp) == esize);
  sig = bzla_bv_slice(bzla->mm, bits, ssize - 2, 0);
  assert(bzla_bv_get_width(sig) == ssize - 1);

  sign_str = bzla_bv_to_char(bzla->mm, sign);
  exp_str  = bzla_bv_to_char(bzla->mm, exp);
  sig_str  = bzla_bv_to_char(bzla->mm, sig);
  fprintf(file, "(fp #b%s #b%s #b%s)", sign_str, exp_str, sig_str);

  bzla_mem_freestr(bzla->mm, sign_str);
  bzla_mem_freestr(bzla->mm, exp_str);
  bzla_mem_freestr(bzla->mm, sig_str);
  bzla_bv_free(bzla->mm, sign);
  bzla_bv_free(bzla->mm, exp);
  bzla_bv_free(bzla->mm, sig);
}

void
bzla_dumpsmt_dump_const_bv_value(Bzla *bzla,
                                 const BzlaBitVector *bits,
                                 uint32_t base,
                                 FILE *file)
{
  assert(bzla);
  assert(bits);
  assert(base == BZLA_OUTPUT_BASE_BIN || base == BZLA_OUTPUT_BASE_DEC
         || base == BZLA_OUTPUT_BASE_HEX);

  char *val;

  /* SMT-LIB v1.2 only supports decimal output */
  if (base == BZLA_OUTPUT_BASE_DEC)
  {
    val = bzla_bv_to_dec_char(bzla->mm, bits);
    fprintf(file, "(_ bv%s %d)", val, bzla_bv_get_width(bits));
  }
  else if (base == BZLA_OUTPUT_BASE_HEX && bzla_bv_get_width(bits) % 4 == 0)
  {
    val = bzla_bv_to_hex_char(bzla->mm, bits);
    fprintf(file, "#x%s", val);
  }
  else
  {
    val = bzla_bv_to_char(bzla->mm, bits);
    fprintf(file, "#b%s", val);
  }
  bzla_mem_freestr(bzla->mm, val);
}

static void
dump_const_bv_value_aux_smt(BzlaSMTDumpContext *sdc, BzlaBitVector *bits)
{
  assert(sdc);
  assert(bits);

  uint32_t base;
  FILE *file;
  char *val;
  BzlaPtrHashBucket *b;

  base = bzla_opt_get(sdc->bzla, BZLA_OPT_OUTPUT_NUMBER_FORMAT);
  file = sdc->file;

  /* converting consts to decimal/hex is costly. we now always dump the value of
   * constants. in order to avoid computing the same value again we cache
   * the result of the first computation and print the cached value in
   * subsequent calls. */
  if (base == BZLA_OUTPUT_BASE_DEC)
  {
    if ((b = bzla_hashptr_table_get(sdc->const_cache, bits)))
    {
      val = b->data.as_str;
      assert(val);
    }
    else
    {
      val = bzla_bv_to_dec_char(sdc->bzla->mm, bits);
      bzla_hashptr_table_add(sdc->const_cache,
                             bzla_bv_copy(sdc->bzla->mm, bits))
          ->data.as_str = val;
    }
    fprintf(file, "(_ bv%s %d)", val, bzla_bv_get_width(bits));
  }
  else if (base == BZLA_OUTPUT_BASE_HEX && bzla_bv_get_width(bits) % 4 == 0)
  {
    if ((b = bzla_hashptr_table_get(sdc->const_cache, bits)))
    {
      val = b->data.as_str;
      assert(val);
    }
    else
    {
      val = bzla_bv_to_hex_char(sdc->bzla->mm, bits);
      bzla_hashptr_table_add(sdc->const_cache,
                             bzla_bv_copy(sdc->bzla->mm, bits))
          ->data.as_str = val;
    }
    fprintf(file, "#x%s", val);
  }
  else
  {
    bzla_dumpsmt_dump_const_bv_value(sdc->bzla, bits, base, file);
  }
}

void
bzla_dumpsmt_dump_sort(BzlaSort *sort, FILE *file)
{
  uint32_t i;
  const char *fmt;

  switch (sort->kind)
  {
    case BZLA_BOOL_SORT: fputs("Bool", file); break;

    case BZLA_BV_SORT:
      fmt = "(_ BitVec %d)";
      fprintf(file, fmt, sort->bitvec.width);
      break;

    case BZLA_ARRAY_SORT:
      fprintf(file, "(Array ");
      bzla_dumpsmt_dump_sort(sort->array.index, file);
      fprintf(file, " ");
      bzla_dumpsmt_dump_sort(sort->array.element, file);
      fprintf(file, ")");
      break;

    case BZLA_FP_SORT:
      fmt = "(_ FloatingPoint %u %u)";
      fprintf(file, fmt, sort->fp.width_exp, sort->fp.width_sig);
      break;

    case BZLA_FUN_SORT:
      if (sort->fun.is_array)
      {
        assert(sort->fun.domain->tuple.num_elements == 1);
        fprintf(file, "(Array ");
        bzla_dumpsmt_dump_sort(sort->fun.domain->tuple.elements[0], file);
        fprintf(file, " ");
        bzla_dumpsmt_dump_sort(sort->fun.codomain, file);
        fprintf(file, ")");
      }
      else
      {
        /* print domain */
        fputc('(', file);
        if (sort->fun.domain->kind == BZLA_TUPLE_SORT)
        {
          for (i = 0; i < sort->fun.domain->tuple.num_elements; i++)
          {
            bzla_dumpsmt_dump_sort(sort->fun.domain->tuple.elements[i], file);
            if (i < sort->fun.domain->tuple.num_elements - 1) fputc(' ', file);
          }
        }
        else
          bzla_dumpsmt_dump_sort(sort->fun.domain, file);
        fputc(')', file);
        fputc(' ', file);

        /* print co-domain */
        bzla_dumpsmt_dump_sort(sort->fun.codomain, file);
      }
      break;

    case BZLA_RM_SORT: fprintf(file, "RoundingMode"); break;

    default: assert(0);
  }
}

void
bzla_dumpsmt_dump_sort_node(BzlaNode *exp, FILE *file)
{
  assert(exp);
  assert(file);

  BzlaSort *sort;
  exp  = bzla_node_real_addr(exp);
  if (bzla_node_is_array(exp))
  {
    BzlaSortId sort_id = bzla_node_get_sort_id(exp);
    BzlaSortId asort =
        bzla_sort_array(exp->bzla,
                        bzla_sort_array_get_index(exp->bzla, sort_id),
                        bzla_sort_array_get_element(exp->bzla, sort_id));
    sort = bzla_sort_get_by_id(exp->bzla, asort);
    bzla_dumpsmt_dump_sort(sort, file);
    bzla_sort_release(exp->bzla, asort);
  }
  else
  {
    sort = bzla_sort_get_by_id(exp->bzla, bzla_node_get_sort_id(exp));
    bzla_dumpsmt_dump_sort(sort, file);
  }
}

#if 0
static void
extract_store (BzlaSMTDumpContext * sdc, BzlaNode * exp,
	       BzlaNode ** index, BzlaNode ** value, BzlaNode ** array)
{
  BzlaNode *ite, *eq, *apply;

  if (!bzla_node_is_lambda (exp))
    return;

  if (((BzlaLambdaNode *) exp)->num_params != 1)
    return;

  if (!bzla_node_is_bv_cond (exp->e[1]))
    return;

  ite = exp->e[1];
  if (bzla_node_is_inverted (ite))
    return;

  if (!bzla_node_is_bv_eq (ite->e[0]))
    return;

  /* check ite condition */
  eq = ite->e[0];
  if (bzla_node_is_inverted (eq))
    return;

  if (!eq->parameterized)
    return;

  /* check if branch */
  if (bzla_node_real_addr (ite->e[1])->parameterized)
    return;

  /* check else branch */
  if (!bzla_node_real_addr (ite->e[2])->parameterized)
    return;

  if (!bzla_node_is_apply (ite->e[2]))
    return;

  apply = ite->e[2];
  if (bzla_node_is_inverted (apply))
    return;

  if (!bzla_node_is_uf_array (apply->e[0])
      && !bzla_hashptr_table_get (sdc->stores, apply->e[0]))
    return;

  if (!bzla_node_is_param (apply->e[1]->e[0]))
    return;

  *index = bzla_node_real_addr (eq->e[0])->parameterized ? eq->e[1] : eq->e[0];
  *value = ite->e[1];
  *array = apply->e[0];
}
#endif

#define PUSH_DUMP_NODE(                                      \
    exp, expect_bv, expect_bool, add_space, zero_ext, depth) \
  {                                                          \
    BZLA_PUSH_STACK(dump, exp);                              \
    BZLA_PUSH_STACK(expect_bv_stack, expect_bv);             \
    BZLA_PUSH_STACK(expect_bool_stack, expect_bool);         \
    BZLA_PUSH_STACK(add_space_stack, add_space);             \
    BZLA_PUSH_STACK(zero_extend_stack, zero_ext);            \
    BZLA_PUSH_STACK(depth_stack, depth);                     \
  }

static const char *g_kind2smt[BZLA_NUM_OPS_NODE] = {
    [BZLA_INVALID_NODE]       = "invalid",
    [BZLA_BV_CONST_NODE]      = "bvconst",
    [BZLA_FP_CONST_NODE]      = "fpconst",
    [BZLA_RM_CONST_NODE]      = "rmconst",
    [BZLA_VAR_NODE]           = "var",
    [BZLA_PARAM_NODE]         = "param",
    [BZLA_BV_SLICE_NODE]      = "extract",
    [BZLA_FP_ABS_NODE]        = "fp.abs",
    [BZLA_FP_IS_INF_NODE]     = "fp.isInfinite",
    [BZLA_FP_IS_NAN_NODE]     = "fp.isNaN",
    [BZLA_FP_IS_NEG_NODE]     = "fp.isNeg",
    [BZLA_FP_IS_NORM_NODE]    = "fp.isNormal",
    [BZLA_FP_IS_POS_NODE]     = "fp.isPositive",
    [BZLA_FP_IS_SUBNORM_NODE] = "fp.isSubnormal",
    [BZLA_FP_IS_ZERO_NODE]    = "fp.isZero",
    [BZLA_FP_NEG_NODE]        = "fp.neg",
    [BZLA_FP_TO_FP_BV_NODE]   = "to_fp",
    [BZLA_BV_AND_NODE]        = "bvand",
    [BZLA_BV_EQ_NODE]         = "=",
    [BZLA_BV_ADD_NODE]        = "bvadd",
    [BZLA_BV_MUL_NODE]        = "bvmul",
    [BZLA_BV_ULT_NODE]        = "bvult",
    [BZLA_BV_SLL_NODE]        = "bvshl",
    [BZLA_BV_SLT_NODE]        = "bvslt",
    [BZLA_BV_SRL_NODE]        = "bvlshr",
    [BZLA_BV_UDIV_NODE]       = "bvudiv",
    [BZLA_BV_UREM_NODE]       = "bvurem",
    [BZLA_BV_CONCAT_NODE]     = "concat",
    [BZLA_FP_EQ_NODE]         = "=",
    [BZLA_FP_LTE_NODE]        = "fp.leq",
    [BZLA_FP_LT_NODE]         = "fp.lt",
    [BZLA_FP_MIN_NODE]        = "fp.min",
    [BZLA_FP_MAX_NODE]        = "fp.max",
    [BZLA_FP_SQRT_NODE]       = "fp.sqrt",
    [BZLA_FP_REM_NODE]        = "fp.rem",
    [BZLA_FP_RTI_NODE]        = "fp.roundToIntegral",
    [BZLA_FP_TO_SBV_NODE]     = "fp.to_sbv",
    [BZLA_FP_TO_UBV_NODE]     = "fp.to_ubv",
    [BZLA_FP_TO_FP_FP_NODE]   = "to_fp",
    [BZLA_FP_TO_FP_SBV_NODE]  = "to_fp",
    [BZLA_FP_TO_FP_UBV_NODE]  = "to_fp_unsigned",
    [BZLA_RM_EQ_NODE]         = "=",
    [BZLA_FUN_EQ_NODE]        = "=",
    [BZLA_APPLY_NODE]         = "apply",
    [BZLA_FORALL_NODE]        = "forall",
    [BZLA_EXISTS_NODE]        = "exists",
    [BZLA_LAMBDA_NODE]        = "lambda",
    [BZLA_COND_NODE]          = "ite",
    [BZLA_FP_ADD_NODE]        = "fp.add",
    [BZLA_FP_MUL_NODE]        = "fp.mul",
    [BZLA_FP_DIV_NODE]        = "fp.div",
    [BZLA_ARGS_NODE]          = "args",
    [BZLA_UPDATE_NODE]        = "update",
    [BZLA_FP_FMA_NODE]        = "fp.fma",
    [BZLA_UF_NODE]            = "uf",
};

static void
collect_and_children(BzlaSMTDumpContext *sdc,
                     BzlaNode *exp,
                     BzlaNodePtrStack *children)
{
  assert(children);
  assert(BZLA_EMPTY_STACK(*children));
  assert(bzla_node_is_bv_and(exp));

  bool skip;
  uint32_t i;
  int32_t id;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrQueue visit;
  BzlaPtrHashBucket *b;
  BzlaIntHashTable *cache;

  cache = bzla_hashint_table_new(sdc->bzla->mm);

  /* get children of multi-input and */
  BZLA_INIT_QUEUE(sdc->bzla->mm, visit);
  for (i = 0; i < bzla_node_real_addr(exp)->arity; i++)
    BZLA_ENQUEUE(visit, bzla_node_real_addr(exp)->e[i]);
  while (!BZLA_EMPTY_QUEUE(visit))
  {
    cur      = BZLA_DEQUEUE(visit);
    real_cur = bzla_node_real_addr(cur);
    id       = bzla_node_get_id(cur);

    skip = bzla_hashint_table_contains(cache, id);
    if (!skip)
    {
      bzla_hashint_table_add(cache, id);
      b = bzla_hashptr_table_get(sdc->dump, real_cur);
    }
    else
      b = 0;

    if (!bzla_node_is_bv_and(real_cur) || (b && b->data.as_int > 1)
        || bzla_node_is_inverted(cur) || skip)
    {
      BZLA_PUSH_STACK(*children, cur);
      continue;
    }

    assert(!bzla_hashptr_table_get(sdc->dumped, real_cur));
    bzla_hashptr_table_add(sdc->dumped, real_cur);
    for (i = 0; i < real_cur->arity; i++) BZLA_ENQUEUE(visit, real_cur->e[i]);
  }
  BZLA_RELEASE_QUEUE(visit);
  bzla_hashint_table_delete(cache);
}

static void
print_indent(BzlaSMTDumpContext *sdc)
{
  uint32_t i;
  for (i = 0; i < sdc->indent; i++) fputc(' ', sdc->file);
}

static inline void
open_sexp(BzlaSMTDumpContext *sdc)
{
  if (sdc->pretty_print && sdc->indent > 0 && sdc->newline)
  {
    fputc('\n', sdc->file);
    print_indent(sdc);
  }
  fputc('(', sdc->file);
  sdc->indent++;
}

static inline void
close_sexp(BzlaSMTDumpContext *sdc)
{
  fputc(')', sdc->file);
  sdc->indent--;
}

static void recursively_dump_exp_let_smt(BzlaSMTDumpContext *sdc,
                                         BzlaNode *exp,
                                         bool expect_bv,
                                         uint32_t depth_limit);

static void
expand_lambda(BzlaSMTDumpContext *sdc,
              BzlaNode *exp,
              BzlaNodePtrStack *indices,
              BzlaNodePtrStack *values,
              BzlaNode **base_array)
{
  assert(bzla_node_is_lambda(exp));
  assert(bzla_node_is_array(exp));

  uint32_t i;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *static_rho;
  BzlaNode *index, *value, *cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *cache;

  BZLA_INIT_STACK(sdc->bzla->mm, visit);

  cache = bzla_hashint_table_new(sdc->bzla->mm);

  *base_array = 0;
  BZLA_PUSH_STACK(visit, exp);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)
        || (!cur->parameterized && !bzla_node_is_array(cur)))
      continue;

    bzla_hashint_table_add(cache, cur->id);

    if (bzla_node_is_lambda(cur))
    {
      assert(bzla_node_is_array(cur));
      static_rho = bzla_node_lambda_get_static_rho(cur);
      assert(static_rho);

      bzla_iter_hashptr_init(&it, static_rho);
      while (bzla_iter_hashptr_has_next(&it))
      {
        value = it.bucket->data.as_ptr;
        index = bzla_iter_hashptr_next(&it);
        assert(bzla_node_is_args(index));
        assert(bzla_node_args_get_arity(sdc->bzla, index) == 1);
        BZLA_PUSH_STACK(*indices, index->e[0]);
        BZLA_PUSH_STACK(*values, value);
      }
    }
    else if (bzla_node_is_array(cur))
    {
      assert(!*base_array);
      *base_array = cur;
      continue;
    }

    if (!bzla_hashptr_table_get(sdc->dumped, cur))
      bzla_hashptr_table_add(sdc->dumped, cur);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }
  assert(*base_array);
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(cache);
}

static void
recursively_dump_exp_smt(BzlaSMTDumpContext *sdc,
                         BzlaNode *exp,
                         int32_t expect_bv,
                         uint32_t depth_limit)
{
  assert(sdc);
  assert(exp);
  assert(bzla_hashptr_table_get(sdc->dump, bzla_node_real_addr(exp)));

  uint32_t depth;
  bool is_bool, expect_bool;
  uint32_t pad, i, zero_extend;
  int32_t add_space;
  BzlaBitVector *bits;
  const char *op;
  BzlaNode *tmp, *real_exp;
  BzlaArgsIterator it;
  BzlaNodeIterator node_it;
  BzlaNodePtrStack dump, args, indices, values;
  BzlaIntStack expect_bv_stack, expect_bool_stack, depth_stack;
  BzlaIntStack add_space_stack, zero_extend_stack;
  BzlaPtrHashTable *visited;
  BzlaMemMgr *mm;

  mm      = sdc->bzla->mm;
  visited = bzla_hashptr_table_new(mm, 0, 0);
  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, dump);
  BZLA_INIT_STACK(mm, expect_bv_stack);
  BZLA_INIT_STACK(mm, expect_bool_stack);
  BZLA_INIT_STACK(mm, add_space_stack);
  BZLA_INIT_STACK(mm, zero_extend_stack);
  BZLA_INIT_STACK(mm, depth_stack);
  BZLA_INIT_STACK(mm, indices);
  BZLA_INIT_STACK(mm, values);

  PUSH_DUMP_NODE(exp, expect_bv, 0, 0, 0, 0);
  while (!BZLA_EMPTY_STACK(dump))
  {
    assert(!BZLA_EMPTY_STACK(expect_bv_stack));
    assert(!BZLA_EMPTY_STACK(expect_bool_stack));
    assert(!BZLA_EMPTY_STACK(add_space_stack));
    assert(!BZLA_EMPTY_STACK(zero_extend_stack));
    assert(!BZLA_EMPTY_STACK(depth_stack));
    assert(BZLA_COUNT_STACK(expect_bv_stack)
           == BZLA_COUNT_STACK(expect_bool_stack));
    assert(BZLA_COUNT_STACK(expect_bool_stack)
           == BZLA_COUNT_STACK(add_space_stack));
    assert(BZLA_COUNT_STACK(add_space_stack)
           == BZLA_COUNT_STACK(zero_extend_stack));
    assert(BZLA_COUNT_STACK(zero_extend_stack)
           == BZLA_COUNT_STACK(depth_stack));
    depth       = BZLA_POP_STACK(depth_stack);
    exp         = BZLA_POP_STACK(dump);
    expect_bv   = BZLA_POP_STACK(expect_bv_stack);
    expect_bool = BZLA_POP_STACK(expect_bool_stack);
    add_space   = BZLA_POP_STACK(add_space_stack);
    zero_extend = BZLA_POP_STACK(zero_extend_stack);
    real_exp    = bzla_node_real_addr(exp);
    is_bool     = is_boolean(sdc, real_exp);
    assert(!expect_bv || !expect_bool);
    assert(!expect_bool || !expect_bv);

    /* open s-expression */
    if (!bzla_hashptr_table_get(visited, real_exp))
    {
      if (add_space) fputc(' ', sdc->file);

      /* wrap node with zero_extend */
      if (zero_extend)
      {
        fputc(' ', sdc->file);
        open_sexp(sdc);
        fprintf(sdc->file, "(_ zero_extend %d) ", zero_extend);
      }

      /* always print constants */
      if (is_const(real_exp))
      {
        if (exp == sdc->bzla->true_exp && !expect_bv)
        {
          fputs("true", sdc->file);
        }
        else if (exp == bzla_node_invert(sdc->bzla->true_exp) && !expect_bv)
        {
          fputs("false", sdc->file);
        }
        else if (bzla_node_is_inverted(exp))
        {
          bits =
              bzla_bv_not(sdc->bzla->mm, bzla_node_bv_const_get_bits(real_exp));
          dump_const_bv_value_aux_smt(sdc, bits);
          bzla_bv_free(sdc->bzla->mm, bits);
        }
        else if (bzla_node_is_rm_const(real_exp))
        {
          BzlaNode *bv_const = bzla_fp_word_blast(sdc->bzla, real_exp);
          bzla_dumpsmt_dump_const_rm_value(
              sdc->bzla, bzla_node_bv_const_get_bits(bv_const), sdc->file);
        }
        else if (bzla_node_is_fp_const(real_exp))
        {
          BzlaNode *bv_const = bzla_fp_word_blast(sdc->bzla, real_exp);
          bzla_dumpsmt_dump_const_fp_value(
              sdc->bzla,
              bzla_node_bv_const_get_bits(bv_const),
              bzla_node_fp_get_exp_width(sdc->bzla, real_exp),
              bzla_node_fp_get_sig_width(sdc->bzla, real_exp),
              sdc->file);
        }
        else
        {
          assert(bzla_node_is_bv_const(real_exp));
          dump_const_bv_value_aux_smt(sdc,
                                      bzla_node_bv_const_get_bits(real_exp));
        }

        /* close zero extend */
        if (zero_extend) close_sexp(sdc);
        continue;
      }

      /* wrap non-bool node and make it bool */
      if (expect_bool && !is_bool)
      {
        open_sexp(sdc);
        fputs("= ", sdc->file);
        bits = bzla_bv_one(sdc->bzla->mm, 1);
        dump_const_bv_value_aux_smt(sdc, bits);
        bzla_bv_free(sdc->bzla->mm, bits);
        fputc(' ', sdc->file);
      }

      /* wrap node with bvnot/not */
      if (bzla_node_is_inverted(exp))
      {
        open_sexp(sdc);
        fputs(expect_bv || !is_bool ? "bvnot " : "not ", sdc->file);
      }

      /* wrap bool node and make it a bit vector expression */
      if (is_bool && expect_bv)
      {
        open_sexp(sdc);
        fputs("ite ", sdc->file);
      }

      if (bzla_hashptr_table_get(sdc->dumped, real_exp)
          || (bzla_node_is_lambda(real_exp) && !bzla_node_is_array(real_exp))
          || bzla_node_is_uf(real_exp))
      {
#ifndef NDEBUG
        BzlaPtrHashBucket *b;
        b = bzla_hashptr_table_get(sdc->dump, real_exp);
        assert(b);
        /* functions and variables are declared separately */
        assert(bzla_node_is_lambda(real_exp) || bzla_node_is_uf(real_exp)
               || bzla_node_is_var(real_exp) || bzla_node_is_param(real_exp)
               || b->data.as_int > 1);
#endif
        dump_smt_id(sdc, exp);
        goto CLOSE_WRAPPER;
      }

      if (depth_limit && depth >= depth_limit)
      {
        fprintf(sdc->file, "%s_%d", g_kind2smt[real_exp->kind], real_exp->id);
        goto CLOSE_WRAPPER;
      }

      PUSH_DUMP_NODE(exp, expect_bv, expect_bool, 0, zero_extend, depth);
      bzla_hashptr_table_add(visited, real_exp);
      op = "";
      switch (real_exp->kind)
      {
        case BZLA_BV_SLL_NODE:
        case BZLA_BV_SRL_NODE:
          assert(!is_bool);
          op = g_kind2smt[real_exp->kind];
          assert(bzla_node_bv_get_width(sdc->bzla, real_exp) > 1);
          pad = bzla_node_bv_get_width(sdc->bzla, real_exp)
                - bzla_node_bv_get_width(sdc->bzla, real_exp->e[1]);
          PUSH_DUMP_NODE(real_exp->e[1], 1, 0, 1, pad, depth + 1);
          PUSH_DUMP_NODE(real_exp->e[0], 1, 0, 1, 0, depth + 1);
          break;

        case BZLA_COND_NODE:
          op = "ite";
          PUSH_DUMP_NODE(real_exp->e[2], !is_bool, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE(real_exp->e[1], !is_bool, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE(real_exp->e[0], 0, 1, 1, 0, depth + 1);
          break;

        case BZLA_APPLY_NODE:
          if (bzla_node_is_array(real_exp->e[0]))
          {
            op = "select ";
          }

          /* we need the arguments in reversed order */
          bzla_iter_args_init(&it, real_exp->e[1]);
          while (bzla_iter_args_has_next(&it))
          {
            tmp = bzla_iter_args_next(&it);
            BZLA_PUSH_STACK(args, tmp);
          }
          while (!BZLA_EMPTY_STACK(args))
          {
            tmp = BZLA_POP_STACK(args);
            // TODO (ma): what about bool arguments/indices
            PUSH_DUMP_NODE(tmp, 1, 0, 1, 0, depth + 1);
          }
          PUSH_DUMP_NODE(real_exp->e[0], 1, 0, 0, 0, depth + 1);
          break;

        case BZLA_LAMBDA_NODE:
          assert(bzla_node_is_lambda(exp));
          assert(bzla_node_is_array(exp));

          if (bzla_node_is_const_array(exp))
          {
            op = "";
            PUSH_DUMP_NODE(real_exp->e[1], 1, 0, 0, 0, depth + 1);
          }
          else
          {
            tmp = 0;
            expand_lambda(sdc, exp, &indices, &values, &tmp);
            assert(tmp);
            assert(bzla_node_is_uf_array(tmp));

            for (i = 0; i < BZLA_COUNT_STACK(indices); i++)
            {
              PUSH_DUMP_NODE(BZLA_PEEK_STACK(values, i), 1, 0, 1, 0, depth + 1);
              PUSH_DUMP_NODE(
                  BZLA_PEEK_STACK(indices, i), 1, 0, 1, 0, depth + 1);
              if (i < BZLA_COUNT_STACK(indices) - 1)
              {
                open_sexp(sdc);
                fputs("store ", sdc->file);
                PUSH_DUMP_NODE(exp, 1, 0, 1, 0, depth + 1);
              }
            }
            BZLA_RESET_STACK(indices);
            BZLA_RESET_STACK(values);

            op = "store";
            /* push base array */
            PUSH_DUMP_NODE(tmp, 1, 0, 1, 0, depth + 1);
          }
          break;

        case BZLA_UPDATE_NODE:
          op = "store";
          PUSH_DUMP_NODE(real_exp->e[2], 1, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE(real_exp->e[1]->e[0], 1, 0, 1, 0, depth + 1);
          PUSH_DUMP_NODE(real_exp->e[0], 1, 0, 1, 0, depth + 1);
          break;

        default:
          expect_bv = 1;
          switch (real_exp->kind)
          {
            case BZLA_FUN_EQ_NODE:
            case BZLA_BV_EQ_NODE:
              op        = "=";
              expect_bv = 1;
              break;
            case BZLA_BV_ULT_NODE:
              op        = "bvult";
              expect_bv = 1;
              break;
            case BZLA_BV_SLT_NODE:
              op        = "bvslt";
              expect_bv = 1;
              break;
            case BZLA_BV_SLICE_NODE:
              assert(!is_bool);
              op = "extract";
              break;
            case BZLA_BV_AND_NODE:
              op        = is_bool ? "and" : "bvand";
              expect_bv = !is_bool;
              break;
            case BZLA_BV_ADD_NODE:
              assert(!is_bool);
              op = "bvadd";
              break;
            case BZLA_BV_MUL_NODE:
              assert(!is_bool);
              op = "bvmul";
              break;
            case BZLA_BV_UDIV_NODE:
              assert(!is_bool);
              op = "bvudiv";
              break;
            case BZLA_BV_UREM_NODE:
              assert(!is_bool);
              op = "bvurem";
              break;
            case BZLA_BV_CONCAT_NODE:
              assert(!is_bool);
              op = "concat";
              break;
            case BZLA_FORALL_NODE:
              assert(is_bool);
              op = "forall";
              break;
            case BZLA_EXISTS_NODE:
              assert(is_bool);
              op = "exists";
              break;
            default: op = g_kind2smt[real_exp->kind];
          }
          if (bzla_node_is_bv_and(real_exp) && is_bool)
          {
            assert(BZLA_EMPTY_STACK(args));
            collect_and_children(sdc, exp, &args);
            assert(BZLA_COUNT_STACK(args) >= 2);
            for (i = 0; i < BZLA_COUNT_STACK(args); i++)
            {
              tmp = BZLA_PEEK_STACK(args, i);
              PUSH_DUMP_NODE(tmp, expect_bv, 0, 1, 0, depth + 1);
            }
            BZLA_RESET_STACK(args);
          }
#if 0
		else if (bzla_node_is_quantifier (real_exp))
		  {
		    /* body of quantifiers are handled differently (let
		     * bindings etc.) */
		    if (real_exp->e[1] != bzla_node_binder_get_body (real_exp)
			&& real_exp->kind
			   != bzla_node_real_addr (real_exp->e[1])->kind)
		      PUSH_DUMP_NODE (real_exp->e[1], 0, 1, 1, 0,
				      depth + 1);
		  }
#endif
          else if (!bzla_node_is_quantifier(real_exp))
            for (i = 1; i <= real_exp->arity; i++)
              PUSH_DUMP_NODE(real_exp->e[real_exp->arity - i],
                             expect_bv,
                             0,
                             1,
                             0,
                             depth + 1);
      }

      /* open s-expression */
      assert(op);
      open_sexp(sdc);

      if (bzla_node_is_bv_slice(real_exp))
      {
        fprintf(sdc->file,
                "(_ %s %d %d)",
                op,
                bzla_node_bv_slice_get_upper(real_exp),
                bzla_node_bv_slice_get_lower(real_exp));
      }
      else if (bzla_node_is_const_array(real_exp))
      {
        fputs("(as const ", sdc->file);
        bzla_dumpsmt_dump_sort_node(real_exp, sdc->file);
        fputs(") ", sdc->file);
      }
      else if (bzla_node_is_fp_to_fp_from_sbv(real_exp)
               || bzla_node_is_fp_to_fp_from_bv(real_exp)
               || bzla_node_is_fp_to_fp_from_fp(real_exp)
               || bzla_node_is_fp_to_fp_from_ubv(real_exp))
      {
        BzlaSort *sort =
            bzla_sort_get_by_id(sdc->bzla, bzla_node_get_sort_id(real_exp));
        fprintf(sdc->file,
                "(_ %s %u %u)",
                op,
                sort->fp.width_exp,
                sort->fp.width_sig);
      }
      else if (bzla_node_is_fp_to_sbv(real_exp)
               || bzla_node_is_fp_to_ubv(real_exp))
      {
        fprintf(sdc->file,
                "(_ %s %u)",
                op,
                bzla_node_bv_get_width(sdc->bzla, real_exp));
      }
      else if (bzla_node_is_quantifier(real_exp))
      {
        fprintf(sdc->file, "%s (", op);
        bzla_iter_binder_init(&node_it, real_exp);
        tmp = 0;
        while (bzla_iter_binder_has_next(&node_it))
        {
          tmp = bzla_iter_binder_next(&node_it);

          if (tmp->kind != real_exp->kind) break;

          if (tmp != real_exp) fputc(' ', sdc->file);
          if (sdc->pretty_print)
          {
            fputc('\n', sdc->file);
            print_indent(sdc);
          }
          fputc('(', sdc->file);
          dump_smt_id(sdc, tmp->e[0]);
          fputc(' ', sdc->file);
          bzla_dumpsmt_dump_sort_node(tmp->e[0], sdc->file);
          fputc(')', sdc->file);
          bzla_hashptr_table_add(sdc->dumped, tmp->e[0]);
          bzla_hashptr_table_add(sdc->dumped, tmp);
        }
        assert(tmp);
        assert(bzla_node_is_regular(tmp));
        assert(bzla_node_is_quantifier(tmp));
        fputc(')', sdc->file);

        if (tmp->kind == real_exp->kind)
        {
          assert(tmp->e[1] == bzla_node_binder_get_body(tmp));
          recursively_dump_exp_let_smt(
              sdc, tmp->e[1], false, depth_limit ? depth_limit - depth : 0);
        }
        else
          PUSH_DUMP_NODE(tmp, 0, 1, 1, 0, depth + 1);

#if 0
	      fprintf (sdc->file, " ((%s ",
		       bzla_get_symbol_exp (sdc->bzla, real_exp->e[0]));
	      bzla_dumpsmt_dump_sort_node (real_exp->e[0], sdc->file);
	      fprintf (sdc->file, "))");
	      bzla_hashptr_table_add (sdc->dumped, real_exp->e[0]);
	      if (real_exp->e[1] == bzla_node_binder_get_body (real_exp))
		recursively_dump_exp_let_smt (
		    sdc, real_exp->e[1], false,
		    depth_limit ? depth_limit - depth : 0);
#endif
      }
      else
      {
        fprintf(sdc->file, "%s", op);
      }
    }
    /* close s-expression */
    else
    {
      if (!bzla_hashptr_table_get(sdc->dumped, real_exp))
        bzla_hashptr_table_add(sdc->dumped, real_exp);

      /* close s-expression */
      if (real_exp->arity > 0) close_sexp(sdc);

    CLOSE_WRAPPER:
      /* close wrappers */

      /* wrap boolean expressions in bit vector expression */
      if (is_bool && expect_bv && !bzla_node_is_bv_const(real_exp))
      {
        fputc(' ', sdc->file);
        bits = bzla_bv_one(sdc->bzla->mm, 1);
        dump_const_bv_value_aux_smt(sdc, bits);
        bzla_bv_free(sdc->bzla->mm, bits);
        fputc(' ', sdc->file);
        bits = bzla_bv_new(sdc->bzla->mm, 1);
        dump_const_bv_value_aux_smt(sdc, bits);
        bzla_bv_free(sdc->bzla->mm, bits);
        close_sexp(sdc);
      }

      /* close bvnot for non-constants */
      if (bzla_node_is_inverted(exp) && !bzla_node_is_bv_const(real_exp))
        close_sexp(sdc);

      /* close bool wrapper */
      if (expect_bool && !is_boolean(sdc, real_exp)) close_sexp(sdc);

      /* close zero extend wrapper */
      if (zero_extend) close_sexp(sdc);
    }
  }
  assert(BZLA_EMPTY_STACK(expect_bv_stack));
  BZLA_RELEASE_STACK(args);
  BZLA_RELEASE_STACK(dump);
  BZLA_RELEASE_STACK(expect_bv_stack);
  BZLA_RELEASE_STACK(expect_bool_stack);
  BZLA_RELEASE_STACK(add_space_stack);
  BZLA_RELEASE_STACK(zero_extend_stack);
  BZLA_RELEASE_STACK(depth_stack);
  BZLA_RELEASE_STACK(indices);
  BZLA_RELEASE_STACK(values);
  bzla_hashptr_table_delete(visited);
}

static void
dump_let_smt(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(sdc);
  assert(bzla_node_is_regular(exp));
  assert(!bzla_hashptr_table_get(sdc->dumped, exp));

  bool newline;

  open_sexp(sdc);
  sdc->indent--;
  fputs("let (", sdc->file);
  fputc('(', sdc->file);
  dump_smt_id(sdc, exp);  // TODO (ma): better symbol for lets?
  fputc(' ', sdc->file);
  newline      = sdc->newline;
  sdc->newline = false;
  recursively_dump_exp_smt(sdc, exp, !is_boolean(sdc, exp), 0);
  sdc->newline = newline;
  fputs("))", sdc->file);
  sdc->open_lets++;
  assert(bzla_hashptr_table_get(sdc->dumped, exp));
}

static void
collect_shared_exps(BzlaSMTDumpContext *sdc,
                    BzlaNode *root,
                    BzlaNodePtrStack *shared)
{
  uint32_t i, refs;
  BzlaNode *cur;
  BzlaIntHashTable *cache;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit;
  BzlaPtrHashBucket *b;

  mm    = sdc->bzla->mm;
  cache = bzla_hashint_table_new(mm);

  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, *shared);
  BZLA_PUSH_STACK(visit, root);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashint_table_contains(cache, cur->id)
        || bzla_hashptr_table_get(sdc->dumped, cur) || bzla_node_is_binder(cur))
      continue;

    b = bzla_hashptr_table_get(sdc->dump, cur);
    assert(b);
    refs = b->data.as_int;

    if (!bzla_node_is_args(cur)
        && !bzla_node_is_param(cur)
        /* constants are always printed */
        && !is_const(cur) && refs > 1)
      BZLA_PUSH_STACK(*shared, cur);

    bzla_hashint_table_add(cache, cur->id);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  bzla_hashint_table_delete(cache);
  BZLA_RELEASE_STACK(visit);
}

static void
recursively_dump_exp_let_smt(BzlaSMTDumpContext *sdc,
                             BzlaNode *exp,
                             bool expect_bv,
                             uint32_t depth_limit)
{
  uint32_t i;
  BzlaNode *cur;
  BzlaNodePtrStack shared;

  if (bzla_node_is_quantifier(exp))
    recursively_dump_exp_smt(sdc, exp, expect_bv, depth_limit);
  else
  {
    BZLA_INIT_STACK(sdc->bzla->mm, shared);
    collect_shared_exps(sdc, exp, &shared);

    if (shared.start)
      qsort(shared.start,
            BZLA_COUNT_STACK(shared),
            sizeof(BzlaNode *),
            cmp_node_id);

    for (i = 0; i < BZLA_COUNT_STACK(shared); i++)
    {
      cur = BZLA_PEEK_STACK(shared, i);
      assert(bzla_node_is_regular(cur));
      dump_let_smt(sdc, cur);
      fputc(' ', sdc->file);
    }

    recursively_dump_exp_smt(sdc, exp, expect_bv, depth_limit);

    /* close lets */
    for (i = 0; i < BZLA_COUNT_STACK(shared); i++)
    {
      fputc(')', sdc->file);
      //      close_sexp (sdc);
      sdc->open_lets--;
    }

    BZLA_RELEASE_STACK(shared);
  }
}

static void
dump_fun_let_smt2(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(sdc);
  assert(bzla_node_is_regular(exp));
  assert(!bzla_hashptr_table_get(sdc->dumped, exp));

  bool is_bool;

  is_bool = is_boolean(sdc, exp);
  open_sexp(sdc);
  fputs("define-fun ", sdc->file);
  dump_smt_id(sdc, exp);
  fputs(" () ", sdc->file);
  if (is_bool)
    fputs("Bool", sdc->file);
  else
    bzla_dumpsmt_dump_sort_node(exp, sdc->file);
  fputc(' ', sdc->file);
  recursively_dump_exp_smt(sdc, exp, !is_bool, 0);
  close_sexp(sdc);
  fputc('\n', sdc->file);
  assert(bzla_hashptr_table_get(sdc->dumped, exp));
}

static void
dump_fun_smt2(BzlaSMTDumpContext *sdc, BzlaNode *fun, bool dump_as_node)
{
  assert(fun);
  assert(sdc);
  assert(bzla_node_is_regular(fun));
  assert(bzla_node_is_lambda(fun));
  assert(!bzla_node_is_array(fun));
  assert(!fun->parameterized);
  assert(!bzla_hashptr_table_get(sdc->dumped, fun));

  uint32_t i, refs;
  BzlaNode *cur, *param, *fun_body, *p;
  BzlaMemMgr *mm = sdc->bzla->mm;
  BzlaNodePtrStack visit, shared;
  BzlaNodeIterator it, iit;
  BzlaPtrHashTable *mark;
  BzlaPtrHashBucket *b;

  mark = bzla_hashptr_table_new(mm,
                                (BzlaHashPtr) bzla_node_hash_by_id,
                                (BzlaCmpPtr) bzla_node_compare_by_id);
  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, shared);

#if 0
  extract_store (sdc, fun, &index, &value, &array);

  if (index)
    {
      assert (value);
      assert (array);
      bzla_hashptr_table_add (sdc->stores, fun);
      return;
    }
#endif

  /* collect shared parameterized expressions in function body */
  fun_body = bzla_node_binder_get_body(fun);
  BZLA_PUSH_STACK(visit, fun_body);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashptr_table_get(mark, cur)
        || bzla_hashptr_table_get(sdc->dumped, cur)
        || (bzla_node_is_lambda(cur) && !bzla_node_is_array(cur)))
      continue;

    b = bzla_hashptr_table_get(sdc->dump, cur);
    assert(b);
    refs = b->data.as_int;

    /* args and params are handled differently */
    /* collect shared parameterized expressions in function body.
     * arguments, parameters, and constants are excluded. */
    if (!bzla_node_is_args(cur)
        && !bzla_node_is_param(cur)
        /* constants are always printed */
        && !is_const(cur) && cur->parameterized && refs > 1)
      BZLA_PUSH_STACK(shared, cur);

    bzla_hashptr_table_add(mark, cur);
    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  /* dump function signature */
  if (dump_as_node)
  {
    fputs("(lambda", sdc->file);
  }
  else
  {
    fputs("(define-fun ", sdc->file);
    dump_smt_id(sdc, fun);
  }
  fputs(" (", sdc->file);

  bzla_iter_lambda_init(&it, fun);
  while (bzla_iter_lambda_has_next(&it))
  {
    cur   = bzla_iter_lambda_next(&it);
    param = cur->e[0];
    if (!bzla_hashptr_table_get(mark, cur)) bzla_hashptr_table_add(mark, cur);
    if (!bzla_hashptr_table_get(mark, param))
      bzla_hashptr_table_add(mark, param);
    bzla_hashptr_table_add(sdc->dumped, cur);
    bzla_hashptr_table_add(sdc->dumped, param);
    if (fun != cur) fputc(' ', sdc->file);
    fputc('(', sdc->file);
    dump_smt_id(sdc, param);
    fputc(' ', sdc->file);
    bzla_dumpsmt_dump_sort_node(param, sdc->file);
    fputc(')', sdc->file);
  }
  fputs(") ", sdc->file);

  if (!dump_as_node)
  {
    if (is_boolean(sdc, fun_body))
      fputs("Bool", sdc->file);
    else
      bzla_dumpsmt_dump_sort_node(fun_body, sdc->file);
    fputc(' ', sdc->file);
  }

  assert(sdc->open_lets == 0);

  /* dump expressions that are shared in 'fun' */
  if (shared.start)
    qsort(shared.start,
          BZLA_COUNT_STACK(shared),
          sizeof(BzlaNode *),
          cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(shared); i++)
  {
    cur = BZLA_PEEK_STACK(shared, i);
    assert(bzla_node_is_regular(cur));
    assert(cur->parameterized);
    dump_let_smt(sdc, cur);
    fputc(' ', sdc->file);
  }
  recursively_dump_exp_smt(sdc, fun_body, !is_boolean(sdc, fun_body), 0);

  /* close lets */
  for (i = 0; i < sdc->open_lets; i++) fputc(')', sdc->file);
  //    close_sexp (sdc);
  sdc->open_lets = 0;

  /* close define-fun */
  fputs(")", sdc->file);

  /* due to lambda hashing it is possible that a lambda in 'fun' is shared in
   * different functions. hence, we have to check if all lambda parents of
   * the resp. lambda have already been dumped as otherwise all expressions
   * below have to be removed from 'sdc->dumped' as they will be dumped
   * again in a different function definition. */
  bzla_iter_lambda_init(&it, fun);
  while (bzla_iter_lambda_has_next(&it))
  {
    cur = bzla_iter_lambda_next(&it);
    bzla_iter_parent_init(&iit, cur);
    while (bzla_iter_parent_has_next(&iit))
    {
      p = bzla_iter_parent_next(&iit);
      /* find lambda parent that needs to be dumped but has not yet been
       * dumped */
      if (bzla_hashptr_table_get(sdc->dump, p)
          && !bzla_hashptr_table_get(sdc->dumped, p) && bzla_node_is_lambda(p))
      {
        BZLA_PUSH_STACK(visit, cur);
        while (!BZLA_EMPTY_STACK(visit))
        {
          cur = bzla_node_real_addr(BZLA_POP_STACK(visit));
          assert(bzla_node_is_regular(cur));

          if (!cur->parameterized
              && (!bzla_hashptr_table_get(mark, cur)
                  || !bzla_hashptr_table_get(sdc->dumped, cur)))
            continue;

          if (bzla_hashptr_table_get(sdc->dumped, cur))
            bzla_hashptr_table_remove(sdc->dumped, cur, 0, 0);

          for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
        }
        break;
      }
    }
  }

  BZLA_RELEASE_STACK(shared);
  BZLA_RELEASE_STACK(visit);
  bzla_hashptr_table_delete(mark);
}

static void
dump_declare_fun_smt(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(!bzla_hashptr_table_get(sdc->dumped, exp));
  bool is_const = bzla_node_is_var(exp) || bzla_node_is_uf_array(exp);

  fputs(is_const ? "(declare-const " : "(declare-fun ", sdc->file);
  dump_smt_id(sdc, exp);
  fputc(' ', sdc->file);
  bzla_dumpsmt_dump_sort_node(exp, sdc->file);
  fputs(")\n", sdc->file);
  bzla_hashptr_table_add(sdc->dumped, exp);
}

static void
dump_assert_smt2(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(sdc);
  assert(exp);
  assert(bzla_node_bv_get_width(sdc->bzla, exp) == 1);

  open_sexp(sdc);
  fputs("assert ", sdc->file);
  if (!is_boolean(sdc, exp)) fputs("(= ", sdc->file);
  recursively_dump_exp_smt(sdc, exp, 0, 0);
  if (!is_boolean(sdc, exp)) fputs(" #b1)", sdc->file);
  close_sexp(sdc);
  fputc('\n', sdc->file);
}

static void
set_logic_smt(BzlaSMTDumpContext *sdc, const char *logic)
{
  assert(sdc);

  const char *fmt;

  fmt = "(set-logic %s)\n";
  fprintf(sdc->file, fmt, logic);
}

static uint32_t
get_references(BzlaSMTDumpContext *sdc, BzlaNode *exp)
{
  assert(exp);

  uint32_t refs = 0;
  BzlaNode *cur;
  BzlaNodeIterator it;
  BzlaPtrHashBucket *b;

  exp = bzla_node_real_addr(exp);

  /* get reference count of roots */
  if (bzla_hashptr_table_get(sdc->roots, exp)) refs++;
  if (bzla_hashptr_table_get(sdc->roots, bzla_node_invert(exp))) refs++;

  bzla_iter_parent_init(&it, exp);
  while (bzla_iter_parent_has_next(&it))
  {
    cur = bzla_iter_parent_next(&it);
    assert(bzla_node_is_regular(cur));
    b = bzla_hashptr_table_get(sdc->dump, cur);
    /* argument nodes are counted differently */
    if (!b || bzla_node_is_args(cur)) continue;
    refs++;
  }
  return refs;
}

static bool
has_lambda_parents_only(BzlaNode *exp)
{
  BzlaNode *p;
  BzlaNodeIterator it;
  bzla_iter_parent_init(&it, exp);
  while (bzla_iter_parent_has_next(&it))
  {
    p = bzla_iter_parent_next(&it);
    if (!bzla_node_is_lambda(p)) return false;
  }
  return true;
}

static void
mark_boolean(BzlaSMTDumpContext *sdc, BzlaNodePtrStack *exps)
{
  uint32_t i, j;
  bool is_bool;
  BzlaNode *cur;

  /* collect boolean terms */
  for (i = 0; i < BZLA_COUNT_STACK(*exps); i++)
  {
    cur = BZLA_PEEK_STACK(*exps, i);

    /* these nodes are boolean by definition */
    if (
        /* Boolean BV nodes */
        bzla_node_is_bv_eq(cur) || bzla_node_is_fun_eq(cur)
        || bzla_node_is_bv_ult(cur)
        || bzla_node_is_bv_slt(cur)

        /* Boolean FP nodes */
        || bzla_node_is_fp_is_inf(cur) || bzla_node_is_fp_is_nan(cur)
        || bzla_node_is_fp_is_neg(cur) || bzla_node_is_fp_is_normal(cur)
        || bzla_node_is_fp_is_pos(cur) || bzla_node_is_fp_is_subnormal(cur)
        || bzla_node_is_fp_is_zero(cur) || bzla_node_is_fp_lte(cur)
        || bzla_node_is_fp_lt(cur)
        || bzla_node_is_fp_eq(cur)
        || bzla_node_is_rm_eq(cur)

        /* Other Boolean nodes */
        || cur == bzla_node_real_addr(sdc->bzla->true_exp)
        || bzla_node_is_quantifier(cur))
    {
      bzla_hashptr_table_add(sdc->boolean, cur);
      continue;
    }
    else if (bzla_node_is_apply(cur))
    {
      /* boolean function */
      if ((bzla_node_is_lambda(cur->e[0])
           && is_boolean(sdc, bzla_node_binder_get_body(cur->e[0])))
          || (bzla_node_is_fun_cond(cur->e[0]) && is_boolean(sdc, cur->e[1])))
      {
        bzla_hashptr_table_add(sdc->boolean, cur);
      }
      continue;
    }
    else if ((bzla_node_is_bv_and(cur) || bzla_node_is_bv_cond(cur))
             && bzla_node_bv_get_width(sdc->bzla, cur) == 1)
    {
      is_bool = true;
      for (j = 0; j < cur->arity; j++)
        if (!(is_bool = is_boolean(sdc, cur->e[j]))) break;

      if (!is_bool) continue;

      bzla_hashptr_table_add(sdc->boolean, cur);
    }
  }
}

static void
print_logic(BzlaSMTDumpContext *sdc,
            bool logic_quant,
            bool logic_bv,
            bool logic_fp,
            bool logic_arrays,
            bool logic_uf)
{
  char logic_str[32];
  size_t size = 32;

  const char *str_quant = "", *str_arrays = "", *str_uf = "", *str_bv = "";
  const char *str_fp = "";

  if (!logic_quant)
  {
    str_quant = "QF_";
  }
  if (logic_arrays)
  {
    str_arrays = "A";
  }
  if (logic_uf)
  {
    str_uf = "UF";
  }
  if (logic_bv)
  {
    str_bv = "BV";
  }
  if (logic_fp)
  {
    str_fp = "FP";
  }

  snprintf(logic_str,
           size,
           "%s%s%s%s%s",
           str_quant,
           str_arrays,
           str_uf,
           str_bv,
           str_fp);

  set_logic_smt(sdc, logic_str);
}

static void
dump_smt(BzlaSMTDumpContext *sdc)
{
  assert(sdc);

  bool logic_quant = false, logic_arrays = false, logic_fp = false;
  bool logic_bv = true, logic_uf = false;
  uint32_t i, j;
  BzlaNode *e, *cur, *value, *index;
  BzlaMemMgr *mm;
  BzlaNodePtrStack visit, all, vars, shared, ufs, larr;
  BzlaPtrHashBucket *b;
  BzlaPtrHashTableIterator it;
  BzlaArgsIterator ait;
  BzlaPtrHashTable *static_rho;

  mm = sdc->bzla->mm;
  BZLA_INIT_STACK(mm, visit);
  BZLA_INIT_STACK(mm, shared);
  BZLA_INIT_STACK(mm, all);
  BZLA_INIT_STACK(mm, vars);
  BZLA_INIT_STACK(mm, ufs);
  BZLA_INIT_STACK(mm, larr);

  bzla_iter_hashptr_init(&it, sdc->roots);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    BZLA_PUSH_STACK(visit, bzla_node_real_addr(cur));
  }

  /* collect constants, variables, array variables and functions */
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = BZLA_POP_STACK(visit);
    assert(bzla_node_is_regular(cur));
    assert(!bzla_hashptr_table_get(sdc->dumped, cur));

    if (bzla_hashptr_table_get(sdc->dump, cur)) continue;

    bzla_hashptr_table_add(sdc->dump, cur)->data.as_int = 0;
    BZLA_PUSH_STACK(all, cur);

    if (bzla_node_is_var(cur))
    {
      BZLA_PUSH_STACK(vars, cur);
    }
    else if (bzla_node_is_uf(cur))
    {
      BZLA_PUSH_STACK(ufs, cur);
    }
    else if (bzla_node_is_lambda(cur) && !bzla_node_is_array(cur)
             && !cur->parameterized && !has_lambda_parents_only(cur))
    {
      BZLA_PUSH_STACK(shared, cur);
    }
    else if (bzla_node_is_lambda(cur) && bzla_node_is_array(cur)
             && !bzla_node_is_const_array(cur))
    {
      BZLA_PUSH_STACK(larr, cur);
    }
    else if (bzla_node_is_quantifier(cur))
    {
      logic_quant = true;
    }

    if (bzla_sort_is_fp(sdc->bzla, bzla_node_get_sort_id(cur)))
    {
      logic_fp = true;
    }
    else if (bzla_node_is_array(cur))
    {
      logic_arrays = true;
    }
    else if (bzla_node_is_uf(cur))
    {
      logic_uf = true;
    }

    for (j = 0; j < cur->arity; j++)
      BZLA_PUSH_STACK(visit, bzla_node_real_addr(cur->e[j]));
  }

  /* compute reference counts of indices and elements for array writes
   * (represented as lambdas) */
  for (i = 0; i < BZLA_COUNT_STACK(larr); i++)
  {
    cur        = BZLA_PEEK_STACK(larr, i);
    static_rho = bzla_node_lambda_get_static_rho(cur);
    assert(static_rho);

    bzla_iter_hashptr_init(&it, static_rho);
    while (bzla_iter_hashptr_has_next(&it))
    {
      value = bzla_node_real_addr(it.bucket->data.as_ptr);
      index = bzla_node_real_addr(bzla_iter_hashptr_next(&it));
      assert(bzla_node_is_args(index));
      assert(bzla_node_args_get_arity(sdc->bzla, index) == 1);
      if (!(b = bzla_hashptr_table_get(sdc->dump, value)))
      {
        b              = bzla_hashptr_table_add(sdc->dump, value);
        b->data.as_int = 0;
        BZLA_PUSH_STACK(all, value); /* not yet seen */
      }
      b->data.as_int += 1;
      if (!(b = bzla_hashptr_table_get(sdc->dump, index)))
      {
        b              = bzla_hashptr_table_add(sdc->dump, index);
        b->data.as_int = 0;
        BZLA_PUSH_STACK(all, index); /* not yet seen */
      }
      b->data.as_int += 1;
    }
  }

  /* compute reference counts of expressions (required for determining shared
   * expressions)*/
  if (all.start) qsort(all.start, BZLA_COUNT_STACK(all), sizeof e, cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(all); i++)
  {
    cur = BZLA_PEEK_STACK(all, i);
    b   = bzla_hashptr_table_get(sdc->dump, cur);
    assert(b);
    /* cache result for later reuse */
    b->data.as_int += get_references(sdc, cur);

    /* update references for expressions under argument nodes */
    if (bzla_node_is_args(cur) && b->data.as_int > 0)
    {
      bzla_iter_args_init(&ait, cur);
      while (bzla_iter_args_has_next(&ait))
      {
        e = bzla_node_real_addr(bzla_iter_args_next(&ait));
        assert(bzla_hashptr_table_get(sdc->dump, e));
        bzla_hashptr_table_get(sdc->dump, e)->data.as_int += b->data.as_int;
      }
    }
  }

  /* collect globally shared expressions */
  for (i = 0; i < BZLA_COUNT_STACK(all); i++)
  {
    cur = BZLA_PEEK_STACK(all, i);
    b   = bzla_hashptr_table_get(sdc->dump, cur);
    assert(b);

    if (b->data.as_int <= 1
        /* parameterized expressions are only shared within a function */
        || cur->parameterized
        || bzla_node_is_param(cur)
        /* constants are always printed */
        || is_const(cur)
        /* for variables and functions the resp. symbols are always printed */
        || bzla_node_is_var(cur)
        || (bzla_node_is_lambda(cur) && !bzla_node_is_array(cur))
        || bzla_node_is_uf(cur)
        /* argument nodes are never printed */
        || bzla_node_is_args(cur))
      continue;

    BZLA_PUSH_STACK(shared, cur);
  }

  /* collect boolean terms */
  mark_boolean(sdc, &all);

  /* begin dump */
  print_logic(sdc, logic_quant, logic_bv, logic_fp, logic_arrays, logic_uf);

  /* dump inputs */
  if (vars.start)
    qsort(vars.start, BZLA_COUNT_STACK(vars), sizeof e, cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(vars); i++)
  {
    cur = BZLA_PEEK_STACK(vars, i);
    dump_declare_fun_smt(sdc, cur);
  }

  if (ufs.start) qsort(ufs.start, BZLA_COUNT_STACK(ufs), sizeof e, cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(ufs); i++)
  {
    cur = BZLA_PEEK_STACK(ufs, i);
    dump_declare_fun_smt(sdc, cur);
  }

  /* dump shared expressions and functions */
  if (shared.start)
    qsort(shared.start, BZLA_COUNT_STACK(shared), sizeof e, cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(shared); i++)
  {
    cur = BZLA_PEEK_STACK(shared, i);
    assert(bzla_node_is_regular(cur));

    if (bzla_hashptr_table_get(sdc->dumped, cur)) continue;

    assert(!cur->parameterized);

    if (bzla_node_is_lambda(cur) && !bzla_node_is_array(cur))
      dump_fun_smt2(sdc, cur, false);
    else
      dump_fun_let_smt2(sdc, cur);
  }

  /* dump assertions/build root */
  bzla_iter_hashptr_init(&it, sdc->roots);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    dump_assert_smt2(sdc, cur);
  }
  assert(sdc->open_lets == 0);

#ifndef NDEBUG
  bzla_iter_hashptr_init(&it, sdc->dump);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = bzla_iter_hashptr_next(&it);
    /* constants and function applications are always dumped (hence, not in
     * mark) */
    if (is_const(cur)
        || bzla_node_is_apply(cur)
        /* argument nodes are never dumped and not in mark */
        || bzla_node_is_args(cur) || cur->parameterized
        || (bzla_node_is_lambda(cur) && bzla_node_is_array(cur)))
      continue;
    assert(bzla_hashptr_table_get(sdc->dumped, cur));
  }
#endif

  BZLA_RELEASE_STACK(shared);
  BZLA_RELEASE_STACK(visit);
  BZLA_RELEASE_STACK(all);
  BZLA_RELEASE_STACK(vars);
  BZLA_RELEASE_STACK(ufs);
  BZLA_RELEASE_STACK(larr);

  fputs("(check-sat)\n", sdc->file);
  fputs("(exit)\n", sdc->file);
  fflush(sdc->file);
}

static void
dump_smt_aux(Bzla *bzla, FILE *file, BzlaNode **roots, uint32_t nroots)
{
  assert(bzla);
  assert(file);

  uint32_t i;
  BzlaNode *tmp;
  BzlaPtrHashTableIterator it;
  BzlaSMTDumpContext *sdc;

  sdc = new_smt_dump_context(bzla, file);

  if (nroots)
  {
    for (i = 0; i < nroots; i++) add_root_to_smt_dump_context(sdc, roots[i]);
  }
  else
  {
    if (bzla->inconsistent)
    {
      tmp = bzla_exp_false(bzla);
      add_root_to_smt_dump_context(sdc, tmp);
      bzla_node_release(bzla, tmp);
    }
    else if (bzla->unsynthesized_constraints->count == 0
             && bzla->synthesized_constraints->count == 0)
    {
      tmp = bzla_exp_true(bzla);
      add_root_to_smt_dump_context(sdc, tmp);
      bzla_node_release(bzla, tmp);
    }
    else
    {
      bzla_iter_hashptr_init(&it, bzla->unsynthesized_constraints);
      bzla_iter_hashptr_queue(&it, bzla->synthesized_constraints);
      while (bzla_iter_hashptr_has_next(&it))
        add_root_to_smt_dump_context(sdc, bzla_iter_hashptr_next(&it));
    }
  }

  dump_smt(sdc);
  delete_smt_dump_context(sdc);
}

void
bzla_dumpsmt_dump(Bzla *bzla, FILE *file)
{
  assert(bzla);
  assert(file);
  dump_smt_aux(bzla, file, 0, 0);
}

void
bzla_dumpsmt_dump_node(Bzla *bzla, FILE *file, BzlaNode *exp, uint32_t depth)
{
  assert(bzla);

  uint32_t i;
  BzlaNode *cur, *real_exp, *binder;
  BzlaSMTDumpContext *sdc;
  BzlaNodePtrStack visit, all;
  BzlaArgsIterator ait;
  BzlaPtrHashBucket *b;

  real_exp = bzla_node_real_addr(exp);

  BZLA_INIT_STACK(bzla->mm, all);
  BZLA_INIT_STACK(bzla->mm, visit);
  sdc          = new_smt_dump_context(bzla, file);
  sdc->newline = false;

  if (!exp)
  {
    fprintf(file, "null\n");
    goto CLEANUP;
  }
  else if (bzla_node_is_args(real_exp))
  {
    fprintf(file, "%s_%d\n", g_kind2smt[real_exp->kind], real_exp->id);
    goto CLEANUP;
  }
  else if (bzla_node_is_regular(exp)
           && (bzla_node_is_var(exp) || bzla_node_is_uf(exp)))
  {
    dump_declare_fun_smt(sdc, exp);
    goto CLEANUP;
  }

  BZLA_PUSH_STACK(visit, exp);
  while (!BZLA_EMPTY_STACK(visit))
  {
    cur = bzla_node_real_addr(BZLA_POP_STACK(visit));

    if (bzla_hashptr_table_get(sdc->dump, cur)) continue;

    if (bzla_node_is_var(cur) || bzla_node_is_uf(cur)
        || (bzla_node_is_param(cur)
            && (!(binder = bzla_node_param_get_binder(cur))
                || !bzla_hashptr_table_get(sdc->dump, binder))))
      bzla_hashptr_table_add(sdc->dumped, cur);

    bzla_hashptr_table_add(sdc->dump, cur);
    BZLA_PUSH_STACK(all, cur);

    for (i = 0; i < cur->arity; i++) BZLA_PUSH_STACK(visit, cur->e[i]);
  }

  /* compute reference counts of expressions (required for determining shared
   * expressions)*/
  if (all.start)
    qsort(all.start, BZLA_COUNT_STACK(all), sizeof(BzlaNode *), cmp_node_id);

  for (i = 0; i < BZLA_COUNT_STACK(all); i++)
  {
    cur = BZLA_PEEK_STACK(all, i);
    b   = bzla_hashptr_table_get(sdc->dump, cur);
    assert(b);
    assert(b->data.as_int == 0);
    /* cache result for later reuse */
    b->data.as_int = get_references(sdc, cur);

    /* update references for expressions under argument nodes */
    if (bzla_node_is_args(cur) && b->data.as_int > 0)
    {
      bzla_iter_args_init(&ait, cur);
      while (bzla_iter_args_has_next(&ait))
      {
        cur = bzla_node_real_addr(bzla_iter_args_next(&ait));
        assert(bzla_hashptr_table_get(sdc->dump, cur));
        bzla_hashptr_table_get(sdc->dump, cur)->data.as_int += b->data.as_int;
      }
    }
  }

  mark_boolean(sdc, &all);
  if (bzla_node_is_lambda(exp) && !bzla_node_is_array(exp))
    dump_fun_smt2(sdc, exp, true);
  else
  {
    recursively_dump_exp_let_smt(sdc, exp, false, depth);
  }
CLEANUP:
  delete_smt_dump_context(sdc);
  BZLA_RELEASE_STACK(all);
  BZLA_RELEASE_STACK(visit);
}
