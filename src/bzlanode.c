/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlanode.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "bzlaaig.h"
#include "bzlaaigvec.h"
#include "bzlabeta.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlalog.h"
#include "bzlarewrite.h"
#include "bzlarm.h"
#include "utils/bzlaabort.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#define BZLA_UNIQUE_TABLE_LIMIT 30

#define BZLA_FULL_UNIQUE_TABLE(table)   \
  ((table).num_elements >= (table).size \
   && bzla_util_log_2((table).size) < BZLA_UNIQUE_TABLE_LIMIT)

/*------------------------------------------------------------------------*/

const char *const g_bzla_op2str[BZLA_NUM_OPS_NODE] = {
    [BZLA_INVALID_NODE]       = "invalid",
    [BZLA_BV_CONST_NODE]      = "bvconst",
    [BZLA_VAR_NODE]           = "var",
    [BZLA_PARAM_NODE]         = "param",
    [BZLA_BV_SLICE_NODE]      = "slice",
    [BZLA_BV_AND_NODE]        = "and",
    [BZLA_BV_EQ_NODE]         = "bveq",
    [BZLA_FUN_EQ_NODE]        = "funeq",
    [BZLA_BV_ADD_NODE]        = "add",
    [BZLA_BV_MUL_NODE]        = "mul",
    [BZLA_BV_ULT_NODE]        = "ult",
    [BZLA_BV_SLL_NODE]        = "sll",
    [BZLA_BV_SLT_NODE]        = "slt",
    [BZLA_BV_SRL_NODE]        = "srl",
    [BZLA_BV_UDIV_NODE]       = "udiv",
    [BZLA_BV_UREM_NODE]       = "urem",
    [BZLA_BV_CONCAT_NODE]     = "concat",
    [BZLA_FP_ABS_NODE]        = "fpabs",
    [BZLA_FP_ADD_NODE]        = "fpadd",
    [BZLA_FP_CONST_NODE]      = "fpconst",
    [BZLA_FP_DIV_NODE]        = "fpdiv",
    [BZLA_FP_EQ_NODE]         = "fpeq",
    [BZLA_FP_IS_INF_NODE]     = "fpisinf",
    [BZLA_FP_IS_NAN_NODE]     = "fpisnan",
    [BZLA_FP_IS_NEG_NODE]     = "fpisneg",
    [BZLA_FP_IS_NORM_NODE]    = "fpisnorm",
    [BZLA_FP_IS_POS_NODE]     = "fpispos",
    [BZLA_FP_IS_SUBNORM_NODE] = "fpissubnorm",
    [BZLA_FP_IS_ZERO_NODE]    = "fpiszero",
    [BZLA_FP_FMA_NODE]        = "fpfma",
    [BZLA_FP_LTE_NODE]        = "fplte",
    [BZLA_FP_LT_NODE]         = "fplt",
    [BZLA_FP_MIN_NODE]        = "fpmin",
    [BZLA_FP_MAX_NODE]        = "fpmax",
    [BZLA_FP_MUL_NODE]        = "fpmul",
    [BZLA_FP_NEG_NODE]        = "fpneg",
    [BZLA_FP_REM_NODE]        = "fprem",
    [BZLA_FP_RTI_NODE]        = "fprti",
    [BZLA_FP_SQRT_NODE]       = "fpsqrt",
    [BZLA_FP_TO_SBV_NODE]     = "fptosbv",
    [BZLA_FP_TO_UBV_NODE]     = "fptoubv",
    [BZLA_FP_TO_FP_BV_NODE]   = "fptofpfrombv",
    [BZLA_FP_TO_FP_FP_NODE]   = "fptofpfromfp",
    [BZLA_FP_TO_FP_SBV_NODE]  = "fptofpfromint",
    [BZLA_FP_TO_FP_UBV_NODE]  = "fptofpfromuint",
    [BZLA_RM_CONST_NODE]      = "rmconst",
    [BZLA_RM_EQ_NODE]         = "rmeq",
    [BZLA_APPLY_NODE]         = "apply",
    [BZLA_FORALL_NODE]        = "forall",
    [BZLA_EXISTS_NODE]        = "exists",
    [BZLA_LAMBDA_NODE]        = "lambda",
    [BZLA_COND_NODE]          = "cond",
    [BZLA_ARGS_NODE]          = "args",
    [BZLA_UF_NODE]            = "uf",
    [BZLA_UPDATE_NODE]        = "update",
    [BZLA_PROXY_NODE]         = "proxy",
};

/*------------------------------------------------------------------------*/

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u, 111130391u};

#define NPRIMES ((uint32_t)(sizeof hash_primes / sizeof *hash_primes))

/*------------------------------------------------------------------------*/

/* do not move these two functions to the header (circular dependency) */

bool
bzla_node_is_bv_cond(const BzlaNode *exp)
{
  return bzla_node_is_cond(exp)
         && bzla_sort_is_bv(bzla_node_real_addr(exp)->bzla,
                            bzla_node_get_sort_id(exp));
}

bool
bzla_node_is_fun_cond(const BzlaNode *exp)
{
  return bzla_node_is_cond(exp)
         && bzla_sort_is_fun(bzla_node_real_addr(exp)->bzla,
                             bzla_node_get_sort_id(exp));
}

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static bool
is_valid_kind(BzlaNodeKind kind)
{
  return BZLA_INVALID_NODE <= kind && kind < BZLA_NUM_OPS_NODE;
}
#endif

static void
set_kind(Bzla *bzla, BzlaNode *exp, BzlaNodeKind kind)
{
  assert(is_valid_kind(kind));
  assert(is_valid_kind(exp->kind));

  assert(!BZLA_INVALID_NODE);

  if (exp->kind)
  {
    assert(bzla->ops[exp->kind].cur > 0);
    bzla->ops[exp->kind].cur--;
  }

  if (kind)
  {
    bzla->ops[kind].cur++;
    assert(bzla->ops[kind].cur > 0);
    if (bzla->ops[kind].cur > bzla->ops[kind].max)
      bzla->ops[kind].max = bzla->ops[kind].cur;
  }

  exp->kind = kind;
}

/*------------------------------------------------------------------------*/

bool
bzla_node_is_bv_const_zero(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaNode *real_exp;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  real_exp = bzla_node_real_addr(exp);
  bits     = bzla_node_bv_const_get_bits(real_exp);
  if (bzla_node_is_inverted(exp)) bits = bzla_bv_not(bzla->mm, bits);
  result = bzla_bv_is_zero(bits);
  if (bzla_node_is_inverted(exp)) bzla_bv_free(bzla->mm, bits);

  return result;
}

bool
bzla_node_is_bv_const_one(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaNode *real_exp;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  real_exp = bzla_node_real_addr(exp);
  bits     = bzla_node_bv_const_get_bits(real_exp);
  if (bzla_node_is_inverted(exp)) bits = bzla_bv_not(bzla->mm, bits);
  result = bzla_bv_is_one(bits);
  if (bzla_node_is_inverted(exp)) bzla_bv_free(bzla->mm, bits);

  return result;
}

bool
bzla_node_is_bv_const_ones(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaNode *real_exp;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  real_exp = bzla_node_real_addr(exp);
  bits     = bzla_node_bv_const_get_bits(real_exp);
  if (bzla_node_is_inverted(exp)) bits = bzla_bv_not(bzla->mm, bits);
  result = bzla_bv_is_ones(bits);
  if (bzla_node_is_inverted(exp)) bzla_bv_free(bzla->mm, bits);

  return result;
}

bool
bzla_node_is_bv_const_min_signed(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaNode *real_exp;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  real_exp = bzla_node_real_addr(exp);
  bits     = bzla_node_bv_const_get_bits(real_exp);
  if (bzla_node_is_inverted(exp)) bits = bzla_bv_not(bzla->mm, bits);
  result = bzla_bv_is_min_signed(bits);
  if (bzla_node_is_inverted(exp)) bzla_bv_free(bzla->mm, bits);

  return result;
}

bool
bzla_node_is_bv_const_max_signed(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaNode *real_exp;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  real_exp = bzla_node_real_addr(exp);
  bits     = bzla_node_bv_const_get_bits(real_exp);
  if (bzla_node_is_inverted(exp)) bits = bzla_bv_not(bzla->mm, bits);
  result = bzla_bv_is_max_signed(bits);
  if (bzla_node_is_inverted(exp)) bzla_bv_free(bzla->mm, bits);

  return result;
}

bool
bzla_node_bv_is_neg(Bzla *bzla, BzlaNode *exp, BzlaNode **res)
{
  assert(bzla);
  assert(exp);

  if (bzla_node_is_inverted(exp) || !bzla_node_is_bv_add(exp)) return false;

  if (bzla_node_is_bv_const_one(bzla, exp->e[0]))
  {
    if (res) *res = bzla_node_invert(exp->e[1]);
    return true;
  }

  if (bzla_node_is_bv_const_one(bzla, exp->e[1]))
  {
    if (res) *res = bzla_node_invert(exp->e[0]);
    return true;
  }

  return false;
}

/*------------------------------------------------------------------------*/

bool
bzla_node_is_fp_const_pos_zero(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_fp_const(exp)) return false;

  BzlaFloatingPoint *fp = ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
  return bzla_fp_is_zero(bzla, fp) && bzla_fp_is_pos(bzla, fp);
}

bool
bzla_node_is_fp_const_neg_zero(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_fp_const(exp)) return false;

  BzlaFloatingPoint *fp = ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
  return bzla_fp_is_zero(bzla, fp) && bzla_fp_is_neg(bzla, fp);
}

bool
bzla_node_is_fp_const_pos_inf(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_fp_const(exp)) return false;

  BzlaFloatingPoint *fp = ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
  return bzla_fp_is_inf(bzla, fp) && bzla_fp_is_pos(bzla, fp);
}

bool
bzla_node_is_fp_const_neg_inf(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_fp_const(exp)) return false;

  BzlaFloatingPoint *fp = ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
  return bzla_fp_is_inf(bzla, fp) && bzla_fp_is_neg(bzla, fp);
}

bool
bzla_node_is_fp_const_nan(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_fp_const(exp)) return false;

  BzlaFloatingPoint *fp = ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
  return bzla_fp_is_nan(bzla, fp);
}

/*------------------------------------------------------------------------*/

bool
bzla_node_is_rm_const_rna(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_rm_const(exp)) return false;

  return bzla_node_rm_const_get_rm(exp) == BZLA_RM_RNA;
}

bool
bzla_node_is_rm_const_rne(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_rm_const(exp)) return false;

  return bzla_node_rm_const_get_rm(exp) == BZLA_RM_RNE;
}

bool
bzla_node_is_rm_const_rtn(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_rm_const(exp)) return false;

  return bzla_node_rm_const_get_rm(exp) == BZLA_RM_RTN;
}

bool
bzla_node_is_rm_const_rtp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_rm_const(exp)) return false;

  return bzla_node_rm_const_get_rm(exp) == BZLA_RM_RTP;
}

bool
bzla_node_is_rm_const_rtz(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_rm_const(exp)) return false;

  return bzla_node_rm_const_get_rm(exp) == BZLA_RM_RTZ;
}

/*------------------------------------------------------------------------*/

bool
bzla_node_is_bv(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return bzla_sort_is_bv(bzla, bzla_node_get_sort_id(exp));
}

bool
bzla_node_is_rm(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return bzla_sort_is_rm(bzla, bzla_node_get_sort_id(exp));
}

bool
bzla_node_is_fp(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  return bzla_sort_is_fp(bzla, bzla_node_get_sort_id(exp));
}

bool
bzla_node_fp_needs_word_blast(Bzla *bzla, const BzlaNode *exp)
{
  assert(exp);
  exp = bzla_node_real_addr(exp);

  if (exp->parameterized) return false;

  return bzla_node_is_fp(bzla, exp) || bzla_node_is_rm(bzla, exp)
         || exp->kind == BZLA_FP_EQ_NODE || exp->kind == BZLA_FP_IS_INF_NODE
         || exp->kind == BZLA_FP_IS_NAN_NODE || exp->kind == BZLA_FP_IS_NEG_NODE
         || exp->kind == BZLA_FP_IS_NORM_NODE
         || exp->kind == BZLA_FP_IS_POS_NODE
         || exp->kind == BZLA_FP_IS_SUBNORM_NODE
         || exp->kind == BZLA_FP_IS_ZERO_NODE || exp->kind == BZLA_FP_LTE_NODE
         || exp->kind == BZLA_FP_LT_NODE || exp->kind == BZLA_FP_TO_SBV_NODE
         || exp->kind == BZLA_FP_TO_UBV_NODE || exp->kind == BZLA_RM_EQ_NODE;
}

/*------------------------------------------------------------------------*/

static void
inc_exp_ref_counter(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  BzlaNode *real_exp;

  (void) bzla;
  real_exp = bzla_node_real_addr(exp);
  BZLA_ABORT(real_exp->refs == INT32_MAX, "Node reference counter overflow");
  real_exp->refs++;
}

void
bzla_node_inc_ext_ref_counter(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  BzlaNode *real_exp = bzla_node_real_addr(exp);
  BZLA_ABORT(real_exp->ext_refs == INT32_MAX,
             "Node reference counter overflow");
  real_exp->ext_refs += 1;
  bzla->external_refs += 1;
}

void
bzla_node_dec_ext_ref_counter(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bzla_node_real_addr(exp)->ext_refs -= 1;
  bzla->external_refs -= 1;
}

BzlaNode *
bzla_node_copy(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  inc_exp_ref_counter(bzla, exp);
  return exp;
}

/*------------------------------------------------------------------------*/

static inline uint32_t
hash_bv_fp_exp(Bzla *bzla, BzlaNodeKind kind, uint32_t arity, BzlaNode *e[])
{
  uint32_t hash = 0;
  uint32_t i;
#ifndef NDEBUG
  if (bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP) > 0
      && bzla_node_is_binary_commutative_bv_kind(kind))
    assert(arity == 2),
        assert(bzla_node_real_addr(e[0])->id <= bzla_node_real_addr(e[1])->id);
#else
  (void) bzla;
  (void) kind;
#endif
  assert(arity <= NPRIMES);
  for (i = 0; i < arity; i++)
    hash += hash_primes[i] * (uint32_t) bzla_node_real_addr(e[i])->id;
  return hash;
}

static inline uint32_t
hash_slice_exp(BzlaNode *e, uint32_t upper, uint32_t lower)
{
  uint32_t hash;
  assert(upper >= lower);
  hash = hash_primes[0] * (uint32_t) bzla_node_real_addr(e)->id;
  hash += hash_primes[1] * (uint32_t) upper;
  hash += hash_primes[2] * (uint32_t) lower;
  return hash;
}

static inline uint32_t
hash_fp_conversion_exp(BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  uint32_t hash;
  hash = hash_primes[0] * (uint32_t) bzla_node_real_addr(e0)->id;
  if (e1) hash += hash_primes[1] * (uint32_t) bzla_node_real_addr(e1)->id;
  hash += hash_primes[2] * sort;
  return hash;
}

static uint32_t
hash_binder_exp(Bzla *bzla,
                BzlaNode *param,
                BzlaNode *body,
                BzlaIntHashTable *params)
{
  assert(bzla);
  assert(body);

  uint32_t i;
  uint32_t hash = 0;
  BzlaNode *cur, *real_cur;
  BzlaNodePtrStack visit;
  BzlaIntHashTable *marked, *p;
  BzlaPtrHashBucket *b;

  marked = bzla_hashint_table_new(bzla->mm);
  BZLA_INIT_STACK(bzla->mm, visit);
  BZLA_PUSH_STACK(visit, body);

  while (!BZLA_EMPTY_STACK(visit))
  {
    cur      = BZLA_POP_STACK(visit);
    real_cur = bzla_node_real_addr(cur);

    if (bzla_hashint_table_contains(marked, real_cur->id)) continue;

    if (!real_cur->parameterized)
    {
      hash += bzla_node_get_id(cur);
      continue;
    }

    /* paramterized lambda already hashed, we can use already computed hash
     * value instead of recomputing it */
    if (bzla_node_is_lambda(real_cur))
    {
      hash += bzla_hashptr_table_get(bzla->lambdas, real_cur)->data.as_int;
      hash += real_cur->kind;
      hash += real_cur->e[0]->kind;
      continue;
    }
    else if (bzla_node_is_quantifier(real_cur))
    {
      hash += bzla_hashptr_table_get(bzla->quantifiers, real_cur)->data.as_int;
      hash += real_cur->kind;
      hash += real_cur->e[0]->kind;
      /* copy parameters of real_cur to params */
      if (params)
      {
        b = bzla_hashptr_table_get(bzla->parameterized, real_cur);
        if (b)
        {
          assert(b->data.as_ptr);
          p = b->data.as_ptr;
          for (i = 0; i < p->size; i++)
          {
            if (p->keys[i] && p->keys[i] != param->id
                && !bzla_hashint_table_contains(params, p->keys[i]))
              bzla_hashint_table_add(params, p->keys[i]);
          }
        }
      }
      continue;
    }
    else if (bzla_node_is_param(real_cur) && real_cur != param && params)
      bzla_hashint_table_add(params, real_cur->id);

    bzla_hashint_table_add(marked, real_cur->id);
    hash += bzla_node_is_inverted(cur) ? -real_cur->kind : real_cur->kind;
    for (i = 0; i < real_cur->arity; i++)
      BZLA_PUSH_STACK(visit, real_cur->e[i]);
  }
  BZLA_RELEASE_STACK(visit);
  bzla_hashint_table_delete(marked);
  return hash;
}

/* Computes hash value of expresssion by children ids */
static uint32_t
compute_hash_exp(Bzla *bzla, BzlaNode *exp, uint32_t table_size)
{
  assert(exp);
  assert(table_size > 0);
  assert(bzla_util_is_power_of_2(table_size));
  assert(bzla_node_is_regular(exp));
  assert(!bzla_node_is_var(exp));
  assert(!bzla_node_is_uf(exp));

  uint32_t hash = 0;

  if (bzla_node_is_bv_const(exp))
  {
    hash = bzla_bv_hash(bzla_node_bv_const_get_bits(exp));
  }
  else if (bzla_node_is_rm_const(exp))
  {
    hash = bzla_rm_hash(bzla_node_rm_const_get_rm(exp));
  }
  else if (bzla_node_is_fp_const(exp))
  {
    hash = bzla_fp_hash(bzla_node_fp_const_get_fp(exp));
  }
  /* hash for lambdas is computed once during creation. afterwards, we always
   * have to use the saved hash value since hashing of lambdas requires all
   * parameterized nodes and their inputs (cf. hash_binder_exp), which may
   * change at some point. */
  else if (bzla_node_is_lambda(exp))
  {
    hash = bzla_hashptr_table_get(exp->bzla->lambdas, (BzlaNode *) exp)
               ->data.as_int;
  }
  else if (bzla_node_is_quantifier(exp))
  {
    hash = bzla_hashptr_table_get(exp->bzla->quantifiers, exp)->data.as_int;
  }
  else if (exp->kind == BZLA_BV_SLICE_NODE)
  {
    hash = hash_slice_exp(exp->e[0],
                          bzla_node_bv_slice_get_upper(exp),
                          bzla_node_bv_slice_get_lower(exp));
  }
  else if (exp->kind == BZLA_FP_TO_FP_BV_NODE)
  {
    hash = hash_fp_conversion_exp(exp->e[0], 0, bzla_node_get_sort_id(exp));
  }
  else if (exp->kind == BZLA_FP_TO_SBV_NODE || exp->kind == BZLA_FP_TO_UBV_NODE
           || exp->kind == BZLA_FP_TO_FP_FP_NODE
           || exp->kind == BZLA_FP_TO_FP_SBV_NODE
           || exp->kind == BZLA_FP_TO_FP_UBV_NODE)
  {
    hash = hash_fp_conversion_exp(
        exp->e[0], exp->e[1], bzla_node_get_sort_id(exp));
  }
  else
  {
    hash = hash_bv_fp_exp(bzla, exp->kind, exp->arity, exp->e);
  }
  hash &= table_size - 1;
  return hash;
}

/*------------------------------------------------------------------------*/

static void
setup_node_and_add_to_id_table(Bzla *bzla, void *ptr)
{
  assert(bzla);
  assert(ptr);

  BzlaNode *exp;
  uint32_t id;

  exp = (BzlaNode *) ptr;
  assert(!bzla_node_is_inverted(exp));
  assert(!exp->id);

  exp->refs = 1;
  exp->bzla = bzla;
  bzla->stats.expressions++;
  id = BZLA_COUNT_STACK(bzla->nodes_id_table);
  BZLA_ABORT(id == INT32_MAX, "expression id overflow");
  exp->id = id;
  BZLA_PUSH_STACK(bzla->nodes_id_table, exp);
  assert(BZLA_COUNT_STACK(bzla->nodes_id_table) == (size_t) exp->id + 1);
  assert(BZLA_PEEK_STACK(bzla->nodes_id_table, exp->id) == exp);
  bzla->stats.node_bytes_alloc += exp->bytes;

  if (bzla_node_is_apply(exp)) exp->apply_below = 1;
}

/* Enlarges unique table and rehashes expressions. */
static void
enlarge_nodes_unique_table(Bzla *bzla)
{
  assert(bzla);

  BzlaMemMgr *mm;
  uint32_t size, new_size, i;
  uint32_t hash;
  BzlaNode *cur, *temp, **new_chains;

  mm       = bzla->mm;
  size     = bzla->nodes_unique_table.size;
  new_size = size ? 2 * size : 1;
  BZLA_CNEWN(mm, new_chains, new_size);
  for (i = 0; i < size; i++)
  {
    cur = bzla->nodes_unique_table.chains[i];
    while (cur)
    {
      assert(bzla_node_is_regular(cur));
      assert(!bzla_node_is_var(cur));
      assert(!bzla_node_is_uf(cur));
      temp             = cur->next;
      hash             = compute_hash_exp(bzla, cur, new_size);
      cur->next        = new_chains[hash];
      new_chains[hash] = cur;
      cur              = temp;
    }
  }
  BZLA_DELETEN(mm, bzla->nodes_unique_table.chains, size);
  bzla->nodes_unique_table.size   = new_size;
  bzla->nodes_unique_table.chains = new_chains;
}

static void
remove_from_nodes_unique_table_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));

  uint32_t hash;
  BzlaNode *cur, *prev;

  if (!exp->unique) return;

  assert(bzla);
  assert(bzla->nodes_unique_table.num_elements > 0);

  hash = compute_hash_exp(bzla, exp, bzla->nodes_unique_table.size);
  prev = 0;
  cur  = bzla->nodes_unique_table.chains[hash];

  while (cur != exp)
  {
    assert(cur);
    assert(bzla_node_is_regular(cur));
    prev = cur;
    cur  = cur->next;
  }
  assert(cur);
  if (!prev)
    bzla->nodes_unique_table.chains[hash] = cur->next;
  else
    prev->next = cur->next;

  bzla->nodes_unique_table.num_elements--;

  exp->unique = 0; /* NOTE: this is not debugging code ! */
  exp->next   = 0;
}

static void
remove_from_hash_tables(Bzla *bzla, BzlaNode *exp, bool keep_symbol)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(!bzla_node_is_invalid(exp));

  BzlaHashTableData data;

  switch (exp->kind)
  {
    case BZLA_VAR_NODE:
      bzla_hashptr_table_remove(bzla->bv_vars, exp, 0, 0);
      break;
    case BZLA_LAMBDA_NODE:
      bzla_hashptr_table_remove(bzla->lambdas, exp, 0, 0);
      break;
    case BZLA_FORALL_NODE:
    case BZLA_EXISTS_NODE:
      bzla_hashptr_table_remove(bzla->quantifiers, exp, 0, 0);
      break;
    case BZLA_UF_NODE: bzla_hashptr_table_remove(bzla->ufs, exp, 0, 0); break;
    case BZLA_FUN_EQ_NODE:
      if (!exp->parameterized)
      {
        bzla_hashptr_table_remove(bzla->feqs, exp, 0, 0);
      }
      break;
    default: break;
  }

  if (!keep_symbol && bzla_hashptr_table_get(bzla->node2symbol, exp))
  {
    bzla_hashptr_table_remove(bzla->node2symbol, exp, 0, &data);
    if (data.as_str)
    {
      bzla_mem_freestr(bzla->mm, data.as_str);
    }
  }

  if (!keep_symbol
      && bzla_hashptr_table_get(bzla->node2symbol, bzla_node_invert(exp)))
  {
    bzla_hashptr_table_remove(
        bzla->node2symbol, bzla_node_invert(exp), 0, &data);
    if (data.as_str)
    {
      bzla_mem_freestr(bzla->mm, data.as_str);
    }
  }

  if (bzla_hashptr_table_get(bzla->parameterized, exp))
  {
    bzla_hashptr_table_remove(bzla->parameterized, exp, 0, &data);
    assert(data.as_ptr);
    bzla_hashint_table_delete(data.as_ptr);
  }
}

/*------------------------------------------------------------------------*/

/* Connects child to its parent and updates list of parent pointers.
 * Expressions are inserted at the beginning of the regular parent list
 */
static void
connect_child_exp(Bzla *bzla, BzlaNode *parent, BzlaNode *child, uint32_t pos)
{
  assert(bzla);
  assert(parent);
  assert(bzla_node_is_regular(parent));
  assert(bzla == parent->bzla);
  assert(child);
  assert(bzla == bzla_node_real_addr(child)->bzla);
  assert(pos <= BZLA_NODE_MAX_CHILDREN - 1);
  assert(bzla_simplify_exp(bzla, child) == child);
  assert(!bzla_node_is_args(child) || bzla_node_is_args(parent)
         || bzla_node_is_apply(parent) || bzla_node_is_update(parent));

  (void) bzla;
  uint32_t tag;
  bool insert_beginning = 1;
  BzlaNode *real_child, *first_parent, *last_parent, *tagged_parent;

  /* set specific flags */

  /* set parent parameterized if child is parameterized */
  if (!bzla_node_is_binder(parent) && bzla_node_real_addr(child)->parameterized)
    parent->parameterized = 1;

  // TODO (ma): why don't we bind params here?

  if (bzla_node_is_fun_cond(parent) && bzla_node_real_addr(child)->is_array)
    parent->is_array = 1;

  if (bzla_node_real_addr(child)->lambda_below) parent->lambda_below = 1;

  if (bzla_node_real_addr(child)->quantifier_below)
    parent->quantifier_below = 1;

  if (bzla_node_real_addr(child)->rebuild) parent->rebuild = 1;

  if (bzla_node_real_addr(child)->apply_below) parent->apply_below = 1;

  bzla_node_real_addr(child)->parents++;
  inc_exp_ref_counter(bzla, child);

  /* update parent lists */

  if (bzla_node_is_apply(parent)) insert_beginning = false;

  real_child     = bzla_node_real_addr(child);
  parent->e[pos] = child;
  tagged_parent  = bzla_node_set_tag(parent, pos);

  assert(!parent->prev_parent[pos]);
  assert(!parent->next_parent[pos]);

  /* no parent so far? */
  if (!real_child->first_parent)
  {
    assert(!real_child->last_parent);
    real_child->first_parent = tagged_parent;
    real_child->last_parent  = tagged_parent;
  }
  /* add parent at the beginning of the list */
  else if (insert_beginning)
  {
    first_parent = real_child->first_parent;
    assert(first_parent);
    parent->next_parent[pos] = first_parent;
    tag                      = bzla_node_get_tag(first_parent);
    bzla_node_real_addr(first_parent)->prev_parent[tag] = tagged_parent;
    real_child->first_parent                            = tagged_parent;
  }
  /* add parent at the end of the list */
  else
  {
    last_parent = real_child->last_parent;
    assert(last_parent);
    parent->prev_parent[pos] = last_parent;
    tag                      = bzla_node_get_tag(last_parent);
    bzla_node_real_addr(last_parent)->next_parent[tag] = tagged_parent;
    real_child->last_parent                            = tagged_parent;
  }
}

/* Disconnects a child from its parent and updates its parent list */
static void
disconnect_child_exp(Bzla *bzla, BzlaNode *parent, uint32_t pos)
{
  assert(bzla);
  assert(parent);
  assert(bzla_node_is_regular(parent));
  assert(bzla == parent->bzla);
  assert(!bzla_node_is_bv_const(parent));
  assert(!bzla_node_is_var(parent));
  assert(!bzla_node_is_uf(parent));
  assert(pos <= BZLA_NODE_MAX_CHILDREN - 1);

  (void) bzla;
  BzlaNode *first_parent, *last_parent;
  BzlaNode *real_child, *tagged_parent;

  tagged_parent = bzla_node_set_tag(parent, pos);
  real_child    = bzla_node_real_addr(parent->e[pos]);
  real_child->parents--;
  first_parent = real_child->first_parent;
  last_parent  = real_child->last_parent;
  assert(first_parent);
  assert(last_parent);

  /* if a parameter is disconnected from a lambda we have to reset
   * 'lambda_exp' of the parameter in order to keep a valid state */
  if (bzla_node_is_binder(parent)
      && pos == 0
      /* if parent gets rebuilt via substitute_and_rebuild, it might
       * result in a new binder term, where the param is already reused.
       * if this is the case param is already bound by a different binder
       * and we are not allowed to reset param->binder to 0. */
      && bzla_node_param_get_binder(parent->e[0]) == parent)
    bzla_node_param_set_binder(parent->e[0], 0);

  /* only one parent? */
  if (first_parent == tagged_parent && first_parent == last_parent)
  {
    assert(!parent->next_parent[pos]);
    assert(!parent->prev_parent[pos]);
    real_child->first_parent = 0;
    real_child->last_parent  = 0;
  }
  /* is parent first parent in the list? */
  else if (first_parent == tagged_parent)
  {
    assert(parent->next_parent[pos]);
    assert(!parent->prev_parent[pos]);
    real_child->first_parent                   = parent->next_parent[pos];
    BZLA_PREV_PARENT(real_child->first_parent) = 0;
  }
  /* is parent last parent in the list? */
  else if (last_parent == tagged_parent)
  {
    assert(!parent->next_parent[pos]);
    assert(parent->prev_parent[pos]);
    real_child->last_parent                   = parent->prev_parent[pos];
    BZLA_NEXT_PARENT(real_child->last_parent) = 0;
  }
  /* detach parent from list */
  else
  {
    assert(parent->next_parent[pos]);
    assert(parent->prev_parent[pos]);
    BZLA_PREV_PARENT(parent->next_parent[pos]) = parent->prev_parent[pos];
    BZLA_NEXT_PARENT(parent->prev_parent[pos]) = parent->next_parent[pos];
  }
  parent->next_parent[pos] = 0;
  parent->prev_parent[pos] = 0;
  parent->e[pos]           = 0;
}

/* Disconnect children of expression in parent list and if applicable from
 * unique table.  Do not touch local data, nor any reference counts.  The
 * kind of the expression becomes 'BZLA_DISCONNECTED_NODE' in debugging mode.
 *
 * Actually we have the sequence
 *
 *   UNIQUE -> !UNIQUE -> ERASED -> DISCONNECTED -> INVALID
 *
 * after a unique or non uninque expression is allocated until it is
 * deallocated.  We also have loop back from DISCONNECTED to !UNIQUE
 * if an expression is rewritten and reused as PROXY.
 */
static void
disconnect_children_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(!bzla_node_is_invalid(exp));
  assert(!exp->unique);
  assert(exp->erased);
  assert(!exp->disconnected);

  uint32_t i;

  for (i = 0; i < exp->arity; i++) disconnect_child_exp(bzla, exp, i);
  exp->disconnected = 1;
}

/*------------------------------------------------------------------------*/

/* Delete local data of expression.
 *
 * Virtual reads and simplified expressions have to be handled by the
 * calling function, e.g. 'bzla_node_release', to avoid recursion.
 *
 * We use this function to update operator stats
 */
static void
erase_local_data_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  assert(bzla_node_is_regular(exp));

  assert(!exp->unique);
  assert(!exp->erased);
  assert(!exp->disconnected);
  assert(!bzla_node_is_invalid(exp));

  BzlaMemMgr *mm;
  BzlaPtrHashTable *static_rho;
  BzlaPtrHashTableIterator it;

  mm = bzla->mm;
  //  BZLALOG ("%s: %s", __FUNCTION__, bzla_util_node2string (exp));

  switch (exp->kind)
  {
    case BZLA_BV_CONST_NODE: {
      bzla_bv_free(mm, bzla_node_bv_const_get_bits_ptr(exp));
      if (bzla_node_bv_const_get_invbits_ptr(exp))
      {
        bzla_bv_free(mm, bzla_node_bv_const_get_invbits_ptr(exp));
      }
      bzla_node_bv_const_set_bits(exp, 0);
      bzla_node_bv_const_set_invbits(exp, 0);
    }
      break;
    case BZLA_FP_CONST_NODE:
      bzla_fp_free(bzla, bzla_node_fp_const_get_fp(exp));
      bzla_node_fp_const_set_fp(exp, 0);
      break;
    case BZLA_LAMBDA_NODE:
    case BZLA_UPDATE_NODE:
    case BZLA_UF_NODE:
      if (exp->kind == BZLA_LAMBDA_NODE)
      {
        static_rho = bzla_node_lambda_get_static_rho(exp);
        if (static_rho)
        {
          bzla_iter_hashptr_init(&it, static_rho);
          while (bzla_iter_hashptr_has_next(&it))
          {
            bzla_node_release(bzla, it.bucket->data.as_ptr);
            bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
          }
          bzla_hashptr_table_delete(static_rho);
          ((BzlaLambdaNode *) exp)->static_rho = 0;
        }
      }
      if (exp->rho)
      {
        bzla_hashptr_table_delete(exp->rho);
        exp->rho = 0;
      }
      break;
    case BZLA_COND_NODE:
      if (bzla_node_is_fun_cond(exp) && exp->rho)
      {
        bzla_hashptr_table_delete(exp->rho);
        exp->rho = 0;
      }
      break;
    case BZLA_RM_CONST_NODE: /* nothing extra to do */
    default: break;
  }

  if (exp->av)
  {
    bzla_aigvec_release_delete(bzla->avmgr, exp->av);
    exp->av = 0;
  }
  exp->erased = 1;
}

static void
really_deallocate_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla == exp->bzla);
  assert(!exp->unique);
  assert(exp->disconnected);
  assert(exp->erased);
  assert(exp->id);
  assert(BZLA_PEEK_STACK(bzla->nodes_id_table, exp->id) == exp);
  BZLA_POKE_STACK(bzla->nodes_id_table, exp->id, 0);

  BzlaMemMgr *mm;

  mm = bzla->mm;

  set_kind(bzla, exp, BZLA_INVALID_NODE);

  assert(bzla_node_get_sort_id(exp));
  bzla_sort_release(bzla, bzla_node_get_sort_id(exp));
  bzla_node_set_sort_id(exp, 0);

  bzla_mem_free(mm, exp, exp->bytes);
}

static void
recursively_release_exp(Bzla *bzla, BzlaNode *root)
{
  assert(bzla);
  assert(root);
  assert(bzla_node_is_regular(root));
  assert(root->refs == 1);

  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  BzlaNode *cur;
  uint32_t i;

  mm = bzla->mm;

  BZLA_INIT_STACK(mm, stack);
  cur = root;
  goto RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP;

  do
  {
    cur = BZLA_POP_STACK(stack);
    cur = bzla_node_real_addr(cur);
    assert(cur);

    if (cur->refs > 1)
    {
      cur->refs--;
    }
    else
    {
    RECURSIVELY_RELEASE_NODE_ENTER_WITHOUT_POP:
      assert(cur->refs == 1);
      assert(!cur->ext_refs || cur->ext_refs == 1);
      assert(cur->parents == 0);

      for (i = 1; i <= cur->arity; i++)
      {
        assert(cur->e[cur->arity - i]);
        BZLA_PUSH_STACK(stack, cur->e[cur->arity - i]);
      }

      if (cur->simplified)
      {
        BZLA_PUSH_STACK(stack, cur->simplified);
        cur->simplified = 0;
      }

      remove_from_nodes_unique_table_exp(bzla, cur);
      erase_local_data_exp(bzla, cur);

      /* It is safe to access the children here, since they are pushed
       * on the stack and will be released later if necessary.
       */
      remove_from_hash_tables(bzla, cur, 0);
      disconnect_children_exp(bzla, cur);
      really_deallocate_exp(bzla, cur);
    }
  } while (!BZLA_EMPTY_STACK(stack));
  BZLA_RELEASE_STACK(stack);
}

void
bzla_node_release(Bzla *bzla, BzlaNode *root)
{
  assert(bzla);
  assert(root);
  assert(bzla == bzla_node_real_addr(root)->bzla);

  root = bzla_node_real_addr(root);

  assert(root->refs > 0);

  if (root->refs > 1)
    root->refs--;
  else
    recursively_release_exp(bzla, root);
}

/*------------------------------------------------------------------------*/

void
bzla_node_set_to_proxy(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla == exp->bzla);
  assert(bzla_node_is_simplified(exp));
  assert(!bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));

  uint32_t i;
  BzlaNode *e[BZLA_NODE_MAX_CHILDREN];

  remove_from_nodes_unique_table_exp(bzla, exp);
  /* also updates op stats */
  erase_local_data_exp(bzla, exp);
  assert(exp->arity <= BZLA_NODE_MAX_CHILDREN);
  BZLA_CLR(e);
  for (i = 0; i < exp->arity; i++) e[i] = exp->e[i];
  remove_from_hash_tables(bzla, exp, 1);
  disconnect_children_exp(bzla, exp);

  for (i = 0; i < exp->arity; i++) bzla_node_release(bzla, e[i]);

  set_kind(bzla, exp, BZLA_PROXY_NODE);

  exp->disconnected  = 0;
  exp->erased        = 0;
  exp->arity         = 0;
  exp->parameterized = 0;
}

/*------------------------------------------------------------------------*/

void
bzla_node_set_bzla_id(Bzla *bzla, BzlaNode *exp, int32_t id)
{
  assert(bzla);
  assert(exp);
  assert(id);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(bzla_node_is_var(exp) || bzla_node_is_uf_array(exp));

  (void) bzla;
  BzlaNode *real_exp;
  BzlaPtrHashBucket *b;

  real_exp = bzla_node_real_addr(exp);
  b        = bzla_hashptr_table_get(bzla->inputs, real_exp);
  assert(b);
  b->data.as_int = id;
}

int32_t
bzla_node_get_bzla_id(BzlaNode *exp)
{
  assert(exp);

  int32_t id = 0;
  Bzla *bzla;
  BzlaNode *real_exp;
  BzlaPtrHashBucket *b;

  real_exp = bzla_node_real_addr(exp);
  bzla     = real_exp->bzla;

  if ((b = bzla_hashptr_table_get(bzla->inputs, real_exp))) id = b->data.as_int;
  if (bzla_node_is_inverted(exp)) return -id;
  return id;
}

BzlaNode *
bzla_node_match_by_id(Bzla *bzla, int32_t id)
{
  assert(bzla);
  assert(id > 0);
  if ((size_t) id >= BZLA_COUNT_STACK(bzla->nodes_id_table)) return 0;
  BzlaNode *exp = BZLA_PEEK_STACK(bzla->nodes_id_table, id);
  if (!exp) return 0;
  return bzla_node_copy(bzla, exp);
}

BzlaNode *
bzla_node_get_by_id(Bzla *bzla, int32_t id)
{
  assert(bzla);
  bool is_inverted = id < 0;
  id               = abs(id);
  if ((size_t) id >= BZLA_COUNT_STACK(bzla->nodes_id_table)) return 0;
  BzlaNode *res = BZLA_PEEK_STACK(bzla->nodes_id_table, id);
  if (!res) return 0;
  return is_inverted ? bzla_node_invert(res) : res;
}

/*------------------------------------------------------------------------*/

char *
bzla_node_get_symbol(Bzla *bzla, const BzlaNode *exp)
{
  /* do not pointer-chase! */
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  BzlaPtrHashBucket *b;

  b = bzla_hashptr_table_get(bzla->node2symbol, exp);
  if (b) return b->data.as_str;
  return 0;
}

void
bzla_node_set_symbol(Bzla *bzla, BzlaNode *exp, const char *symbol)
{
  /* do not pointer-chase! */
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(symbol);

  BzlaPtrHashBucket *b;
  char *sym;

  sym = bzla_mem_strdup(bzla->mm, symbol);
  b = bzla_hashptr_table_get(bzla->node2symbol, exp);

  if (b)
  {
    bzla_mem_freestr(bzla->mm, b->data.as_str);
  }
  else
  {
    b = bzla_hashptr_table_add(bzla->node2symbol, exp);
  }

  b->data.as_str = sym;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_match(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  uint32_t id;
  BzlaNode *res;

  id = bzla_node_real_addr(exp)->id;
  assert(id > 0);
  if (id >= BZLA_COUNT_STACK(bzla->nodes_id_table)) return 0;
  res = bzla_node_copy(bzla, BZLA_PEEK_STACK(bzla->nodes_id_table, id));
  return bzla_node_is_inverted(exp) ? bzla_node_invert(res) : res;
}

/*------------------------------------------------------------------------*/

/* Compares expressions by id */
int32_t
bzla_node_compare_by_id(const BzlaNode *exp0, const BzlaNode *exp1)
{
  assert(exp0);
  assert(exp1);

  uint32_t id0, id1;

  id0 = bzla_node_get_id(exp0);
  id1 = bzla_node_get_id(exp1);
  if (id0 < id1) return -1;
  if (id0 > id1) return 1;
  return 0;
}

int32_t
bzla_node_compare_by_id_qsort_desc(const void *p, const void *q)
{
  BzlaNode *a = bzla_node_real_addr(*(BzlaNode **) p);
  BzlaNode *b = bzla_node_real_addr(*(BzlaNode **) q);
  return b->id - a->id;
}

int32_t
bzla_node_compare_by_id_qsort_asc(const void *p, const void *q)
{
  BzlaNode *a = bzla_node_real_addr(*(BzlaNode **) p);
  BzlaNode *b = bzla_node_real_addr(*(BzlaNode **) q);
  return a->id - b->id;
}

/* Computes hash value of expression by id */
uint32_t
bzla_node_hash_by_id(const BzlaNode *exp)
{
  assert(exp);
  return (uint32_t) bzla_node_get_id(exp) * 7334147u;
}

/*------------------------------------------------------------------------*/

uint32_t
bzla_node_bv_get_width(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_bv(bzla, exp));
  return bzla_sort_bv_get_width(bzla, bzla_node_get_sort_id(exp));
}

uint32_t
bzla_node_fp_get_exp_width(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_fp(bzla, exp));
  return bzla_sort_fp_get_exp_width(bzla, bzla_node_get_sort_id(exp));
}

uint32_t
bzla_node_fp_get_sig_width(Bzla *bzla, const BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  assert(bzla_node_is_fp(bzla, exp));
  return bzla_sort_fp_get_sig_width(bzla, bzla_node_get_sort_id(exp));
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_node_bv_const_get_bits(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_bv_const(exp));
  if (bzla_node_is_regular(exp))
  {
    return bzla_node_bv_const_get_bits_ptr(exp);
  }
  return bzla_node_bv_const_get_invbits_ptr(exp);
}

BzlaBitVector *
bzla_node_bv_const_get_bits_ptr(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_bv_const(exp));
  return ((BzlaBVConstNode *) bzla_node_real_addr(exp))->bits;
}

BzlaBitVector *
bzla_node_bv_const_get_invbits_ptr(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_bv_const(exp));
  return ((BzlaBVConstNode *) bzla_node_real_addr(exp))->invbits;
}

void
bzla_node_bv_const_set_bits(BzlaNode *exp, BzlaBitVector *bits)
{
  assert(exp);
  assert(bzla_node_is_bv_const(exp));
  ((BzlaBVConstNode *) bzla_node_real_addr(exp))->bits = bits;
}

void
bzla_node_bv_const_set_invbits(BzlaNode *exp, BzlaBitVector *bits)
{
  assert(exp);
  assert(bzla_node_is_bv_const(exp));
  ((BzlaBVConstNode *) bzla_node_real_addr(exp))->invbits = bits;
}

/*------------------------------------------------------------------------*/

BzlaRoundingMode
bzla_node_rm_const_get_rm(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_rm_const(exp));
  return ((BzlaRMConstNode *) bzla_node_real_addr(exp))->rm;
}

/*------------------------------------------------------------------------*/

void
bzla_node_fp_const_set_fp(BzlaNode *exp, BzlaFloatingPoint *fp)
{
  assert(exp);
  assert(bzla_node_is_fp_const(exp));
  ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp = fp;
}

BzlaFloatingPoint *
bzla_node_fp_const_get_fp(BzlaNode *exp)
{
  assert(exp);
  assert(bzla_node_is_fp_const(exp));
  return ((BzlaFPConstNode *) bzla_node_real_addr(exp))->fp;
}

/*------------------------------------------------------------------------*/

uint32_t
bzla_node_fun_get_arity(Bzla *bzla, BzlaNode *exp)
{
  (void) bzla;
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla_sort_is_fun(bzla, bzla_node_get_sort_id(exp)));
  return bzla_sort_fun_get_arity(bzla, bzla_node_get_sort_id(exp));
}

uint32_t
bzla_node_args_get_arity(Bzla *bzla, BzlaNode *exp)
{
  (void) bzla;
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_node_is_regular(exp));
  assert(bzla_node_is_args(exp));
  return bzla_sort_tuple_get_arity(bzla, bzla_node_get_sort_id(exp));
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_binder_get_body(BzlaNode *binder)
{
  assert(bzla_node_is_regular(binder));
  assert(bzla_node_is_binder(binder));
  return ((BzlaBinderNode *) binder)->body;
}

void
bzla_node_binder_set_body(BzlaNode *binder, BzlaNode *body)
{
  assert(bzla_node_is_regular(binder));
  assert(bzla_node_is_binder(binder));
  ((BzlaBinderNode *) binder)->body = body;
}

/*------------------------------------------------------------------------*/

BzlaPtrHashTable *
bzla_node_lambda_get_static_rho(BzlaNode *lambda)
{
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));
  return ((BzlaLambdaNode *) lambda)->static_rho;
}

void
bzla_node_lambda_set_static_rho(BzlaNode *lambda, BzlaPtrHashTable *static_rho)
{
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));
  ((BzlaLambdaNode *) lambda)->static_rho = static_rho;
}

BzlaPtrHashTable *
bzla_node_lambda_copy_static_rho(Bzla *bzla, BzlaNode *lambda)
{
  assert(bzla_node_is_regular(lambda));
  assert(bzla_node_is_lambda(lambda));
  assert(bzla_node_lambda_get_static_rho(lambda));

  BzlaNode *data, *key;
  BzlaPtrHashTableIterator it;
  BzlaPtrHashTable *static_rho;

  bzla_iter_hashptr_init(&it, bzla_node_lambda_get_static_rho(lambda));
  static_rho = bzla_hashptr_table_new(bzla->mm,
                                      (BzlaHashPtr) bzla_node_hash_by_id,
                                      (BzlaCmpPtr) bzla_node_compare_by_id);
  while (bzla_iter_hashptr_has_next(&it))
  {
    data = bzla_node_copy(bzla, it.bucket->data.as_ptr);
    key  = bzla_node_copy(bzla, bzla_iter_hashptr_next(&it));
    bzla_hashptr_table_add(static_rho, key)->data.as_ptr = data;
  }
  return static_rho;
}

void
bzla_node_lambda_delete_static_rho(Bzla *bzla, BzlaNode *lambda)
{
  BzlaPtrHashTable *static_rho;
  BzlaPtrHashTableIterator it;

  static_rho = bzla_node_lambda_get_static_rho(lambda);
  if (!static_rho) return;

  bzla_iter_hashptr_init(&it, static_rho);
  while (bzla_iter_hashptr_has_next(&it))
  {
    bzla_node_release(bzla, it.bucket->data.as_ptr);
    bzla_node_release(bzla, bzla_iter_hashptr_next(&it));
  }
  bzla_hashptr_table_delete(static_rho);
  bzla_node_lambda_set_static_rho(lambda, 0);
}

/*------------------------------------------------------------------------*/

uint32_t
bzla_node_bv_slice_get_upper(const BzlaNode *slice)
{
  assert(bzla_node_is_bv_slice(slice));
  return ((BzlaBVSliceNode *) bzla_node_real_addr(slice))->upper;
}

uint32_t
bzla_node_bv_slice_get_lower(const BzlaNode *slice)
{
  assert(bzla_node_is_bv_slice(slice));
  return ((BzlaBVSliceNode *) bzla_node_real_addr(slice))->lower;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_param_get_binder(BzlaNode *param)
{
  assert(bzla_node_is_param(param));
  return ((BzlaParamNode *) bzla_node_real_addr(param))->binder;
}

void
bzla_node_param_set_binder(BzlaNode *param, BzlaNode *binder)
{
  assert(bzla_node_is_param(param));
  assert(!binder || bzla_node_is_binder(binder));

  BzlaNode *q;

  /* param is not bound anymore, remove from exists/forall vars tables */
  if (!binder)
  {
    q = bzla_node_param_get_binder(param);
    if (q)
    {
      if (bzla_node_is_exists(q))
        bzla_hashptr_table_remove(param->bzla->exists_vars, param, 0, 0);
      else if (bzla_node_is_forall(q))
        bzla_hashptr_table_remove(param->bzla->forall_vars, param, 0, 0);
    }
  }
  /* param is bound, add to exists/forall vars tables */
  else
  {
    if (bzla_node_is_exists(binder))
      (void) bzla_hashptr_table_add(param->bzla->exists_vars, param);
    else if (bzla_node_is_forall(binder))
      (void) bzla_hashptr_table_add(param->bzla->forall_vars, param);
  }
  ((BzlaParamNode *) bzla_node_real_addr(param))->binder = binder;
}

bool
bzla_node_param_is_bound(BzlaNode *param)
{
  assert(bzla_node_is_param(param));
  return bzla_node_param_get_binder(param) != 0;
}

bool
bzla_node_param_is_exists_var(BzlaNode *param)
{
  assert(bzla_node_is_param(param));
  return bzla_node_param_is_bound(param)
         && bzla_node_is_exists(bzla_node_param_get_binder(param));
}

bool
bzla_node_param_is_forall_var(BzlaNode *param)
{
  assert(bzla_node_is_param(param));
  return bzla_node_param_is_bound(param)
         && bzla_node_is_forall(bzla_node_param_get_binder(param));
}

BzlaNode *
bzla_node_param_get_assigned_exp(BzlaNode *param)
{
  assert(bzla_node_is_param(param));
  return ((BzlaParamNode *) bzla_node_real_addr(param))->assigned_exp;
}

BzlaNode *
bzla_node_param_set_assigned_exp(BzlaNode *param, BzlaNode *exp)
{
  assert(bzla_node_is_param(param));
  assert(!exp || bzla_node_get_sort_id(param) == bzla_node_get_sort_id(exp));
  return ((BzlaParamNode *) bzla_node_real_addr(param))->assigned_exp = exp;
}

/*------------------------------------------------------------------------*/

static bool
is_sorted_binary_bv_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e[])
{
  if (!bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP)) return 1;
  if (!bzla_node_is_binary_commutative_bv_kind(kind)) return 1;
  if (e[0] == e[1]) return 1;
  if (bzla_node_invert(e[0]) == e[1] && bzla_node_is_inverted(e[1])) return 1;
  return bzla_node_real_addr(e[0])->id <= bzla_node_real_addr(e[1])->id;
}

static bool
is_sorted_binary_fp_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e[])
{
  if (!bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP)) return 1;
  if (!bzla_node_is_binary_commutative_fp_kind(kind)) return 1;
  assert(bzla_node_is_regular(e[1]));
  assert(bzla_node_is_regular(e[2]));
  if (e[1] == e[2]) return 1;
  return e[1]->id <= e[2]->id;
}

static bool
is_sorted_fp_fma_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e[])
{
  if (!bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP)) return 1;
  if (kind != BZLA_FP_FMA_NODE) return 1;
  assert(bzla_node_is_regular(e[1]));
  assert(bzla_node_is_regular(e[2]));
  if (e[1] == e[2]) return 1;
  return e[1]->id <= e[2]->id;
}

/*------------------------------------------------------------------------*/

/**
 * Search for bit-vector const expression in hash table.
 * Returns 0 if not found.
 */
static BzlaNode **
find_bv_const_exp(Bzla *bzla, BzlaBitVector *bits)
{
  assert(bzla);
  assert(bits);

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = bzla_bv_hash(bits);
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (bzla_node_is_bv_const(cur)
        && bzla_node_bv_get_width(bzla, cur) == bzla_bv_get_width(bits)
        && bzla_bv_compare(bzla_node_bv_const_get_bits(cur), bits) == 0)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/**
 * Search for roundingmode const expression in hash table.
 * Returns 0 if not found.
 */
static BzlaNode **
find_rm_const_exp(Bzla *bzla, const BzlaRoundingMode rm)
{
  assert(bzla);
  assert(bzla_rm_is_valid(rm));

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = bzla_rm_hash(rm);
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (bzla_node_is_rm_const(cur) && bzla_node_rm_const_get_rm(cur) == rm)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/**
 * Search for floating-point const expression in hash table.
 * Returns 0 if not found.
 */
static BzlaNode **
find_fp_const_exp(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = bzla_fp_hash(fp);
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (bzla_node_is_fp_const(cur)
        && !bzla_fp_compare(bzla_node_fp_const_get_fp(cur), fp))
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/* Search for slice expression in hash table. Returns 0 if not found. */
static BzlaNode **
find_slice_exp(Bzla *bzla, BzlaNode *e0, uint32_t upper, uint32_t lower)
{
  assert(bzla);
  assert(e0);
  assert(upper >= lower);

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = hash_slice_exp(e0, upper, lower);
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (cur->kind == BZLA_BV_SLICE_NODE && cur->e[0] == e0
        && bzla_node_bv_slice_get_upper(cur) == upper
        && bzla_node_bv_slice_get_lower(cur) == lower)
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

/**
 * Search for floating-point conversion expression in hash table.
 * Returns 0 if not found.
 */
static BzlaNode **
find_fp_conversion_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  assert(bzla);
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || kind == BZLA_FP_TO_FP_BV_NODE || kind == BZLA_FP_TO_FP_FP_NODE
         || kind == BZLA_FP_TO_FP_SBV_NODE || kind == BZLA_FP_TO_FP_UBV_NODE);
  assert(e0);
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || bzla_sort_is_fp(bzla, sort));
  assert((kind != BZLA_FP_TO_SBV_NODE && kind != BZLA_FP_TO_UBV_NODE)
         || bzla_sort_is_bv(bzla, sort));

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = hash_fp_conversion_exp(e0, e1, sort);
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (cur->kind == kind && cur->e[0] == e0 && (!e1 || cur->e[1] == e1)
        && sort == bzla_node_get_sort_id(cur))
    {
      break;
    }
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  return result;
}

static BzlaNode **
find_bv_fp_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e[], uint32_t arity)
{
  bool equal;
  uint32_t i;
  uint32_t hash;
  BzlaNode *cur, **result;

  assert(kind != BZLA_BV_SLICE_NODE);
  assert(kind != BZLA_BV_CONST_NODE);
  assert(kind != BZLA_FP_CONST_NODE);
  assert(kind != BZLA_FP_TO_SBV_NODE);
  assert(kind != BZLA_FP_TO_UBV_NODE);
  assert(kind != BZLA_FP_TO_FP_BV_NODE);
  assert(kind != BZLA_FP_TO_FP_FP_NODE);
  assert(kind != BZLA_FP_TO_FP_SBV_NODE);
  assert(kind != BZLA_FP_TO_FP_UBV_NODE);

  if (!is_sorted_binary_bv_exp(bzla, kind, e)
      || (kind == BZLA_FP_EQ_NODE && e[0]->id > e[1]->id)
      || (kind == BZLA_RM_EQ_NODE && e[0]->id > e[1]->id))
  {
    BZLA_SWAP(BzlaNode *, e[0], e[1]);
  }
  if (!is_sorted_binary_fp_exp(bzla, kind, e))
  {
    BZLA_SWAP(BzlaNode *, e[1], e[2]);
  }
  else if (!is_sorted_fp_fma_exp(bzla, kind, e))
  {
    BZLA_SWAP(BzlaNode *, e[1], e[2]);
  }

  hash = hash_bv_fp_exp(bzla, kind, arity, e);
  hash &= bzla->nodes_unique_table.size - 1;

  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (cur->kind == kind && cur->arity == arity)
    {
      equal = true;
      /* special case for bv eq; (= (bvnot a) b) == (= a (bvnot b)) */
      if (kind == BZLA_BV_EQ_NODE && cur->e[0] == bzla_node_invert(e[0])
          && cur->e[1] == bzla_node_invert(e[1]))
        break;
      for (i = 0; i < arity && equal; i++)
        if (cur->e[i] != e[i]) equal = false;
      if (equal) break;
#ifndef NDEBUG
      if (bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP) > 0
          && bzla_node_is_binary_commutative_bv_kind(kind))
        assert(arity == 2),
            assert(e[0] == e[1] || bzla_node_invert(e[0]) == e[1]
                   || !(cur->e[0] == e[1] && cur->e[1] == e[0]));
#endif
    }
    result = &(cur->next);
    cur    = *result;
  }
  return result;
}

static int32_t compare_binder_exp(Bzla *bzla,
                                  BzlaNode *param,
                                  BzlaNode *body,
                                  BzlaNode *binder,
                                  BzlaPtrHashTable *map);

static BzlaNode **
find_binder_exp(Bzla *bzla,
                BzlaNodeKind kind,
                BzlaNode *param,
                BzlaNode *body,
                uint32_t *binder_hash,
                BzlaIntHashTable *params,
                BzlaPtrHashTable *map)
{
  assert(bzla);
  assert(param);
  assert(body);
  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));

  BzlaNode *cur, **result;
  uint32_t hash;

  hash = hash_binder_exp(bzla, param, body, params);

  BZLALOG(2,
          "find binder %s %s (hash: %u)",
          bzla_util_node2string(param),
          bzla_util_node2string(body),
          hash);

  if (binder_hash) *binder_hash = hash;
  hash &= bzla->nodes_unique_table.size - 1;
  result = bzla->nodes_unique_table.chains + hash;
  cur    = *result;
  while (cur)
  {
    assert(bzla_node_is_regular(cur));
    if (cur->kind == kind
        && ((!map && param == cur->e[0] && body == cur->e[1])
            || (((map || !cur->parameterized)
                 && compare_binder_exp(bzla, param, body, cur, map)))))
      break;
    else
    {
      result = &cur->next;
      cur    = *result;
    }
  }
  assert(!*result || bzla_node_is_binder(*result));
  BZLALOG(2,
          "found binder %s %s -> %s",
          bzla_util_node2string(param),
          bzla_util_node2string(body),
          bzla_util_node2string(*result));
  return result;
}

static int32_t
compare_binder_exp(Bzla *bzla,
                   BzlaNode *param,
                   BzlaNode *body,
                   BzlaNode *binder,
                   BzlaPtrHashTable *map)
{
  assert(bzla);
  assert(param);
  assert(body);
  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));
  assert(bzla_node_is_regular(binder));
  assert(bzla_node_is_binder(binder));
  assert(!binder->parameterized || map);

  int32_t i, equal = 0;
  BzlaMemMgr *mm;
  BzlaNode *cur, *real_cur, *result, *subst_param, **e, *b0, *b1;
  BzlaPtrHashTable *cache, *param_map;
  BzlaPtrHashBucket *b, *bb;
  BzlaNodePtrStack stack, args;
  BzlaNodeIterator it, iit;
  BzlaPtrHashTableIterator h_it;

  mm          = bzla->mm;
  subst_param = binder->e[0];

  if (bzla_node_get_sort_id(subst_param) != bzla_node_get_sort_id(param)
      || bzla_node_get_sort_id(body) != bzla_node_get_sort_id(binder->e[1]))
    return 0;

  cache = bzla_hashptr_table_new(mm, 0, 0);

  /* create param map */
  param_map = bzla_hashptr_table_new(mm, 0, 0);
  bzla_hashptr_table_add(param_map, param)->data.as_ptr = subst_param;

  if (map)
  {
    bzla_iter_hashptr_init(&h_it, map);
    while (bzla_iter_hashptr_has_next(&h_it))
    {
      subst_param = h_it.bucket->data.as_ptr;
      cur         = bzla_iter_hashptr_next(&h_it);
      bzla_hashptr_table_add(param_map, cur)->data.as_ptr = subst_param;
    }
  }

  if (bzla_node_is_binder(body) && bzla_node_is_binder(binder->e[1])
      && bzla_node_is_inverted(body) == bzla_node_is_inverted(binder->e[1]))
  {
    bzla_iter_binder_init(&it, bzla_node_real_addr(body));
    bzla_iter_binder_init(&iit, bzla_node_real_addr(binder->e[1]));
    while (bzla_iter_binder_has_next(&it))
    {
      if (!bzla_iter_binder_has_next(&iit)) goto NOT_EQUAL;

      b0 = bzla_iter_binder_next(&it);
      b1 = bzla_iter_binder_next(&iit);

      if (bzla_node_get_sort_id(b0) != bzla_node_get_sort_id(b1)
          || b0->kind != b1->kind)
        goto NOT_EQUAL;

      param       = b0->e[0];
      subst_param = b1->e[0];
      assert(bzla_node_is_regular(param));
      assert(bzla_node_is_regular(subst_param));
      assert(bzla_node_is_param(param));
      assert(bzla_node_is_param(subst_param));

      if (bzla_node_get_sort_id(param) != bzla_node_get_sort_id(subst_param))
        goto NOT_EQUAL;

      bzla_hashptr_table_add(param_map, param)->data.as_ptr = subst_param;
    }
    body = bzla_node_binder_get_body(bzla_node_real_addr(body));
  }
  else if (bzla_node_is_binder(body) || bzla_node_is_binder(binder->e[1]))
    goto NOT_EQUAL;

  BZLA_INIT_STACK(mm, args);
  BZLA_INIT_STACK(mm, stack);
  BZLA_PUSH_STACK(stack, body);
  while (!BZLA_EMPTY_STACK(stack))
  {
    cur      = BZLA_POP_STACK(stack);
    real_cur = bzla_node_real_addr(cur);

    if (!real_cur->parameterized)
    {
      BZLA_PUSH_STACK(args, cur);
      continue;
    }

    b = bzla_hashptr_table_get(cache, real_cur);

    if (!b)
    {
      b = bzla_hashptr_table_add(cache, real_cur);

      if (bzla_node_is_binder(real_cur))
      {
        result = *find_binder_exp(bzla,
                                  real_cur->kind,
                                  real_cur->e[0],
                                  real_cur->e[1],
                                  0,
                                  0,
                                  param_map);
        if (result)
        {
          b->data.as_ptr = result;
          BZLA_PUSH_STACK(args, bzla_node_cond_invert(cur, result));
          continue;
        }
        else
        {
          BZLA_RESET_STACK(args);
          break;
        }
      }

      BZLA_PUSH_STACK(stack, cur);
      for (i = real_cur->arity - 1; i >= 0; i--)
        BZLA_PUSH_STACK(stack, real_cur->e[i]);
    }
    else if (!b->data.as_ptr)
    {
      assert(!bzla_node_is_binder(real_cur));
      assert(BZLA_COUNT_STACK(args) >= real_cur->arity);
      args.top -= real_cur->arity;
      e = args.top;

      if (bzla_node_is_bv_slice(real_cur))
      {
        result = *find_slice_exp(bzla,
                                 e[0],
                                 bzla_node_bv_slice_get_upper(real_cur),
                                 bzla_node_bv_slice_get_lower(real_cur));
      }
      else if (bzla_node_is_fp_to_sbv(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_SBV_NODE,
                                         e[0],
                                         e[1],
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_ubv(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_UBV_NODE,
                                         e[0],
                                         e[1],
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_bv(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_FP_BV_NODE,
                                         e[0],
                                         0,
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_fp(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_FP_FP_NODE,
                                         e[0],
                                         e[1],
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_sbv(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_FP_SBV_NODE,
                                         e[0],
                                         e[1],
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_fp_to_fp_from_ubv(real_cur))
      {
        result = *find_fp_conversion_exp(bzla,
                                         BZLA_FP_TO_FP_UBV_NODE,
                                         e[0],
                                         e[1],
                                         bzla_node_get_sort_id(real_cur));
      }
      else if (bzla_node_is_param(real_cur))
      {
        if ((bb = bzla_hashptr_table_get(param_map, real_cur)))
          result = bb->data.as_ptr;
        else
          result = real_cur;
      }
      else
      {
        assert(!bzla_node_is_binder(real_cur));
        result = *find_bv_fp_exp(bzla, real_cur->kind, e, real_cur->arity);
      }

      if (!result)
      {
        BZLA_RESET_STACK(args);
        break;
      }

      BZLA_PUSH_STACK(args, bzla_node_cond_invert(cur, result));
      b->data.as_ptr = result;
    }
    else
    {
      assert(b->data.as_ptr);
      BZLA_PUSH_STACK(args, bzla_node_cond_invert(cur, b->data.as_ptr));
    }
  }
  assert(BZLA_COUNT_STACK(args) <= 1);

  if (!BZLA_EMPTY_STACK(args))
    equal = BZLA_TOP_STACK(args) == bzla_node_binder_get_body(binder);

  BZLA_RELEASE_STACK(stack);
  BZLA_RELEASE_STACK(args);
NOT_EQUAL:
  bzla_hashptr_table_delete(cache);
  bzla_hashptr_table_delete(param_map);
  return equal;
}

static BzlaNode **
find_exp(Bzla *bzla,
         BzlaNodeKind kind,
         BzlaNode *e[],
         uint32_t arity,
         uint32_t *binder_hash,
         BzlaIntHashTable *params)
{
  assert(bzla);
  assert(arity > 0);
  assert(e);

#ifndef NDEBUG
  uint32_t i;
  for (i = 0; i < arity; i++) assert(e[i]);
#endif

  if (kind == BZLA_LAMBDA_NODE || kind == BZLA_FORALL_NODE
      || kind == BZLA_EXISTS_NODE)
    return find_binder_exp(bzla, kind, e[0], e[1], binder_hash, params, 0);
  else if (binder_hash)
    *binder_hash = 0;

  return find_bv_fp_exp(bzla, kind, e, arity);
}

/*------------------------------------------------------------------------*/

static BzlaNode *
new_bv_const_exp_node(Bzla *bzla, BzlaBitVector *bits)
{
  assert(bzla);
  assert(bits);

  BzlaBVConstNode *exp;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_BV_CONST_NODE);
  exp->bytes = sizeof *exp;
  bzla_node_set_sort_id((BzlaNode *) exp,
                        bzla_sort_bv(bzla, bzla_bv_get_width(bits)));
  setup_node_and_add_to_id_table(bzla, exp);
  bzla_node_bv_const_set_bits((BzlaNode *) exp, bzla_bv_copy(bzla->mm, bits));
  bzla_node_bv_const_set_invbits((BzlaNode *) exp, bzla_bv_not(bzla->mm, bits));
  return (BzlaNode *) exp;
}

static BzlaNode *
new_rm_const_exp_node(Bzla *bzla, const BzlaRoundingMode rm)
{
  assert(bzla);
  assert(bzla_rm_is_valid(rm));

  BzlaRMConstNode *exp;
  BzlaSortId sort;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_RM_CONST_NODE);
  exp->bytes = sizeof *exp;
  sort       = bzla_sort_rm(bzla);
  bzla_node_set_sort_id((BzlaNode *) exp, sort);
  setup_node_and_add_to_id_table(bzla, exp);
  exp->rm = rm;
  return (BzlaNode *) exp;
}

static BzlaNode *
new_fp_const_exp_node(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFPConstNode *exp;
  BzlaSortId sort;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_FP_CONST_NODE);
  exp->bytes = sizeof *exp;
  sort =
      bzla_sort_fp(bzla, bzla_fp_get_exp_width(fp), bzla_fp_get_sig_width(fp));
  bzla_node_set_sort_id((BzlaNode *) exp, sort);
  setup_node_and_add_to_id_table(bzla, exp);
  bzla_node_fp_const_set_fp((BzlaNode *) exp, bzla_fp_copy(bzla, fp));
  return (BzlaNode *) exp;
}

static BzlaNode *
new_unary_to_fp_exp_node(Bzla *bzla, BzlaNode *e0, BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(bzla_node_is_bv(bzla, e0));
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla == bzla_node_real_addr(e0)->bzla);

  BzlaNode *exp = 0;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_FP_TO_FP_BV_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  bzla_node_set_sort_id(exp, bzla_sort_copy(bzla, sort));
  setup_node_and_add_to_id_table(bzla, exp);
  connect_child_exp(bzla, exp, e0, 0);
  return exp;
}

static BzlaNode *
new_binary_fp_conversion_node(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  assert(bzla);
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || kind == BZLA_FP_TO_FP_FP_NODE || kind == BZLA_FP_TO_FP_SBV_NODE
         || kind == BZLA_FP_TO_FP_UBV_NODE);
  assert(e0);
  assert(e1);
  assert(bzla_node_is_rm(bzla, e0));
  assert(bzla_node_is_bv(bzla, e1) || bzla_node_is_fp(bzla, e1));
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || bzla_sort_is_fp(bzla, sort));
  assert((kind != BZLA_FP_TO_SBV_NODE && kind != BZLA_FP_TO_UBV_NODE)
         || bzla_sort_is_bv(bzla, sort));
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *exp = 0;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, kind);
  exp->bytes = sizeof *exp;
  exp->arity = 2;
  bzla_node_set_sort_id(exp, bzla_sort_copy(bzla, sort));
  setup_node_and_add_to_id_table(bzla, exp);
  connect_child_exp(bzla, exp, e0, 0);
  connect_child_exp(bzla, exp, e1, 1);
  return exp;
}

static BzlaNode *
new_slice_exp_node(Bzla *bzla, BzlaNode *e0, uint32_t upper, uint32_t lower)
{
  assert(bzla);
  assert(e0);
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(upper < bzla_node_bv_get_width(bzla, e0));
  assert(upper >= lower);

  BzlaBVSliceNode *exp = 0;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_BV_SLICE_NODE);
  exp->bytes = sizeof *exp;
  exp->arity = 1;
  exp->upper = upper;
  exp->lower = lower;
  bzla_node_set_sort_id((BzlaNode *) exp,
                        bzla_sort_bv(bzla, upper - lower + 1));
  setup_node_and_add_to_id_table(bzla, exp);
  connect_child_exp(bzla, (BzlaNode *) exp, e0, 0);
  return (BzlaNode *) exp;
}

static BzlaNode *
new_lambda_exp_node(Bzla *bzla, BzlaNode *e_param, BzlaNode *e_exp)
{
  assert(bzla);
  assert(e_param);
  assert(bzla_node_is_regular(e_param));
  assert(bzla_node_is_param(e_param));
  assert(!bzla_node_param_is_bound(e_param));
  assert(e_exp);
  assert(bzla == e_param->bzla);
  assert(bzla == bzla_node_real_addr(e_exp)->bzla);

  BzlaSortId s, domain, codomain;
  BzlaSortIdStack param_sorts;
  BzlaLambdaNode *lambda_exp;
  BzlaTupleSortIterator it;
  BzlaPtrHashBucket *b;
  BzlaIntHashTable *params;

  BZLA_INIT_STACK(bzla->mm, param_sorts);

  BZLA_CNEW(bzla->mm, lambda_exp);
  set_kind(bzla, (BzlaNode *) lambda_exp, BZLA_LAMBDA_NODE);
  lambda_exp->bytes        = sizeof *lambda_exp;
  lambda_exp->arity        = 2;
  lambda_exp->lambda_below = 1;
  setup_node_and_add_to_id_table(bzla, (BzlaNode *) lambda_exp);
  connect_child_exp(bzla, (BzlaNode *) lambda_exp, e_param, 0);
  connect_child_exp(bzla, (BzlaNode *) lambda_exp, e_exp, 1);

  BZLA_PUSH_STACK(param_sorts, bzla_node_get_sort_id(e_param));
  /* curried lambdas (functions) */
  if (bzla_node_is_lambda(e_exp))
  {
    bzla_node_binder_set_body(
        (BzlaNode *) lambda_exp,
        bzla_simplify_exp(bzla, bzla_node_binder_get_body(e_exp)));
    bzla_iter_tuple_sort_init(
        &it,
        bzla,
        bzla_sort_fun_get_domain(bzla, bzla_node_get_sort_id(e_exp)));
    while (bzla_iter_tuple_sort_has_next(&it))
    {
      s = bzla_iter_tuple_sort_next(&it);
      BZLA_PUSH_STACK(param_sorts, s);
    }

    if ((b = bzla_hashptr_table_get(bzla->parameterized, e_exp)))
    {
      params = b->data.as_ptr;
      bzla_hashint_table_remove(params, e_param->id);
      bzla_hashptr_table_remove(bzla->parameterized, e_exp, 0, 0);
      if (params->count > 0)
      {
        bzla_hashptr_table_add(bzla->parameterized, lambda_exp)->data.as_ptr =
            params;
        lambda_exp->parameterized = 1;
      }
      else
        bzla_hashint_table_delete(params);
    }
  }
  else
    bzla_node_binder_set_body((BzlaNode *) lambda_exp, e_exp);

  domain =
      bzla_sort_tuple(bzla, param_sorts.start, BZLA_COUNT_STACK(param_sorts));
  codomain = bzla_node_get_sort_id(lambda_exp->body);
  bzla_node_set_sort_id((BzlaNode *) lambda_exp,
                        bzla_sort_fun(bzla, domain, codomain));

  bzla_sort_release(bzla, domain);
  BZLA_RELEASE_STACK(param_sorts);

  assert(!bzla_node_real_addr(lambda_exp->body)->simplified);
  assert(!bzla_node_is_lambda(lambda_exp->body));
  assert(!bzla_hashptr_table_get(bzla->lambdas, lambda_exp));
  (void) bzla_hashptr_table_add(bzla->lambdas, lambda_exp);
  /* set lambda expression of parameter */
  bzla_node_param_set_binder(e_param, (BzlaNode *) lambda_exp);
  return (BzlaNode *) lambda_exp;
}

static BzlaNode *
new_quantifier_exp_node(Bzla *bzla,
                        BzlaNodeKind kind,
                        BzlaNode *param,
                        BzlaNode *body)
{
  assert(bzla);
  assert(param);
  assert(body);
  assert(kind == BZLA_FORALL_NODE || kind == BZLA_EXISTS_NODE);
  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));
  assert(!bzla_node_param_is_bound(param));
  assert(bzla_sort_is_bool(bzla, bzla_node_real_addr(body)->sort_id));
  assert(bzla == param->bzla);
  assert(bzla == bzla_node_real_addr(body)->bzla);

  BzlaBinderNode *res;

  BZLA_CNEW(bzla->mm, res);
  set_kind(bzla, (BzlaNode *) res, kind);
  res->bytes            = sizeof *res;
  res->arity            = 2;
  res->quantifier_below = 1;
  res->sort_id = bzla_sort_copy(bzla, bzla_node_real_addr(body)->sort_id);
  setup_node_and_add_to_id_table(bzla, (BzlaNode *) res);
  connect_child_exp(bzla, (BzlaNode *) res, param, 0);
  connect_child_exp(bzla, (BzlaNode *) res, body, 1);

  /* curried (non-inverted) quantifiers */
  if (!bzla_node_is_inverted(body) && bzla_node_is_quantifier(body))
    res->body = bzla_simplify_exp(bzla, bzla_node_binder_get_body(body));
  else
    res->body = body;

#if 0
  /* check if 'res' is parameterized, i.e. if it contains params that are not
   * bound by 'res' */
  remove_param_parameterized (bzla, (BzlaNode *) res, param);
  if (is_parameterized (bzla, (BzlaNode *) res))
    res->parameterized = 1;
#endif

  assert(!bzla_node_real_addr(res->body)->simplified);
  assert(!bzla_node_is_lambda(res->body));
  bzla_node_param_set_binder(param, (BzlaNode *) res);
  assert(!bzla_hashptr_table_get(bzla->quantifiers, res));
  (void) bzla_hashptr_table_add(bzla->quantifiers, res);
  return (BzlaNode *) res;
}

static BzlaNode *
new_args_exp_node(Bzla *bzla, uint32_t arity, BzlaNode *e[])
{
  assert(bzla);
  assert(arity > 0);
  assert(arity <= BZLA_NODE_MAX_CHILDREN);
  assert(e);

  uint32_t i;
  BzlaArgsNode *exp;
  BzlaSortIdStack sorts;
  BzlaTupleSortIterator it;
#ifndef NDEBUG
  for (i = 0; i < arity; i++) assert(e[i]);
#endif

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_ARGS_NODE);
  exp->bytes = sizeof(*exp);
  exp->arity = arity;
  setup_node_and_add_to_id_table(bzla, exp);

  for (i = 0; i < arity; i++)
    connect_child_exp(bzla, (BzlaNode *) exp, e[i], i);

  /* create tuple sort for argument node */
  BZLA_INIT_STACK(bzla->mm, sorts);
  for (i = 0; i < arity; i++)
  {
    if (bzla_node_is_args(e[i]))
    {
      assert(i == 2);
      assert(bzla_node_is_regular(e[i]));
      bzla_iter_tuple_sort_init(&it, bzla, bzla_node_get_sort_id(e[i]));
      while (bzla_iter_tuple_sort_has_next(&it))
        BZLA_PUSH_STACK(sorts, bzla_iter_tuple_sort_next(&it));
    }
    else
      BZLA_PUSH_STACK(sorts, bzla_node_get_sort_id(e[i]));
  }
  bzla_node_set_sort_id(
      (BzlaNode *) exp,
      bzla_sort_tuple(bzla, sorts.start, BZLA_COUNT_STACK(sorts)));
  BZLA_RELEASE_STACK(sorts);
  return (BzlaNode *) exp;
}

static BzlaNode *
new_node(Bzla *bzla, BzlaNodeKind kind, uint32_t arity, BzlaNode *e[])
{
  assert(bzla);
  assert(arity > 0);
  assert(arity <= BZLA_NODE_MAX_CHILDREN);
  assert(e);

#ifndef NDEBUG
  if (bzla_opt_get(bzla, BZLA_OPT_RW_SORT_EXP) > 0
      && bzla_node_is_binary_commutative_bv_kind(kind))
    assert(arity == 2),
        assert(bzla_node_real_addr(e[0])->id <= bzla_node_real_addr(e[1])->id);
#endif

  uint32_t i;
  BzlaNode *exp;
  BzlaSortId sort;

#ifdef NDEBUG
  for (i = 0; i < arity; i++)
  {
    assert(e[i]);
    assert(bzla == bzla_node_real_addr(e[i])->bzla);
  }
#endif

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, exp, kind);
  exp->arity = arity;
  assert(exp->arity > 0);
  assert(exp->arity <= BZLA_NODE_MAX_CHILDREN);
  assert(sizeof(*exp) <= UINT8_MAX);
  exp->bytes = sizeof(*exp);
  setup_node_and_add_to_id_table(bzla, exp);

  switch (kind)
  {
    case BZLA_COND_NODE:
      sort = bzla_sort_copy(bzla, bzla_node_get_sort_id(e[1]));
      break;

    case BZLA_BV_CONCAT_NODE:
      sort = bzla_sort_bv(bzla,
                          bzla_node_bv_get_width(bzla, e[0])
                              + bzla_node_bv_get_width(bzla, e[1]));
      break;

    case BZLA_BV_ULT_NODE:
    case BZLA_BV_SLT_NODE:
    case BZLA_BV_EQ_NODE:
    case BZLA_FP_EQ_NODE:
    case BZLA_FP_IS_NORM_NODE:
    case BZLA_FP_IS_SUBNORM_NODE:
    case BZLA_FP_IS_ZERO_NODE:
    case BZLA_FP_IS_INF_NODE:
    case BZLA_FP_IS_NAN_NODE:
    case BZLA_FP_IS_NEG_NODE:
    case BZLA_FP_IS_POS_NODE:
    case BZLA_FP_LTE_NODE:
    case BZLA_FP_LT_NODE:
    case BZLA_FUN_EQ_NODE:
    case BZLA_RM_EQ_NODE: sort = bzla_sort_bool(bzla); break;

    case BZLA_APPLY_NODE:
      sort = bzla_sort_copy(
          bzla, bzla_sort_fun_get_codomain(bzla, bzla_node_get_sort_id(e[0])));
      break;

    case BZLA_FP_SQRT_NODE:
    case BZLA_FP_RTI_NODE:
    case BZLA_FP_ADD_NODE:
    case BZLA_FP_MUL_NODE:
    case BZLA_FP_DIV_NODE:
    case BZLA_FP_FMA_NODE:
      sort = bzla_sort_copy(bzla, bzla_node_get_sort_id(e[1]));
      break;

    default:
      assert(kind == BZLA_BV_AND_NODE || kind == BZLA_BV_ADD_NODE
             || kind == BZLA_BV_MUL_NODE || kind == BZLA_BV_SLL_NODE
             || kind == BZLA_BV_SRL_NODE || kind == BZLA_BV_UDIV_NODE
             || kind == BZLA_BV_UREM_NODE || kind == BZLA_FP_ABS_NODE
             || kind == BZLA_FP_NEG_NODE || kind == BZLA_FP_MIN_NODE
             || kind == BZLA_FP_MAX_NODE || kind == BZLA_FP_REM_NODE
             || kind == BZLA_UPDATE_NODE);

      sort = bzla_sort_copy(bzla, bzla_node_get_sort_id(e[0]));
  }

  bzla_node_set_sort_id((BzlaNode *) exp, sort);

  for (i = 0; i < arity; i++)
    connect_child_exp(bzla, (BzlaNode *) exp, e[i], i);

  if (kind == BZLA_FUN_EQ_NODE && !exp->parameterized)
  {
    assert(!bzla_hashptr_table_get(bzla->feqs, exp));
    bzla_hashptr_table_add(bzla->feqs, exp)->data.as_int = 0;
  }

  return (BzlaNode *) exp;
}

/*------------------------------------------------------------------------*/

static BzlaNode *
create_exp(Bzla *bzla, BzlaNodeKind kind, uint32_t arity, BzlaNode *e[])
{
  assert(bzla);
  assert(kind);
  assert(arity > 0);
  assert(arity <= BZLA_NODE_MAX_CHILDREN);
  assert(e);

  uint32_t i;
  uint32_t binder_hash;
  BzlaNode **lookup, *simp_e[BZLA_NODE_MAX_CHILDREN], *simp;
  BzlaIntHashTable *params = 0;

  for (i = 0; i < arity; i++)
  {
    assert(bzla_node_real_addr(e[i])->bzla == bzla);
    simp_e[i] = bzla_simplify_exp(bzla, e[i]);
  }

  /* collect params only for quantifier/function bodies */
  if ((kind == BZLA_LAMBDA_NODE && !bzla_node_is_lambda(e[1]))
      || kind == BZLA_FORALL_NODE || kind == BZLA_EXISTS_NODE)
    params = bzla_hashint_table_new(bzla->mm);

  lookup = find_exp(bzla, kind, simp_e, arity, &binder_hash, params);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_exp(bzla, kind, simp_e, arity, &binder_hash, 0);
    }

    switch (kind)
    {
      case BZLA_LAMBDA_NODE:
        assert(arity == 2);
        *lookup = new_lambda_exp_node(bzla, simp_e[0], simp_e[1]);
        bzla_hashptr_table_get(bzla->lambdas, *lookup)->data.as_int =
            binder_hash;
        BZLALOG(2,
                "new lambda: %s (hash: %u, param: %u)",
                bzla_util_node2string(*lookup),
                binder_hash,
                (*lookup)->parameterized);
        break;
      case BZLA_FORALL_NODE:
      case BZLA_EXISTS_NODE:
        assert(arity == 2);
        *lookup = new_quantifier_exp_node(bzla, kind, e[0], e[1]);
        bzla_hashptr_table_get(bzla->quantifiers, *lookup)->data.as_int =
            binder_hash;
        break;
      case BZLA_ARGS_NODE:
        *lookup = new_args_exp_node(bzla, arity, simp_e);
        break;
      default: *lookup = new_node(bzla, kind, arity, simp_e);
    }

    if (params)
    {
      assert(bzla_node_is_binder(*lookup));
      if (params->count > 0)
      {
        bzla_hashptr_table_add(bzla->parameterized, *lookup)->data.as_ptr =
            params;
        (*lookup)->parameterized = 1;
      }
      else
        bzla_hashint_table_delete(params);
    }

    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
    if (params) bzla_hashint_table_delete(params);
  }
  assert(bzla_node_is_regular(*lookup));
  if (bzla_node_is_simplified(*lookup))
  {
    assert(bzla_opt_get(bzla, BZLA_OPT_PP_NONDESTR_SUBST));
    simp = bzla_node_copy(bzla, bzla_node_get_simplified(bzla, *lookup));
    bzla_node_release(bzla, *lookup);
    return simp;
  }
  return *lookup;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_create_bv_const(Bzla *bzla, const BzlaBitVector *bits)
{
  assert(bzla);
  assert(bits);

  bool inv;
  BzlaBitVector *lookupbits;
  BzlaNode **lookup;

  /* normalize constants, constants are always even */
  if (bzla_bv_get_bit(bits, 0))
  {
    lookupbits = bzla_bv_not(bzla->mm, bits);
    inv        = true;
  }
  else
  {
    lookupbits = bzla_bv_copy(bzla->mm, bits);
    inv        = false;
  }

  lookup = find_bv_const_exp(bzla, lookupbits);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_bv_const_exp(bzla, lookupbits);
    }
    *lookup = new_bv_const_exp_node(bzla, lookupbits);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements += 1;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }

  assert(bzla_node_is_regular(*lookup));

  bzla_bv_free(bzla->mm, lookupbits);

  if (inv) return bzla_node_invert(*lookup);
  return *lookup;
}

BzlaNode *
bzla_node_create_rm_const(Bzla *bzla, const BzlaRoundingMode rm)
{
  assert(bzla);
  assert(bzla_rm_is_valid(rm));

  BzlaNode **lookup;

  lookup = find_rm_const_exp(bzla, rm);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_rm_const_exp(bzla, rm);
    }
    *lookup = new_rm_const_exp_node(bzla, rm);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements += 1;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }
  assert(bzla_node_is_regular(*lookup));
  return *lookup;
}

BzlaNode *
bzla_node_create_fp_const(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaNode **lookup;

  lookup = find_fp_const_exp(bzla, fp);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_fp_const_exp(bzla, fp);
    }
    *lookup = new_fp_const_exp_node(bzla, fp);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements += 1;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }
  assert(bzla_node_is_regular(*lookup));
  return *lookup;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_create_var(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort) || bzla_sort_is_rm(bzla, sort)
         || bzla_sort_is_fp(bzla, sort));

  BzlaBVVarNode *exp;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_VAR_NODE);
  exp->bytes = sizeof *exp;
  setup_node_and_add_to_id_table(bzla, exp);
  bzla_node_set_sort_id((BzlaNode *) exp, bzla_sort_copy(bzla, sort));
  (void) bzla_hashptr_table_add(bzla->bv_vars, exp);
  if (symbol) bzla_node_set_symbol(bzla, (BzlaNode *) exp, symbol);
  return (BzlaNode *) exp;
}

BzlaNode *
bzla_node_create_uf(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  assert(bzla);
  assert(sort);

  BzlaUFNode *exp;

  assert(bzla_sort_is_fun(bzla, sort));
  assert(!bzla_sort_is_array(bzla, bzla_sort_fun_get_codomain(bzla, sort))
         && !bzla_sort_is_fun(bzla, bzla_sort_fun_get_codomain(bzla, sort)));

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_UF_NODE);
  exp->bytes = sizeof(*exp);
  bzla_node_set_sort_id((BzlaNode *) exp, bzla_sort_copy(bzla, sort));
  setup_node_and_add_to_id_table(bzla, exp);
  (void) bzla_hashptr_table_add(bzla->ufs, exp);
  if (symbol) bzla_node_set_symbol(bzla, (BzlaNode *) exp, symbol);
  return (BzlaNode *) exp;
}

BzlaNode *
bzla_node_create_param(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort) || bzla_sort_is_rm(bzla, sort)
         || bzla_sort_is_fp(bzla, sort));

  BzlaParamNode *exp;

  BZLA_CNEW(bzla->mm, exp);
  set_kind(bzla, (BzlaNode *) exp, BZLA_PARAM_NODE);
  exp->bytes         = sizeof *exp;
  exp->parameterized = 1;
  bzla_node_set_sort_id((BzlaNode *) exp, bzla_sort_copy(bzla, sort));
  setup_node_and_add_to_id_table(bzla, exp);
  if (symbol) bzla_node_set_symbol(bzla, (BzlaNode *) exp, symbol);
  return (BzlaNode *) exp;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_create_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  BzlaNodeKind kind;
  BzlaSortId sort;

  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_eq_exp(bzla, e[0], e[1]));
  if (bzla_node_is_fun(e[0]))
  {
    kind = BZLA_FUN_EQ_NODE;
  }
  else
  {
    sort = bzla_node_get_sort_id(e0);
    if (bzla_sort_is_bv(bzla, sort))
    {
      kind = BZLA_BV_EQ_NODE;
    }
    else if (bzla_sort_is_rm(bzla, sort))
    {
      kind = BZLA_RM_EQ_NODE;
    }
    else
    {
      assert(bzla_sort_is_fp(bzla, sort));
      kind = BZLA_FP_EQ_NODE;
    }
  }
  return create_exp(bzla, kind, 2, e);
}

BzlaNode *
bzla_node_create_cond(Bzla *bzla,
                      BzlaNode *e_cond,
                      BzlaNode *e_if,
                      BzlaNode *e_else)
{
  uint32_t i, arity;
  BzlaNode *e[3], *cond, *lambda;
  BzlaNodePtrStack params;
  BzlaSort *sort;
  e[0] = bzla_simplify_exp(bzla, e_cond);
  e[1] = bzla_simplify_exp(bzla, e_if);
  e[2] = bzla_simplify_exp(bzla, e_else);
  assert(bzla_dbg_precond_cond_exp(bzla, e[0], e[1], e[2]));

  /* represent parameterized function conditionals (with parameterized
   * functions) as parameterized function
   * -> gets beta reduced in bzla_node_create_apply */
  if (bzla_node_is_fun(e[1]) && (e[1]->parameterized || e[2]->parameterized))
  {
    BZLA_INIT_STACK(bzla->mm, params);
    assert(bzla_sort_is_fun(bzla, bzla_node_get_sort_id(e[1])));
    arity = bzla_node_fun_get_arity(bzla, e[1]);
    sort  = bzla_sort_get_by_id(bzla, bzla_node_get_sort_id(e[1]));
    assert(sort->fun.domain->kind == BZLA_TUPLE_SORT);
    assert(sort->fun.domain->tuple.num_elements == arity);
    for (i = 0; i < arity; i++)
      BZLA_PUSH_STACK(
          params,
          bzla_exp_param(bzla, sort->fun.domain->tuple.elements[i]->id, 0));
    e[1]   = bzla_exp_apply_n(bzla, e[1], params.start, arity);
    e[2]   = bzla_exp_apply_n(bzla, e[2], params.start, arity);
    cond   = create_exp(bzla, BZLA_COND_NODE, 3, e);
    lambda = bzla_exp_fun(bzla, params.start, arity, cond);
    while (!BZLA_EMPTY_STACK(params))
      bzla_node_release(bzla, BZLA_POP_STACK(params));
    bzla_node_release(bzla, e[1]);
    bzla_node_release(bzla, e[2]);
    bzla_node_release(bzla, cond);
    BZLA_RELEASE_STACK(params);
    return lambda;
  }
  return create_exp(bzla, BZLA_COND_NODE, 3, e);
}

/* more than 4 children are not possible as we only have 2 bit for storing
 * the position in the parent pointers */
#define ARGS_MAX_NUM_CHILDREN 3

BzlaNode *
bzla_node_create_args(Bzla *bzla, BzlaNode *args[], uint32_t argc)
{
  assert(bzla);
  assert(argc > 0);
  assert(args);

  int64_t i, cur_argc, cnt_args, rem_free, num_args;
  BzlaNode *e[ARGS_MAX_NUM_CHILDREN];
  BzlaNode *result = 0, *last = 0;

  /* arguments fit in one args node */
  if (argc <= ARGS_MAX_NUM_CHILDREN)
  {
    num_args = 1;
    rem_free = ARGS_MAX_NUM_CHILDREN - argc;
    cur_argc = argc;
  }
  /* arguments have to be split into several args nodes.
   * compute number of required args nodes */
  else
  {
    rem_free = argc % (ARGS_MAX_NUM_CHILDREN - 1);
    num_args = argc / (ARGS_MAX_NUM_CHILDREN - 1);
    /* we can store at most 1 more element into 'num_args' nodes
     * without needing an additional args node */
    if (rem_free > 1) num_args += 1;

    assert(num_args > 1);
    /* compute number of arguments in last args node */
    cur_argc = argc - (num_args - 1) * (ARGS_MAX_NUM_CHILDREN - 1);
  }
  cnt_args = cur_argc - 1;

  /* split up args in 'num_args' of args nodes */
  for (i = argc - 1; i >= 0; i--)
  {
    assert(cnt_args >= 0);
    assert(cnt_args <= ARGS_MAX_NUM_CHILDREN);
    assert(!bzla_node_is_fun(args[i]));
    assert(bzla == bzla_node_real_addr(args[i])->bzla);
    e[cnt_args] = bzla_simplify_exp(bzla, args[i]);
    cnt_args -= 1;

    assert(i > 0 || cnt_args < 0);
    if (cnt_args < 0)
    {
      result = create_exp(bzla, BZLA_ARGS_NODE, cur_argc, e);

      /* init for next iteration */
      cur_argc    = ARGS_MAX_NUM_CHILDREN;
      cnt_args    = cur_argc - 1;
      e[cnt_args] = result;
      cnt_args -= 1;

      if (last) bzla_node_release(bzla, last);

      last = result;
    }
  }

  assert(result);
  return result;
}

BzlaNode *
bzla_node_create_apply(Bzla *bzla, BzlaNode *fun, BzlaNode *args)
{
  assert(bzla);
  assert(fun);
  assert(args);
  assert(bzla == bzla_node_real_addr(fun)->bzla);
  assert(bzla == bzla_node_real_addr(args)->bzla);
  assert(bzla_dbg_precond_apply_exp(bzla, fun, args));

  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, fun);
  e[1] = bzla_simplify_exp(bzla, args);

  assert(bzla_node_is_regular(e[0]));
  assert(bzla_node_is_regular(e[1]));
  assert(bzla_node_is_fun(e[0]));
  assert(bzla_node_is_args(e[1]));

  /* eliminate nested functions */
  if (bzla_node_is_lambda(e[0]) && e[0]->parameterized)
  {
    bzla_beta_assign_args(bzla, e[0], args);
    BzlaNode *result = bzla_beta_reduce_bounded(bzla, e[0], 1);
    bzla_beta_unassign_params(bzla, e[0]);
    return result;
  }
  assert(!bzla_node_is_fun_cond(e[0])
         || (!e[0]->e[1]->parameterized && !e[0]->e[2]->parameterized));
  return create_exp(bzla, BZLA_APPLY_NODE, 2, e);
}

BzlaNode *
bzla_node_create_quantifier(Bzla *bzla,
                            BzlaNodeKind kind,
                            BzlaNode *param,
                            BzlaNode *body)
{
  assert(bzla);
  assert(kind == BZLA_FORALL_NODE || kind == BZLA_EXISTS_NODE);
  assert(param);

  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, param);
  e[1] = bzla_simplify_exp(bzla, body);

  assert(bzla_node_is_regular(e[0]));
  assert(bzla_node_is_param(e[0]));
  assert(e[1]);
  assert(bzla_sort_is_bool(bzla, bzla_node_real_addr(e[1])->sort_id));
  return create_exp(bzla, kind, 2, e);
}

BzlaNode *
bzla_node_create_lambda(Bzla *bzla, BzlaNode *e_param, BzlaNode *e_exp)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e_param);
  e[1] = bzla_simplify_exp(bzla, e_exp);
  return create_exp(bzla, BZLA_LAMBDA_NODE, 2, e);
}

BzlaNode *
bzla_node_create_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  return bzla_node_create_quantifier(bzla, BZLA_FORALL_NODE, param, body);
}

BzlaNode *
bzla_node_create_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  return bzla_node_invert(bzla_node_create_quantifier(
      bzla, BZLA_FORALL_NODE, param, bzla_node_invert(body)));
}

BzlaNode *
bzla_node_create_update(Bzla *bzla,
                        BzlaNode *fun,
                        BzlaNode *args,
                        BzlaNode *value)
{
  BzlaNode *e[3], *res;
  e[0] = bzla_simplify_exp(bzla, fun);
  e[1] = bzla_simplify_exp(bzla, args);
  e[2] = bzla_simplify_exp(bzla, value);
  assert(bzla_node_is_fun(e[0]));
  assert(bzla_node_is_args(e[1]));
  assert(!bzla_node_is_fun(e[2]));

  if (bzla_node_real_addr(e[0])->parameterized
      || bzla_node_real_addr(e[1])->parameterized
      || bzla_node_real_addr(e[2])->parameterized)
  {
    assert(bzla_node_args_get_arity(bzla, args) == 1);
    return bzla_exp_lambda_write(bzla, fun, args->e[0], value);
  }

  res = create_exp(bzla, BZLA_UPDATE_NODE, 3, e);
  if (fun->is_array) res->is_array = 1;
  return res;
}

/*------------------------------------------------------------------------*/

static BzlaNode *
unary_exp_slice_exp(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  bool inv;
  BzlaNode **lookup;

  exp = bzla_simplify_exp(bzla, exp);

  assert(!bzla_node_is_fun(exp));
  assert(upper >= lower);
  assert(upper < bzla_node_bv_get_width(bzla, exp));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0 && bzla_node_is_inverted(exp))
  {
    inv = true;
    exp = bzla_node_invert(exp);
  }
  else
    inv = false;

  lookup = find_slice_exp(bzla, exp, upper, lower);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_slice_exp(bzla, exp, upper, lower);
    }
    *lookup = new_slice_exp_node(bzla, exp, upper, lower);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }
  assert(bzla_node_is_regular(*lookup));
  if (inv) return bzla_node_invert(*lookup);
  return *lookup;
}

static BzlaNode *
unary_exp_to_fp_exp(Bzla *bzla, BzlaNode *exp, BzlaSortId sort)
{
  assert(bzla);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode **lookup;

  exp = bzla_simplify_exp(bzla, exp);

  assert(bzla_node_is_bv(bzla, exp));

  lookup = find_fp_conversion_exp(bzla, BZLA_FP_TO_FP_BV_NODE, exp, 0, sort);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup =
          find_fp_conversion_exp(bzla, BZLA_FP_TO_FP_BV_NODE, exp, 0, sort);
    }
    *lookup = new_unary_to_fp_exp_node(bzla, exp, sort);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }
  assert(bzla_node_is_regular(*lookup));
  return *lookup;
}

static BzlaNode *
binary_exp_fp_conversion_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  assert(bzla);
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || kind == BZLA_FP_TO_FP_FP_NODE || kind == BZLA_FP_TO_FP_SBV_NODE
         || kind == BZLA_FP_TO_FP_UBV_NODE);
  assert(e0);
  assert(e1);
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(kind == BZLA_FP_TO_SBV_NODE || kind == BZLA_FP_TO_UBV_NODE
         || bzla_sort_is_fp(bzla, sort));
  assert((kind != BZLA_FP_TO_SBV_NODE && kind != BZLA_FP_TO_UBV_NODE)
         || bzla_sort_is_bv(bzla, sort));

  BzlaNode **lookup;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  assert(bzla_node_is_rm(bzla, e0));
  assert(bzla_node_is_bv(bzla, e1) || bzla_node_is_fp(bzla, e1));

  lookup = find_fp_conversion_exp(bzla, kind, e0, e1, sort);
  if (!*lookup)
  {
    if (BZLA_FULL_UNIQUE_TABLE(bzla->nodes_unique_table))
    {
      enlarge_nodes_unique_table(bzla);
      lookup = find_fp_conversion_exp(bzla, kind, e0, e1, sort);
    }
    *lookup = new_binary_fp_conversion_node(bzla, kind, e0, e1, sort);
    assert(bzla->nodes_unique_table.num_elements < INT32_MAX);
    bzla->nodes_unique_table.num_elements++;
    (*lookup)->unique = 1;
  }
  else
  {
    inc_exp_ref_counter(bzla, *lookup);
  }
  assert(bzla_node_is_regular(*lookup));
  return *lookup;
}

BzlaNode *
bzla_node_create_bv_slice(Bzla *bzla,
                          BzlaNode *exp,
                          uint32_t upper,
                          uint32_t lower)
{
  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_slice_exp(bzla, exp, upper, lower));
  return unary_exp_slice_exp(bzla, exp, upper, lower);
}

BzlaNode *
bzla_node_create_bv_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_AND_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_ADD_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_MUL_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_ULT_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_SLT_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_SLL_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_SRL_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_UDIV_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_UREM_NODE, 2, e);
}

BzlaNode *
bzla_node_create_bv_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_concat_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_BV_CONCAT_NODE, 2, e);
}

#if 0
BzlaNode *
bzla_bv_cond_exp_node (Bzla * bzla, BzlaNode * e_cond, BzlaNode * e_if,
		       BzlaNode * e_else)
{
  assert (bzla == bzla_node_real_addr (e_cond)->bzla);
  assert (bzla == bzla_node_real_addr (e_if)->bzla);
  assert (bzla == bzla_node_real_addr (e_else)->bzla);

  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 0)
    return bzla_rewrite_ternary_exp (bzla, BZLA_BCOND_NODE, e_cond, e_if, e_else);

  return bzla_node_create_cond (bzla, e_cond, e_if, e_else);
}

// TODO: arbitrary conditionals on functions
BzlaNode *
bzla_array_cond_exp_node (Bzla * bzla, BzlaNode * e_cond, BzlaNode * e_if,
			  BzlaNode * e_else)
{
  assert (bzla == bzla_node_real_addr (e_cond)->bzla);
  assert (bzla == bzla_node_real_addr (e_if)->bzla);
  assert (bzla == bzla_node_real_addr (e_else)->bzla);

  BzlaNode *cond, *param, *lambda, *app_if, *app_else;

  e_cond = bzla_simplify_exp (bzla, e_cond);
  e_if = bzla_simplify_exp (bzla, e_if);
  e_else = bzla_simplify_exp (bzla, e_else);

  assert (bzla_node_is_regular (e_if));
  assert (bzla_node_is_fun (e_if));
  assert (bzla_node_is_regular (e_else));
  assert (bzla_node_is_fun (e_else));

  param = bzla_exp_param (bzla, bzla_node_get_sort_id (e_if), 0);
  app_if = bzla_exp_apply_n (bzla, e_if, &param, 1); 
  app_else = bzla_exp_apply_n (bzla, e_else, &param, 1);
  cond = bzla_bv_cond_exp_node (bzla, e_cond, app_if, app_else); 
  lambda = bzla_exp_lambda (bzla, param, cond); 
  lambda->is_array = 1;

  bzla_node_release (bzla, param);
  bzla_node_release (bzla, app_if);
  bzla_node_release (bzla, app_else);
  bzla_node_release (bzla, cond);

  return lambda;
}
#endif

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_create_fp_abs(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_ABS_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_neg(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_NEG_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_normal(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_NORM_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_subnormal(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_SUBNORM_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_zero(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_ZERO_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_inf(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_INF_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_nan(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_NAN_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_neg(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_NEG_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_is_pos(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);
  BzlaNode *e[1];
  e[0] = bzla_simplify_exp(bzla, e0);
  assert(bzla_dbg_precond_regular_unary_fp_exp(bzla, e[0]));
  return create_exp(bzla, BZLA_FP_IS_POS_NODE, 1, e);
}

BzlaNode *
bzla_node_create_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_LTE_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_LT_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_MIN_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_MAX_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_REM_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_rm_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_SQRT_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_rti(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_rm_binary_fp_exp(bzla, e[0], e[1]));
  return create_exp(bzla, BZLA_FP_RTI_NODE, 2, e);
}

BzlaNode *
bzla_node_create_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[3];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  e[2] = bzla_simplify_exp(bzla, e2);
  assert(bzla_dbg_precond_rm_ternary_fp_exp(bzla, e[0], e[1], e[2]));
  return create_exp(bzla, BZLA_FP_ADD_NODE, 3, e);
}

BzlaNode *
bzla_node_create_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  BzlaNode *e[3];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  e[2] = bzla_simplify_exp(bzla, e2);
  assert(bzla_dbg_precond_rm_ternary_fp_exp(bzla, e[0], e[1], e[2]));
  return create_exp(bzla, BZLA_FP_MUL_NODE, 3, e);
}

BzlaNode *
bzla_node_create_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  BzlaNode *e[3];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  e[2] = bzla_simplify_exp(bzla, e2);
  assert(bzla_dbg_precond_rm_ternary_fp_exp(bzla, e[0], e[1], e[2]));
  return create_exp(bzla, BZLA_FP_DIV_NODE, 3, e);
}

BzlaNode *
bzla_node_create_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  assert(e3);
  BzlaNode *e[4];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  e[2] = bzla_simplify_exp(bzla, e2);
  e[3] = bzla_simplify_exp(bzla, e3);
  assert(bzla_dbg_precond_rm_quaternary_fp_exp(bzla, e[0], e[1], e[2], e[3]));
  BzlaNode *res = create_exp(bzla, BZLA_FP_FMA_NODE, 4, e);
  assert(bzla_node_real_addr(res)->arity == 4);
  return res;
}

BzlaNode *
bzla_node_create_fp_to_sbv(Bzla *bzla,
                           BzlaNode *e0,
                           BzlaNode *e1,
                           BzlaSortId sort)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_binary_fp_conversion_exp(bzla, e[0], e[1], sort));
  return binary_exp_fp_conversion_exp(
      bzla, BZLA_FP_TO_SBV_NODE, e[0], e[1], sort);
}

BzlaNode *
bzla_node_create_fp_to_ubv(Bzla *bzla,
                           BzlaNode *e0,
                           BzlaNode *e1,
                           BzlaSortId sort)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_binary_fp_conversion_exp(bzla, e[0], e[1], sort));
  return binary_exp_fp_conversion_exp(
      bzla, BZLA_FP_TO_UBV_NODE, e[0], e[1], sort);
}

BzlaNode *
bzla_node_create_fp_to_fp_from_bv(Bzla *bzla, BzlaNode *exp, BzlaSortId sort)
{
  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_unary_fp_to_fp_exp(bzla, exp, sort));
  return unary_exp_to_fp_exp(bzla, exp, sort);
}

BzlaNode *
bzla_node_create_fp_to_fp_from_fp(Bzla *bzla,
                                  BzlaNode *e0,
                                  BzlaNode *e1,
                                  BzlaSortId sort)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_binary_fp_conversion_exp(bzla, e[0], e[1], sort));
  return binary_exp_fp_conversion_exp(
      bzla, BZLA_FP_TO_FP_FP_NODE, e[0], e[1], sort);
}

BzlaNode *
bzla_node_create_fp_to_fp_from_sbv(Bzla *bzla,
                                   BzlaNode *e0,
                                   BzlaNode *e1,
                                   BzlaSortId sort)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_binary_fp_conversion_exp(bzla, e[0], e[1], sort));
  return binary_exp_fp_conversion_exp(
      bzla, BZLA_FP_TO_FP_SBV_NODE, e[0], e[1], sort);
}

BzlaNode *
bzla_node_create_fp_to_fp_from_ubv(Bzla *bzla,
                                   BzlaNode *e0,
                                   BzlaNode *e1,
                                   BzlaSortId sort)
{
  BzlaNode *e[2];
  e[0] = bzla_simplify_exp(bzla, e0);
  e[1] = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_binary_fp_conversion_exp(bzla, e[0], e[1], sort));
  return binary_exp_fp_conversion_exp(
      bzla, BZLA_FP_TO_FP_UBV_NODE, e[0], e[1], sort);
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_node_mk_value(Bzla *bzla, BzlaSortId sort, const BzlaBitVector *bv)
{
  BzlaNode *res = 0;

  if (bzla_sort_is_fp(bzla, sort))
  {
    BzlaFloatingPoint *fp = bzla_fp_from_bv(bzla, sort, bv);
    res                   = bzla_exp_fp_const_fp(bzla, fp);
    bzla_fp_free(bzla, fp);
  }
  else if (bzla_sort_is_rm(bzla, sort))
  {
    res = bzla_exp_rm_const(bzla, bzla_rm_from_bv(bv));
  }
  else
  {
    assert(bzla_sort_is_bv(bzla, sort));
    res = bzla_exp_bv_const(bzla, bv);
  }
  assert(res);

  return res;
}

/*========================================================================*/

BzlaNodePair *
bzla_node_pair_new(Bzla *bzla, BzlaNode *exp1, BzlaNode *exp2)
{
  assert(bzla);
  assert(exp1);
  assert(exp2);
  assert(bzla == bzla_node_real_addr(exp1)->bzla);
  assert(bzla == bzla_node_real_addr(exp2)->bzla);

  uint32_t id1, id2;
  BzlaNodePair *result;

  BZLA_NEW(bzla->mm, result);
  id1 = bzla_node_get_id(exp1);
  id2 = bzla_node_get_id(exp2);
  if (id2 < id1)
  {
    result->node1 = bzla_node_copy(bzla, exp2);
    result->node2 = bzla_node_copy(bzla, exp1);
  }
  else
  {
    result->node1 = bzla_node_copy(bzla, exp1);
    result->node2 = bzla_node_copy(bzla, exp2);
  }
  return result;
}

void
bzla_node_pair_delete(Bzla *bzla, BzlaNodePair *pair)
{
  assert(bzla);
  assert(pair);
  bzla_node_release(bzla, pair->node1);
  bzla_node_release(bzla, pair->node2);
  BZLA_DELETE(bzla->mm, pair);
}

uint32_t
bzla_node_pair_hash(const BzlaNodePair *pair)
{
  uint32_t result;
  assert(pair);
  result = (uint32_t) bzla_node_real_addr(pair->node1)->id;
  result += (uint32_t) bzla_node_real_addr(pair->node2)->id;
  result *= 7334147u;
  return result;
}

int32_t
bzla_node_pair_compare(const BzlaNodePair *pair1, const BzlaNodePair *pair2)
{
  assert(pair1);
  assert(pair2);

  int32_t result;

  result = bzla_node_get_id(pair1->node1);
  result -= bzla_node_get_id(pair2->node1);
  if (result != 0) return result;
  result = bzla_node_get_id(pair1->node2);
  result -= bzla_node_get_id(pair2->node2);
  return result;
}
