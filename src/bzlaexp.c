/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaexp.h"

#include <limits.h>

#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlafp.h"
#include "bzlarewrite.h"
#include "utils/bzlaabort.h"

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_create(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e[], uint32_t arity)
{
  assert(arity > 0);
  assert(arity <= BZLA_NODE_MAX_CHILDREN);

  switch (kind)
  {
    case BZLA_BV_AND_NODE:
      assert(arity == 2);
      return bzla_exp_bv_and(bzla, e[0], e[1]);
    case BZLA_BV_EQ_NODE:
    case BZLA_RM_EQ_NODE:
    case BZLA_FP_EQ_NODE:
    case BZLA_FUN_EQ_NODE:
      assert(arity == 2);
      return bzla_exp_eq(bzla, e[0], e[1]);
    case BZLA_BV_ADD_NODE:
      assert(arity == 2);
      return bzla_exp_bv_add(bzla, e[0], e[1]);
    case BZLA_BV_MUL_NODE:
      assert(arity == 2);
      return bzla_exp_bv_mul(bzla, e[0], e[1]);
    case BZLA_BV_ULT_NODE:
      assert(arity == 2);
      return bzla_exp_bv_ult(bzla, e[0], e[1]);
    case BZLA_BV_SLL_NODE:
      assert(arity == 2);
      return bzla_exp_bv_sll(bzla, e[0], e[1]);
    case BZLA_BV_SLT_NODE:
      assert(arity == 2);
      return bzla_exp_bv_slt(bzla, e[0], e[1]);
    case BZLA_BV_SRL_NODE:
      assert(arity == 2);
      return bzla_exp_bv_srl(bzla, e[0], e[1]);
    case BZLA_BV_UDIV_NODE:
      assert(arity == 2);
      return bzla_exp_bv_udiv(bzla, e[0], e[1]);
    case BZLA_BV_UREM_NODE:
      assert(arity == 2);
      return bzla_exp_bv_urem(bzla, e[0], e[1]);
    case BZLA_BV_CONCAT_NODE:
      assert(arity == 2);
      return bzla_exp_bv_concat(bzla, e[0], e[1]);
    case BZLA_FP_ABS_NODE:
      assert(arity == 1);
      return bzla_exp_fp_abs(bzla, e[0]);
    case BZLA_FP_NEG_NODE:
      assert(arity == 1);
      return bzla_exp_fp_neg(bzla, e[0]);
    case BZLA_FP_IS_NORM_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_normal(bzla, e[0]);
    case BZLA_FP_IS_SUBNORM_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_subnormal(bzla, e[0]);
    case BZLA_FP_IS_ZERO_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_zero(bzla, e[0]);
    case BZLA_FP_IS_INF_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_inf(bzla, e[0]);
    case BZLA_FP_IS_NAN_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_nan(bzla, e[0]);
    case BZLA_FP_IS_NEG_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_neg(bzla, e[0]);
    case BZLA_FP_IS_POS_NODE:
      assert(arity == 1);
      return bzla_exp_fp_is_pos(bzla, e[0]);
    case BZLA_FP_LTE_NODE:
      assert(arity == 2);
      return bzla_exp_fp_lte(bzla, e[0], e[1]);
    case BZLA_FP_LT_NODE:
      assert(arity == 2);
      return bzla_exp_fp_lt(bzla, e[0], e[1]);
    case BZLA_FP_MIN_NODE:
      assert(arity == 2);
      return bzla_exp_fp_min(bzla, e[0], e[1]);
    case BZLA_FP_MAX_NODE:
      assert(arity == 2);
      return bzla_exp_fp_max(bzla, e[0], e[1]);
    case BZLA_FP_REM_NODE:
      assert(arity == 2);
      return bzla_exp_fp_rem(bzla, e[0], e[1]);
    case BZLA_FP_SQRT_NODE:
      assert(arity == 2);
      return bzla_exp_fp_sqrt(bzla, e[0], e[1]);
    case BZLA_FP_RTI_NODE:
      assert(arity == 2);
      return bzla_exp_fp_rti(bzla, e[0], e[1]);
    case BZLA_FP_ADD_NODE:
      assert(arity == 3);
      return bzla_exp_fp_add(bzla, e[0], e[1], e[2]);
    case BZLA_FP_MUL_NODE:
      assert(arity == 3);
      return bzla_exp_fp_mul(bzla, e[0], e[1], e[2]);
    case BZLA_FP_DIV_NODE:
      assert(arity == 3);
      return bzla_exp_fp_div(bzla, e[0], e[1], e[2]);
    case BZLA_FP_FMA_NODE:
      assert(arity == 4);
      return bzla_exp_fp_fma(bzla, e[0], e[1], e[2], e[3]);
    case BZLA_APPLY_NODE:
      assert(arity == 2);
      return bzla_exp_apply(bzla, e[0], e[1]);
    case BZLA_LAMBDA_NODE:
      assert(arity == 2);
      return bzla_exp_lambda(bzla, e[0], e[1]);
    case BZLA_EXISTS_NODE:
      assert(arity == 2);
      return bzla_exp_exists(bzla, e[0], e[1]);
    case BZLA_FORALL_NODE:
      assert(arity == 2);
      return bzla_exp_forall(bzla, e[0], e[1]);
    case BZLA_COND_NODE:
      assert(arity == 3);
      return bzla_exp_cond(bzla, e[0], e[1], e[2]);
    case BZLA_UPDATE_NODE:
      assert(arity == 3);
      return bzla_exp_update(bzla, e[0], e[1], e[2]);
    default:
      assert(kind == BZLA_ARGS_NODE);
      return bzla_exp_args(bzla, e, arity);
  }
  return 0;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_var(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  return bzla_node_create_var(bzla, sort, symbol);
}

BzlaNode *
bzla_exp_param(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  return bzla_node_create_param(bzla, sort, symbol);
}

BzlaNode *
bzla_exp_array(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fun(bzla, sort));  // TODO: maybe check is_array
  assert(bzla_sort_tuple_get_arity(bzla, bzla_sort_fun_get_domain(bzla, sort))
         == 1);

  BzlaNode *exp;

  BzlaSort *asort = bzla_sort_get_by_id(bzla, sort);
  BzlaSortId fsort =
      bzla_sort_fun(bzla, asort->fun.domain->id, asort->fun.codomain->id);
  exp           = bzla_exp_uf(bzla, fsort, symbol);
  exp->is_array = 1;
  bzla_sort_release(bzla, fsort);

  return exp;
}

BzlaNode *
bzla_exp_const_array(Bzla *bzla, BzlaSortId sort, BzlaNode *value)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fun(bzla, sort));
  assert(bzla_sort_tuple_get_arity(bzla, bzla_sort_fun_get_domain(bzla, sort))
         == 1);
  assert(bzla_sort_array_get_element(bzla, sort)
         == bzla_node_get_sort_id(value));
  assert(value);
  assert(!bzla_sort_is_fun(bzla, bzla_node_get_sort_id(value)));

  BzlaNode *exp, *param;
  BzlaSortId idxsort;

  idxsort       = bzla_sort_array_get_index(bzla, sort);
  param         = bzla_exp_param(bzla, idxsort, 0);
  exp           = bzla_exp_lambda(bzla, param, value);
  exp->is_array = 1;

  bzla_node_release(bzla, param);

  return exp;
}

BzlaNode *
bzla_exp_uf(Bzla *bzla, BzlaSortId sort, const char *symbol)
{
  return bzla_node_create_uf(bzla, sort, symbol);
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_true(Bzla *bzla)
{
  assert(bzla);

  BzlaSortId sort;
  BzlaNode *result;

  sort   = bzla_sort_bv(bzla, 1);
  result = bzla_exp_bv_one(bzla, sort);
  bzla_sort_release(bzla, sort);
  return result;
}

BzlaNode *
bzla_exp_false(Bzla *bzla)
{
  assert(bzla);

  BzlaSortId sort;
  BzlaNode *result;

  sort   = bzla_sort_bv(bzla, 1);
  result = bzla_exp_bv_zero(bzla, sort);
  bzla_sort_release(bzla, sort);
  return result;
}

BzlaNode *
bzla_exp_implies(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  assert(bzla_node_bv_get_width(bzla, e0) == 1);
  return bzla_node_invert(bzla_exp_bv_and(bzla, e0, bzla_node_invert(e1)));
}

BzlaNode *
bzla_exp_iff(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  assert(bzla_node_bv_get_width(bzla, e0) == 1);
  return bzla_exp_eq(bzla, e0, e1);
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_eq_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
  {
    if (bzla_node_is_fun(e0))
      result = bzla_rewrite_binary_exp(bzla, BZLA_FUN_EQ_NODE, e0, e1);
    else
      result = bzla_rewrite_binary_exp(bzla, BZLA_BV_EQ_NODE, e0, e1);
  }
  else
    result = bzla_node_create_eq(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_ne(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_eq_exp(bzla, e0, e1));
  return bzla_node_invert(bzla_exp_eq(bzla, e0, e1));
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_cond(Bzla *bzla, BzlaNode *e_cond, BzlaNode *e_if, BzlaNode *e_else)
{
  assert(bzla == bzla_node_real_addr(e_cond)->bzla);
  assert(bzla == bzla_node_real_addr(e_if)->bzla);
  assert(bzla == bzla_node_real_addr(e_else)->bzla);

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    return bzla_rewrite_ternary_exp(bzla, BZLA_COND_NODE, e_cond, e_if, e_else);

  return bzla_node_create_cond(bzla, e_cond, e_if, e_else);
}

BzlaNode *
bzla_exp_bv_const(Bzla *bzla, const BzlaBitVector *bits)
{
  return bzla_node_create_bv_const(bzla, bits);
}

/*------------------------------------------------------------------------*/

static BzlaNode *
int_min_exp(Bzla *bzla, uint32_t width)
{
  assert(bzla);
  assert(width > 0);

  BzlaBitVector *bv;
  BzlaNode *result;

  bv = bzla_bv_new(bzla->mm, width);
  bzla_bv_set_bit(bv, width - 1, 1);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_zero(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_new(bzla->mm, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_ones(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_ones(bzla->mm, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_one(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_one(bzla->mm, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_min_signed(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_min_signed(bzla->mm, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_max_signed(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_max_signed(bzla->mm, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_int(Bzla *bzla, int32_t i, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_int64_to_bv(bzla->mm, i, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

BzlaNode *
bzla_exp_bv_unsigned(Bzla *bzla, uint32_t u, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_bv(bzla, sort));

  uint32_t width;
  BzlaNode *result;
  BzlaBitVector *bv;

  width  = bzla_sort_bv_get_width(bzla, sort);
  bv     = bzla_bv_uint64_to_bv(bzla->mm, u, width);
  result = bzla_exp_bv_const(bzla, bv);
  bzla_bv_free(bzla->mm, bv);
  return result;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_bv_not(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  (void) bzla;
  bzla_node_copy(bzla, exp);
  return bzla_node_invert(exp);
}

BzlaNode *
bzla_exp_bv_neg(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *one;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));
  one    = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(exp));
  result = bzla_exp_bv_add(bzla, bzla_node_invert(exp), one);
  bzla_node_release(bzla, one);
  return result;
}

BzlaNode *
bzla_exp_bv_redor(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *zero;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  zero   = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(exp));
  result = bzla_node_invert(bzla_exp_eq(bzla, exp, zero));
  bzla_node_release(bzla, zero);
  return result;
}

BzlaNode *
bzla_exp_bv_redxor(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *slice, *xor;
  uint32_t i, width;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  width = bzla_node_bv_get_width(bzla, exp);

  result = bzla_exp_bv_slice(bzla, exp, 0, 0);
  for (i = 1; i < width; i++)
  {
    slice = bzla_exp_bv_slice(bzla, exp, i, i);
    xor   = bzla_exp_bv_xor(bzla, result, slice);
    bzla_node_release(bzla, slice);
    bzla_node_release(bzla, result);
    result = xor;
  }
  return result;
}

BzlaNode *
bzla_exp_bv_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_slice_exp(bzla, exp, upper, lower));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_slice_exp(bzla, exp, upper, lower);
  else
    result = bzla_node_create_bv_slice(bzla, exp, upper, lower);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_redand(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *ones;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  ones   = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(exp));
  result = bzla_exp_eq(bzla, exp, ones);
  bzla_node_release(bzla, ones);
  return result;
}

BzlaNode *
bzla_exp_bv_uext(Bzla *bzla, BzlaNode *exp, uint32_t width)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *zero;
  BzlaSortId sort;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_ext_exp(bzla, exp));

  if (width == 0)
    result = bzla_node_copy(bzla, exp);
  else
  {
    assert(width > 0);
    sort = bzla_sort_bv(bzla, width);
    zero = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
    result = bzla_exp_bv_concat(bzla, zero, exp);
    bzla_node_release(bzla, zero);
  }
  return result;
}

BzlaNode *
bzla_exp_bv_sext(Bzla *bzla, BzlaNode *exp, uint32_t width)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *result, *zero, *ones, *neg, *cond;
  uint32_t exp_width;
  BzlaSortId sort;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_ext_exp(bzla, exp));

  if (width == 0)
    result = bzla_node_copy(bzla, exp);
  else
  {
    assert(width > 0);
    sort = bzla_sort_bv(bzla, width);
    zero = bzla_exp_bv_zero(bzla, sort);
    ones = bzla_exp_bv_ones(bzla, sort);
    bzla_sort_release(bzla, sort);
    exp_width = bzla_node_bv_get_width(bzla, exp);
    neg       = bzla_exp_bv_slice(bzla, exp, exp_width - 1, exp_width - 1);
    cond      = bzla_exp_cond(bzla, neg, ones, zero);
    result    = bzla_exp_bv_concat(bzla, cond, exp);
    bzla_node_release(bzla, zero);
    bzla_node_release(bzla, ones);
    bzla_node_release(bzla, neg);
    bzla_node_release(bzla, cond);
  }
  return result;
}

BzlaNode *
bzla_exp_bv_xor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, * or, *and;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  or     = bzla_exp_bv_or(bzla, e0, e1);
  and    = bzla_exp_bv_and(bzla, e0, e1);
  result = bzla_exp_bv_and(bzla, or, bzla_node_invert(and));
  bzla_node_release(bzla, or);
  bzla_node_release(bzla, and);
  return result;
}

BzlaNode *
bzla_exp_bv_xnor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_node_invert(bzla_exp_bv_xor(bzla, e0, e1));
}

BzlaNode *
bzla_exp_bv_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_AND_NODE, e0, e1);
  else
    result = bzla_node_create_bv_and(bzla, e0, e1);

  assert(result);
  return result;
}

static BzlaNode *
create_bin_n_exp(Bzla *bzla,
                 BzlaNode *(*func)(Bzla *, BzlaNode *, BzlaNode *),
                 BzlaNode *args[],
                 uint32_t argc)
{
  assert(argc > 0);

  uint32_t i;
  BzlaNode *result, *tmp, *arg;

  result = 0;
  for (i = 0; i < argc; i++)
  {
    arg = args[i];
    if (result)
    {
      tmp = func(bzla, arg, result);
      bzla_node_release(bzla, result);
      result = tmp;
    }
    else
      result = bzla_node_copy(bzla, arg);
  }
  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_and_n(Bzla *bzla, BzlaNode *args[], uint32_t argc)
{
  return create_bin_n_exp(bzla, bzla_exp_bv_and, args, argc);
}

BzlaNode *
bzla_exp_bv_nand(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_node_invert(bzla_exp_bv_and(bzla, e0, e1));
}

BzlaNode *
bzla_exp_bv_or(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_node_invert(
      bzla_exp_bv_and(bzla, bzla_node_invert(e0), bzla_node_invert(e1)));
}

BzlaNode *
bzla_exp_bv_nor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_node_invert(bzla_exp_bv_or(bzla, e0, e1));
}
BzlaNode *
bzla_exp_bv_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_ADD_NODE, e0, e1);
  else
    result = bzla_node_create_bv_add(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_add_n(Bzla *bzla, BzlaNode *args[], uint32_t argc)
{
  return create_bin_n_exp(bzla, bzla_exp_bv_add, args, argc);
}

BzlaNode *
bzla_exp_bv_uaddo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *uext_e1, *uext_e2, *add;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width   = bzla_node_bv_get_width(bzla, e0);
  uext_e1 = bzla_exp_bv_uext(bzla, e0, 1);
  uext_e2 = bzla_exp_bv_uext(bzla, e1, 1);
  add     = bzla_exp_bv_add(bzla, uext_e1, uext_e2);
  result  = bzla_exp_bv_slice(bzla, add, width, width);
  bzla_node_release(bzla, uext_e1);
  bzla_node_release(bzla, uext_e2);
  bzla_node_release(bzla, add);
  return result;
}

BzlaNode *
bzla_exp_bv_saddo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e1, *sign_e2, *sign_result;
  BzlaNode *add, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width       = bzla_node_bv_get_width(bzla, e0);
  sign_e1     = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  sign_e2     = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  add         = bzla_exp_bv_add(bzla, e0, e1);
  sign_result = bzla_exp_bv_slice(bzla, add, width - 1, width - 1);
  and1        = bzla_exp_bv_and(bzla, sign_e1, sign_e2);
  or1         = bzla_exp_bv_and(bzla, and1, bzla_node_invert(sign_result));
  and2        = bzla_exp_bv_and(
      bzla, bzla_node_invert(sign_e1), bzla_node_invert(sign_e2));
  or2    = bzla_exp_bv_and(bzla, and2, sign_result);
  result = bzla_exp_bv_or(bzla, or1, or2);
  bzla_node_release(bzla, and1);
  bzla_node_release(bzla, and2);
  bzla_node_release(bzla, or1);
  bzla_node_release(bzla, or2);
  bzla_node_release(bzla, add);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, sign_e2);
  bzla_node_release(bzla, sign_result);
  return result;
}

BzlaNode *
bzla_exp_bv_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_MUL_NODE, e0, e1);
  else
    result = bzla_node_create_bv_mul(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_umulo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *uext_e1, *uext_e2, *mul, *slice, *and, * or, **temps_e2;
  BzlaSortId sort;
  uint32_t i, width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width = bzla_node_bv_get_width(bzla, e0);
  if (width == 1)
  {
    sort   = bzla_sort_bv(bzla, 1);
    result = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
    return result;
  }
  BZLA_NEWN(bzla->mm, temps_e2, width - 1);
  temps_e2[0] = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  for (i = 1; i < width - 1; i++)
  {
    slice       = bzla_exp_bv_slice(bzla, e1, width - 1 - i, width - 1 - i);
    temps_e2[i] = bzla_exp_bv_or(bzla, temps_e2[i - 1], slice);
    bzla_node_release(bzla, slice);
  }
  slice  = bzla_exp_bv_slice(bzla, e0, 1, 1);
  result = bzla_exp_bv_and(bzla, slice, temps_e2[0]);
  bzla_node_release(bzla, slice);
  for (i = 1; i < width - 1; i++)
  {
    slice = bzla_exp_bv_slice(bzla, e0, i + 1, i + 1);
    and   = bzla_exp_bv_and(bzla, slice, temps_e2[i]);
    or    = bzla_exp_bv_or(bzla, result, and);
    bzla_node_release(bzla, slice);
    bzla_node_release(bzla, and);
    bzla_node_release(bzla, result);
    result = or ;
  }
  uext_e1 = bzla_exp_bv_uext(bzla, e0, 1);
  uext_e2 = bzla_exp_bv_uext(bzla, e1, 1);
  mul     = bzla_exp_bv_mul(bzla, uext_e1, uext_e2);
  slice   = bzla_exp_bv_slice(bzla, mul, width, width);
  or      = bzla_exp_bv_or(bzla, result, slice);
  bzla_node_release(bzla, uext_e1);
  bzla_node_release(bzla, uext_e2);
  bzla_node_release(bzla, mul);
  bzla_node_release(bzla, slice);
  bzla_node_release(bzla, result);
  result = or ;
  for (i = 0; i < width - 1; i++) bzla_node_release(bzla, temps_e2[i]);
  BZLA_DELETEN(bzla->mm, temps_e2, width - 1);
  return result;
}

BzlaNode *
bzla_exp_bv_smulo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sext_e1, *sext_e2, *sign_e1, *sign_e2, *sext_sign_e1;
  BzlaNode *sext_sign_e2, *xor_sign_e1, *xor_sign_e2, *mul, *slice, *slice_n;
  BzlaNode *slice_n_minus_1, *xor, *and, * or, **temps_e2;
  uint32_t i, width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width = bzla_node_bv_get_width(bzla, e0);
  if (width == 1) return bzla_exp_bv_and(bzla, e0, e1);
  if (width == 2)
  {
    sext_e1         = bzla_exp_bv_sext(bzla, e0, 1);
    sext_e2         = bzla_exp_bv_sext(bzla, e1, 1);
    mul             = bzla_exp_bv_mul(bzla, sext_e1, sext_e2);
    slice_n         = bzla_exp_bv_slice(bzla, mul, width, width);
    slice_n_minus_1 = bzla_exp_bv_slice(bzla, mul, width - 1, width - 1);
    result          = bzla_exp_bv_xor(bzla, slice_n, slice_n_minus_1);
    bzla_node_release(bzla, sext_e1);
    bzla_node_release(bzla, sext_e2);
    bzla_node_release(bzla, mul);
    bzla_node_release(bzla, slice_n);
    bzla_node_release(bzla, slice_n_minus_1);
  }
  else
  {
    sign_e1      = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
    sign_e2      = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
    sext_sign_e1 = bzla_exp_bv_sext(bzla, sign_e1, width - 1);
    sext_sign_e2 = bzla_exp_bv_sext(bzla, sign_e2, width - 1);
    xor_sign_e1  = bzla_exp_bv_xor(bzla, e0, sext_sign_e1);
    xor_sign_e2  = bzla_exp_bv_xor(bzla, e1, sext_sign_e2);
    BZLA_NEWN(bzla->mm, temps_e2, width - 2);
    temps_e2[0] = bzla_exp_bv_slice(bzla, xor_sign_e2, width - 2, width - 2);
    for (i = 1; i < width - 2; i++)
    {
      slice =
          bzla_exp_bv_slice(bzla, xor_sign_e2, width - 2 - i, width - 2 - i);
      temps_e2[i] = bzla_exp_bv_or(bzla, temps_e2[i - 1], slice);
      bzla_node_release(bzla, slice);
    }
    slice  = bzla_exp_bv_slice(bzla, xor_sign_e1, 1, 1);
    result = bzla_exp_bv_and(bzla, slice, temps_e2[0]);
    bzla_node_release(bzla, slice);
    for (i = 1; i < width - 2; i++)
    {
      slice = bzla_exp_bv_slice(bzla, xor_sign_e1, i + 1, i + 1);
      and   = bzla_exp_bv_and(bzla, slice, temps_e2[i]);
      or    = bzla_exp_bv_or(bzla, result, and);
      bzla_node_release(bzla, slice);
      bzla_node_release(bzla, and);
      bzla_node_release(bzla, result);
      result = or ;
    }
    sext_e1         = bzla_exp_bv_sext(bzla, e0, 1);
    sext_e2         = bzla_exp_bv_sext(bzla, e1, 1);
    mul             = bzla_exp_bv_mul(bzla, sext_e1, sext_e2);
    slice_n         = bzla_exp_bv_slice(bzla, mul, width, width);
    slice_n_minus_1 = bzla_exp_bv_slice(bzla, mul, width - 1, width - 1);
    xor             = bzla_exp_bv_xor(bzla, slice_n, slice_n_minus_1);
    or              = bzla_exp_bv_or(bzla, result, xor);
    bzla_node_release(bzla, sext_e1);
    bzla_node_release(bzla, sext_e2);
    bzla_node_release(bzla, sign_e1);
    bzla_node_release(bzla, sign_e2);
    bzla_node_release(bzla, sext_sign_e1);
    bzla_node_release(bzla, sext_sign_e2);
    bzla_node_release(bzla, xor_sign_e1);
    bzla_node_release(bzla, xor_sign_e2);
    bzla_node_release(bzla, mul);
    bzla_node_release(bzla, slice_n);
    bzla_node_release(bzla, slice_n_minus_1);
    bzla_node_release(bzla, xor);
    bzla_node_release(bzla, result);
    result = or ;
    for (i = 0; i < width - 2; i++) bzla_node_release(bzla, temps_e2[i]);
    BZLA_DELETEN(bzla->mm, temps_e2, width - 2);
  }
  return result;
}

BzlaNode *
bzla_exp_bv_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_ULT_NODE, e0, e1);
  else
    result = bzla_node_create_bv_ult(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_SLT))
  {
    BzlaNode *determined_by_sign, *eq_sign, *ult, *eq_sign_and_ult;
    BzlaNode *s0, *s1, *r0, *r1, *l, *r;

    uint32_t width;

    e0 = bzla_simplify_exp(bzla, e0);
    e1 = bzla_simplify_exp(bzla, e1);
    assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

    width = bzla_node_bv_get_width(bzla, e0);
    if (width == 1) return bzla_exp_bv_and(bzla, e0, bzla_node_invert(e1));
    s0                 = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
    s1                 = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
    r0                 = bzla_exp_bv_slice(bzla, e0, width - 2, 0);
    r1                 = bzla_exp_bv_slice(bzla, e1, width - 2, 0);
    ult                = bzla_exp_bv_ult(bzla, r0, r1);
    determined_by_sign = bzla_exp_bv_and(bzla, s0, bzla_node_invert(s1));
    l                  = bzla_node_copy(bzla, determined_by_sign);
    r                  = bzla_exp_bv_and(bzla, bzla_node_invert(s0), s1);
    eq_sign = bzla_exp_bv_and(bzla, bzla_node_invert(l), bzla_node_invert(r));
    eq_sign_and_ult = bzla_exp_bv_and(bzla, eq_sign, ult);
    result          = bzla_exp_bv_or(bzla, determined_by_sign, eq_sign_and_ult);
    bzla_node_release(bzla, s0);
    bzla_node_release(bzla, s1);
    bzla_node_release(bzla, r0);
    bzla_node_release(bzla, r1);
    bzla_node_release(bzla, ult);
    bzla_node_release(bzla, determined_by_sign);
    bzla_node_release(bzla, l);
    bzla_node_release(bzla, r);
    bzla_node_release(bzla, eq_sign);
    bzla_node_release(bzla, eq_sign_and_ult);
  }
  else
  {
    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
      result = bzla_rewrite_binary_exp(bzla, BZLA_BV_SLT_NODE, e0, e1);
    else
      result = bzla_node_create_bv_slt(bzla, e0, e1);
  }

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_ulte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *ult;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  ult    = bzla_exp_bv_ult(bzla, e1, e0);
  result = bzla_exp_bv_not(bzla, ult);
  bzla_node_release(bzla, ult);
  return result;
}

BzlaNode *
bzla_exp_bv_slte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *slt;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  slt    = bzla_exp_bv_slt(bzla, e1, e0);
  result = bzla_exp_bv_not(bzla, slt);
  bzla_node_release(bzla, slt);
  return result;
}

BzlaNode *
bzla_exp_bv_ugt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_exp_bv_ult(bzla, e1, e0);
}

BzlaNode *
bzla_exp_bv_sgt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));
  return bzla_exp_bv_slt(bzla, e1, e0);
}

BzlaNode *
bzla_exp_bv_ugte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *ult;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  ult    = bzla_exp_bv_ult(bzla, e0, e1);
  result = bzla_exp_bv_not(bzla, ult);
  bzla_node_release(bzla, ult);
  return result;
}

BzlaNode *
bzla_exp_bv_sgte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *slt;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  slt    = bzla_exp_bv_slt(bzla, e0, e1);
  result = bzla_exp_bv_not(bzla, slt);
  bzla_node_release(bzla, slt);
  return result;
}

BzlaNode *
bzla_exp_bv_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_SLL_NODE, e0, e1);
  else
    result = bzla_node_create_bv_sll(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_SRL_NODE, e0, e1);
  else
    result = bzla_node_create_bv_srl(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_sra(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e1, *srl1, *srl2;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  width   = bzla_node_bv_get_width(bzla, e0);
  sign_e1 = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  srl1    = bzla_exp_bv_srl(bzla, e0, e1);
  srl2    = bzla_exp_bv_srl(bzla, bzla_node_invert(e0), e1);
  result  = bzla_exp_cond(bzla, sign_e1, bzla_node_invert(srl2), srl1);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, srl1);
  bzla_node_release(bzla, srl2);
  return result;
}

static BzlaNode *
exp_rotate(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, bool left)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  uint32_t width;
  BzlaNode *w, *nbits, *dbits, *cond, *zero, *lshift, *rshift, *rot;
  BzlaNode *res;
  BzlaSortId sort;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  width = bzla_node_bv_get_width(bzla, e0);
  assert(width > 0);
  if (width == 1) return bzla_node_copy(bzla, e0);

  /* actual number of bits to rotate is e1 % width */
  sort  = bzla_node_get_sort_id(e0);
  w     = bzla_exp_bv_unsigned(bzla, width, sort);
  nbits = bzla_exp_bv_urem(bzla, e1, w);
  dbits = bzla_exp_bv_sub(bzla, w, nbits); /* width - nbits */

  /* rotate left: (e0 << nbits) | (e0 >> (dbits))
   * rotate right: (e0 >> nbits) | (e0 << (dbits)) */
  if (left)
  {
    lshift = bzla_exp_bv_sll(bzla, e0, nbits);
    rshift = bzla_exp_bv_srl(bzla, e0, dbits);
  }
  else
  {
    lshift = bzla_exp_bv_sll(bzla, e0, dbits);
    rshift = bzla_exp_bv_srl(bzla, e0, nbits);
  }
  rot = bzla_exp_bv_or(bzla, lshift, rshift);

  /* if nbits == 0 -> exp, else we have to rotate */
  zero = bzla_exp_bv_zero(bzla, sort);
  cond = bzla_exp_eq(bzla, nbits, zero);
  res  = bzla_exp_cond(bzla, cond, e0, rot);

  bzla_node_release(bzla, rot);
  bzla_node_release(bzla, rshift);
  bzla_node_release(bzla, lshift);
  bzla_node_release(bzla, zero);
  bzla_node_release(bzla, cond);
  bzla_node_release(bzla, dbits);
  bzla_node_release(bzla, nbits);
  bzla_node_release(bzla, w);
  return res;
}

BzlaNode *
bzla_exp_bv_rol(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return exp_rotate(bzla, e0, e1, true);
}

BzlaNode *
bzla_exp_bv_ror(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return exp_rotate(bzla, e0, e1, false);
}

static BzlaNode *
exp_bv_rotate_i(Bzla *bzla, BzlaNode *exp, uint32_t nbits, bool is_left)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  BzlaNode *left, *right, *res;
  uint32_t width;

  width = bzla_node_bv_get_width(bzla, exp);
  assert(width > 0);
  nbits %= width;

  if (nbits)
  {
    if (is_left) nbits = width - nbits;

    assert(1 <= nbits && nbits < width);

    left  = bzla_exp_bv_slice(bzla, exp, nbits - 1, 0);
    right = bzla_exp_bv_slice(bzla, exp, width - 1, nbits);

    res = bzla_exp_bv_concat(bzla, left, right);

    bzla_node_release(bzla, left);
    bzla_node_release(bzla, right);
  }
  else
  {
    res = bzla_node_copy(bzla, exp);
  }
  assert(bzla_node_bv_get_width(bzla, res) == width);
  return res;
}

BzlaNode *
bzla_exp_bv_roli(Bzla *bzla, BzlaNode *exp, uint32_t nbits)
{
  return exp_bv_rotate_i(bzla, exp, nbits, true);
}

BzlaNode *
bzla_exp_bv_rori(Bzla *bzla, BzlaNode *exp, uint32_t nbits)
{
  return exp_bv_rotate_i(bzla, exp, nbits, false);
}

BzlaNode *
bzla_exp_bv_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *neg_e2;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  neg_e2 = bzla_exp_bv_neg(bzla, e1);
  result = bzla_exp_bv_add(bzla, e0, neg_e2);
  bzla_node_release(bzla, neg_e2);
  return result;
}

BzlaNode *
bzla_exp_bv_usubo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *uext_e1, *uext_e2, *add1, *add2, *one;
  BzlaSortId sort;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width   = bzla_node_bv_get_width(bzla, e0);
  uext_e1 = bzla_exp_bv_uext(bzla, e0, 1);
  uext_e2 = bzla_exp_bv_uext(bzla, bzla_node_invert(e1), 1);
  assert(width < INT32_MAX);
  sort = bzla_sort_bv(bzla, width + 1);
  one  = bzla_exp_bv_one(bzla, sort);
  bzla_sort_release(bzla, sort);
  add1   = bzla_exp_bv_add(bzla, uext_e2, one);
  add2   = bzla_exp_bv_add(bzla, uext_e1, add1);
  result = bzla_node_invert(bzla_exp_bv_slice(bzla, add2, width, width));
  bzla_node_release(bzla, uext_e1);
  bzla_node_release(bzla, uext_e2);
  bzla_node_release(bzla, add1);
  bzla_node_release(bzla, add2);
  bzla_node_release(bzla, one);
  return result;
}

BzlaNode *
bzla_exp_bv_ssubo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e1, *sign_e2, *sign_result;
  BzlaNode *sub, *and1, *and2, *or1, *or2;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width       = bzla_node_bv_get_width(bzla, e0);
  sign_e1     = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  sign_e2     = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  sub         = bzla_exp_bv_sub(bzla, e0, e1);
  sign_result = bzla_exp_bv_slice(bzla, sub, width - 1, width - 1);
  and1        = bzla_exp_bv_and(bzla, bzla_node_invert(sign_e1), sign_e2);
  or1         = bzla_exp_bv_and(bzla, and1, sign_result);
  and2        = bzla_exp_bv_and(bzla, sign_e1, bzla_node_invert(sign_e2));
  or2         = bzla_exp_bv_and(bzla, and2, bzla_node_invert(sign_result));
  result      = bzla_exp_bv_or(bzla, or1, or2);
  bzla_node_release(bzla, and1);
  bzla_node_release(bzla, and2);
  bzla_node_release(bzla, or1);
  bzla_node_release(bzla, or2);
  bzla_node_release(bzla, sub);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, sign_e2);
  bzla_node_release(bzla, sign_result);
  return result;
}

BzlaNode *
bzla_exp_bv_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_UDIV_NODE, e0, e1);
  else
    result = bzla_node_create_bv_udiv(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_sdiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e1, *sign_e2, *xor, *neg_e1, *neg_e2;
  BzlaNode *cond_e1, *cond_e2, *udiv, *neg_udiv;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width = bzla_node_bv_get_width(bzla, e0);

  if (width == 1)
    return bzla_node_invert(bzla_exp_bv_and(bzla, bzla_node_invert(e0), e1));

  sign_e1 = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  sign_e2 = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  /* xor: must result be signed? */
  xor    = bzla_exp_bv_xor(bzla, sign_e1, sign_e2);
  neg_e1 = bzla_exp_bv_neg(bzla, e0);
  neg_e2 = bzla_exp_bv_neg(bzla, e1);
  /* normalize e0 and e1 if necessary */
  cond_e1  = bzla_exp_cond(bzla, sign_e1, neg_e1, e0);
  cond_e2  = bzla_exp_cond(bzla, sign_e2, neg_e2, e1);
  udiv     = bzla_exp_bv_udiv(bzla, cond_e1, cond_e2);
  neg_udiv = bzla_exp_bv_neg(bzla, udiv);
  /* sign result if necessary */
  result = bzla_exp_cond(bzla, xor, neg_udiv, udiv);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, sign_e2);
  bzla_node_release(bzla, xor);
  bzla_node_release(bzla, neg_e1);
  bzla_node_release(bzla, neg_e2);
  bzla_node_release(bzla, cond_e1);
  bzla_node_release(bzla, cond_e2);
  bzla_node_release(bzla, udiv);
  bzla_node_release(bzla, neg_udiv);
  return result;
}

BzlaNode *
bzla_exp_bv_sdivo(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *int_min, *ones, *eq1, *eq2;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  int_min = int_min_exp(bzla, bzla_node_bv_get_width(bzla, e0));
  ones    = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(e1));
  eq1     = bzla_exp_eq(bzla, e0, int_min);
  eq2     = bzla_exp_eq(bzla, e1, ones);
  result  = bzla_exp_bv_and(bzla, eq1, eq2);
  bzla_node_release(bzla, int_min);
  bzla_node_release(bzla, ones);
  bzla_node_release(bzla, eq1);
  bzla_node_release(bzla, eq2);
  return result;
}

BzlaNode *
bzla_exp_bv_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_UREM_NODE, e0, e1);
  else
    result = bzla_node_create_bv_urem(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_srem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1;
  BzlaNode *cond_e0, *cond_e1, *urem, *neg_urem;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width = bzla_node_bv_get_width(bzla, e0);

  if (width == 1) return bzla_exp_bv_and(bzla, e0, bzla_node_invert(e1));

  sign_e0 = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  sign_e1 = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  neg_e0  = bzla_exp_bv_neg(bzla, e0);
  neg_e1  = bzla_exp_bv_neg(bzla, e1);
  /* normalize e0 and e1 if necessary */
  cond_e0  = bzla_exp_cond(bzla, sign_e0, neg_e0, e0);
  cond_e1  = bzla_exp_cond(bzla, sign_e1, neg_e1, e1);
  urem     = bzla_exp_bv_urem(bzla, cond_e0, cond_e1);
  neg_urem = bzla_exp_bv_neg(bzla, urem);
  /* sign result if necessary */
  /* result is negative if e0 is negative */
  result = bzla_exp_cond(bzla, sign_e0, neg_urem, urem);
  bzla_node_release(bzla, sign_e0);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, neg_e0);
  bzla_node_release(bzla, neg_e1);
  bzla_node_release(bzla, cond_e0);
  bzla_node_release(bzla, cond_e1);
  bzla_node_release(bzla, urem);
  bzla_node_release(bzla, neg_urem);
  return result;
}

BzlaNode *
bzla_exp_bv_smod(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result, *sign_e0, *sign_e1, *neg_e0, *neg_e1, *cond_e0, *cond_e1;
  BzlaNode *neg_e0_and_e1, *neg_e0_and_neg_e1, *zero, *e0_zero;
  BzlaNode *neg_urem, *add1, *add2, *or1, *or2, *e0_and_e1, *e0_and_neg_e1;
  BzlaNode *cond_case1, *cond_case2, *cond_case3, *cond_case4, *urem;
  BzlaNode *urem_zero, *gadd1, *gadd2;
  uint32_t width;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  width     = bzla_node_bv_get_width(bzla, e0);
  zero      = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
  e0_zero   = bzla_exp_eq(bzla, zero, e0);
  sign_e0   = bzla_exp_bv_slice(bzla, e0, width - 1, width - 1);
  sign_e1   = bzla_exp_bv_slice(bzla, e1, width - 1, width - 1);
  neg_e0    = bzla_exp_bv_neg(bzla, e0);
  neg_e1    = bzla_exp_bv_neg(bzla, e1);
  e0_and_e1 = bzla_exp_bv_and(
      bzla, bzla_node_invert(sign_e0), bzla_node_invert(sign_e1));
  e0_and_neg_e1     = bzla_exp_bv_and(bzla, bzla_node_invert(sign_e0), sign_e1);
  neg_e0_and_e1     = bzla_exp_bv_and(bzla, sign_e0, bzla_node_invert(sign_e1));
  neg_e0_and_neg_e1 = bzla_exp_bv_and(bzla, sign_e0, sign_e1);
  /* normalize e0 and e1 if necessary */
  cond_e0    = bzla_exp_cond(bzla, sign_e0, neg_e0, e0);
  cond_e1    = bzla_exp_cond(bzla, sign_e1, neg_e1, e1);
  urem       = bzla_exp_bv_urem(bzla, cond_e0, cond_e1);
  urem_zero  = bzla_exp_eq(bzla, urem, zero);
  neg_urem   = bzla_exp_bv_neg(bzla, urem);
  add1       = bzla_exp_bv_add(bzla, neg_urem, e1);
  add2       = bzla_exp_bv_add(bzla, urem, e1);
  gadd1      = bzla_exp_cond(bzla, urem_zero, zero, add1);
  gadd2      = bzla_exp_cond(bzla, urem_zero, zero, add2);
  cond_case1 = bzla_exp_cond(bzla, e0_and_e1, urem, zero);
  cond_case2 = bzla_exp_cond(bzla, neg_e0_and_e1, gadd1, zero);
  cond_case3 = bzla_exp_cond(bzla, e0_and_neg_e1, gadd2, zero);
  cond_case4 = bzla_exp_cond(bzla, neg_e0_and_neg_e1, neg_urem, zero);
  or1        = bzla_exp_bv_or(bzla, cond_case1, cond_case2);
  or2        = bzla_exp_bv_or(bzla, cond_case3, cond_case4);
  result     = bzla_exp_bv_or(bzla, or1, or2);
  bzla_node_release(bzla, zero);
  bzla_node_release(bzla, e0_zero);
  bzla_node_release(bzla, sign_e0);
  bzla_node_release(bzla, sign_e1);
  bzla_node_release(bzla, neg_e0);
  bzla_node_release(bzla, neg_e1);
  bzla_node_release(bzla, cond_e0);
  bzla_node_release(bzla, cond_e1);
  bzla_node_release(bzla, urem_zero);
  bzla_node_release(bzla, cond_case1);
  bzla_node_release(bzla, cond_case2);
  bzla_node_release(bzla, cond_case3);
  bzla_node_release(bzla, cond_case4);
  bzla_node_release(bzla, urem);
  bzla_node_release(bzla, neg_urem);
  bzla_node_release(bzla, add1);
  bzla_node_release(bzla, add2);
  bzla_node_release(bzla, gadd1);
  bzla_node_release(bzla, gadd2);
  bzla_node_release(bzla, or1);
  bzla_node_release(bzla, or2);
  bzla_node_release(bzla, e0_and_e1);
  bzla_node_release(bzla, neg_e0_and_e1);
  bzla_node_release(bzla, e0_and_neg_e1);
  bzla_node_release(bzla, neg_e0_and_neg_e1);
  return result;
}

BzlaNode *
bzla_exp_bv_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_concat_exp(bzla, e0, e1));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_BV_CONCAT_NODE, e0, e1);
  else
    result = bzla_node_create_bv_concat(bzla, e0, e1);

  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_repeat(Bzla *bzla, BzlaNode *exp, uint32_t n)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(((uint32_t) UINT32_MAX / n) >= bzla_node_bv_get_width(bzla, exp));

  BzlaNode *result, *tmp;
  uint32_t i;

  result = bzla_node_copy(bzla, exp);
  for (i = 1; i < n; i++)
  {
    tmp    = result;
    result = bzla_exp_bv_concat(bzla, tmp, exp);
    bzla_node_release(bzla, tmp);
  }
  assert(result);
  return result;
}

BzlaNode *
bzla_exp_bv_inc(Bzla *bzla, BzlaNode *exp)
{
  BzlaNode *one, *result;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  one    = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(exp));
  result = bzla_exp_bv_add(bzla, exp, one);
  bzla_node_release(bzla, one);
  return result;
}

BzlaNode *
bzla_exp_bv_dec(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla == bzla_node_real_addr(exp)->bzla);

  BzlaNode *one, *result;

  exp = bzla_simplify_exp(bzla, exp);
  assert(bzla_dbg_precond_regular_unary_bv_exp(bzla, exp));

  one    = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(exp));
  result = bzla_exp_bv_sub(bzla, exp, one);
  bzla_node_release(bzla, one);
  return result;
}

/*------------------------------------------------------------------------*/

static BzlaNode *
exp_rm_const_aux(Bzla *bzla, const BzlaRoundingMode rm)
{
  return bzla_node_create_rm_const(bzla, rm);
}

BzlaNode *
bzla_exp_rm_const(Bzla *bzla, BzlaRoundingMode rm)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  return exp_rm_const_aux(bzla, rm);
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_fp_const_fp(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  return bzla_node_create_fp_const(bzla, fp);
}

BzlaNode *
bzla_exp_fp_pos_zero(Bzla *bzla, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode *result;
  BzlaFloatingPoint *fp;

  fp     = bzla_fp_zero(bzla, sort, false);
  result = bzla_exp_fp_const_fp(bzla, fp);
  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_neg_zero(Bzla *bzla, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode *result;
  BzlaFloatingPoint *fp;

  fp     = bzla_fp_zero(bzla, sort, true);
  result = bzla_exp_fp_const_fp(bzla, fp);
  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_pos_inf(Bzla *bzla, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode *result;
  BzlaFloatingPoint *fp;

  fp     = bzla_fp_inf(bzla, sort, false);
  result = bzla_exp_fp_const_fp(bzla, fp);
  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_neg_inf(Bzla *bzla, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode *result;
  BzlaFloatingPoint *fp;

  fp     = bzla_fp_inf(bzla, sort, true);
  result = bzla_exp_fp_const_fp(bzla, fp);
  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_nan(Bzla *bzla, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaNode *result;
  BzlaFloatingPoint *fp;

  fp     = bzla_fp_nan(bzla, sort);
  result = bzla_exp_fp_const_fp(bzla, fp);
  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_const(Bzla *bzla,
                  BzlaNode *e0_sign,
                  BzlaNode *e1_exp,
                  BzlaNode *e2_sig)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(e0_sign);
  assert(e1_exp);
  assert(e2_sig);
  assert(bzla == bzla_node_real_addr(e0_sign)->bzla);
  assert(bzla == bzla_node_real_addr(e1_exp)->bzla);
  assert(bzla == bzla_node_real_addr(e2_sig)->bzla);
  assert(bzla_node_is_bv_const(e0_sign));
  assert(bzla_node_is_bv_const(e1_exp));
  assert(bzla_node_is_bv_const(e2_sig));
  assert(bzla_node_bv_get_width(bzla, e0_sign) == 1);

  BzlaNode *result;
  BzlaBitVector *bv_e0_sign, *bv_e1_exp, *bv_e2_sig;
  BzlaFloatingPoint *fp;

  e0_sign = bzla_simplify_exp(bzla, e0_sign);
  e1_exp  = bzla_simplify_exp(bzla, e1_exp);
  e2_sig  = bzla_simplify_exp(bzla, e2_sig);

  bv_e0_sign = bzla_node_bv_const_get_bits(e0_sign);
  bv_e1_exp  = bzla_node_bv_const_get_bits(e1_exp);
  bv_e2_sig  = bzla_node_bv_const_get_bits(e2_sig);

  fp     = bzla_fp_fp(bzla, bv_e0_sign, bv_e1_exp, bv_e2_sig);
  result = bzla_exp_fp_const_fp(bzla, fp);

  bzla_fp_free(bzla, fp);
  return result;
}

BzlaNode *
bzla_exp_fp_const_from_real(Bzla *bzla,
                            BzlaSortId sort,
                            BzlaNode *rm,
                            const char *real)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla_node_is_regular(rm));

  BzlaNode *result;

  if (bzla_node_is_rm_const(rm))
  {
    BzlaFloatingPoint *fp;
    fp = bzla_fp_convert_from_real(
        bzla, sort, bzla_node_rm_const_get_rm(rm), real);
    result = bzla_exp_fp_const_fp(bzla, fp);
    bzla_fp_free(bzla, fp);
  }
  else
  {
    BzlaFloatingPoint *fp_rna, *fp_rne, *fp_rtn, *fp_rtp, *fp_rtz;
    BzlaNode *rna, *rne, *rtn, *rtp;
    BzlaNode *c, *t_rna, *t_rne, *t_rtn, *t_rtp, *t_rtz, *e;

    rna = bzla_exp_rm_const(bzla, BZLA_RM_RNA);
    rne = bzla_exp_rm_const(bzla, BZLA_RM_RNE);
    rtn = bzla_exp_rm_const(bzla, BZLA_RM_RTN);
    rtp = bzla_exp_rm_const(bzla, BZLA_RM_RTP);

    fp_rna = bzla_fp_convert_from_real(bzla, sort, BZLA_RM_RNA, real);
    fp_rne = bzla_fp_convert_from_real(bzla, sort, BZLA_RM_RNE, real);
    fp_rtn = bzla_fp_convert_from_real(bzla, sort, BZLA_RM_RTN, real);
    fp_rtp = bzla_fp_convert_from_real(bzla, sort, BZLA_RM_RTP, real);
    fp_rtz = bzla_fp_convert_from_real(bzla, sort, BZLA_RM_RTZ, real);

    t_rna = bzla_exp_fp_const_fp(bzla, fp_rna);
    t_rne = bzla_exp_fp_const_fp(bzla, fp_rne);
    t_rtn = bzla_exp_fp_const_fp(bzla, fp_rtn);
    t_rtp = bzla_exp_fp_const_fp(bzla, fp_rtp);
    t_rtz = bzla_exp_fp_const_fp(bzla, fp_rtz);

    e = t_rtz;

    c      = bzla_exp_eq(bzla, rm, rtp);
    result = bzla_exp_cond(bzla, c, t_rtp, e);
    bzla_node_release(bzla, c);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rtn);
    result = bzla_exp_cond(bzla, c, t_rtn, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rne);
    result = bzla_exp_cond(bzla, c, t_rne, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rna);
    result = bzla_exp_cond(bzla, c, t_rna, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);

    bzla_node_release(bzla, t_rna);
    bzla_node_release(bzla, t_rne);
    bzla_node_release(bzla, t_rtn);
    bzla_node_release(bzla, t_rtp);
    bzla_node_release(bzla, t_rtz);

    bzla_fp_free(bzla, fp_rna);
    bzla_fp_free(bzla, fp_rne);
    bzla_fp_free(bzla, fp_rtn);
    bzla_fp_free(bzla, fp_rtp);
    bzla_fp_free(bzla, fp_rtz);

    bzla_node_release(bzla, rna);
    bzla_node_release(bzla, rne);
    bzla_node_release(bzla, rtn);
    bzla_node_release(bzla, rtp);
  }
  return result;
}

BzlaNode *
bzla_exp_fp_const_from_rational(
    Bzla *bzla, BzlaSortId sort, BzlaNode *rm, const char *num, const char *den)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla_node_is_regular(rm));

  BzlaNode *result;

  if (bzla_node_is_rm_const(rm))
  {
    BzlaFloatingPoint *fp;
    fp = bzla_fp_convert_from_rational(
        bzla, sort, bzla_node_rm_const_get_rm(rm), num, den);
    result = bzla_exp_fp_const_fp(bzla, fp);
    bzla_fp_free(bzla, fp);
  }
  else
  {
    BzlaFloatingPoint *fp_rna, *fp_rne, *fp_rtn, *fp_rtp, *fp_rtz;
    BzlaNode *rna, *rne, *rtn, *rtp;
    BzlaNode *c, *t_rna, *t_rne, *t_rtn, *t_rtp, *t_rtz, *e;

    rna = bzla_exp_rm_const(bzla, BZLA_RM_RNA);
    rne = bzla_exp_rm_const(bzla, BZLA_RM_RNE);
    rtn = bzla_exp_rm_const(bzla, BZLA_RM_RTN);
    rtp = bzla_exp_rm_const(bzla, BZLA_RM_RTP);

    fp_rna = bzla_fp_convert_from_rational(bzla, sort, BZLA_RM_RNA, num, den);
    fp_rne = bzla_fp_convert_from_rational(bzla, sort, BZLA_RM_RNE, num, den);
    fp_rtn = bzla_fp_convert_from_rational(bzla, sort, BZLA_RM_RTN, num, den);
    fp_rtp = bzla_fp_convert_from_rational(bzla, sort, BZLA_RM_RTP, num, den);
    fp_rtz = bzla_fp_convert_from_rational(bzla, sort, BZLA_RM_RTZ, num, den);

    t_rna = bzla_exp_fp_const_fp(bzla, fp_rna);
    t_rne = bzla_exp_fp_const_fp(bzla, fp_rne);
    t_rtn = bzla_exp_fp_const_fp(bzla, fp_rtn);
    t_rtp = bzla_exp_fp_const_fp(bzla, fp_rtp);
    t_rtz = bzla_exp_fp_const_fp(bzla, fp_rtz);

    e = t_rtz;

    c      = bzla_exp_eq(bzla, rm, rtp);
    result = bzla_exp_cond(bzla, c, t_rtp, e);
    bzla_node_release(bzla, c);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rtn);
    result = bzla_exp_cond(bzla, c, t_rtn, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rne);
    result = bzla_exp_cond(bzla, c, t_rne, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);
    e = result;

    c      = bzla_exp_eq(bzla, rm, rna);
    result = bzla_exp_cond(bzla, c, t_rna, e);
    bzla_node_release(bzla, c);
    bzla_node_release(bzla, e);

    bzla_node_release(bzla, t_rna);
    bzla_node_release(bzla, t_rne);
    bzla_node_release(bzla, t_rtn);
    bzla_node_release(bzla, t_rtp);
    bzla_node_release(bzla, t_rtz);

    bzla_fp_free(bzla, fp_rna);
    bzla_fp_free(bzla, fp_rne);
    bzla_fp_free(bzla, fp_rtn);
    bzla_fp_free(bzla, fp_rtp);
    bzla_fp_free(bzla, fp_rtz);

    bzla_node_release(bzla, rna);
    bzla_node_release(bzla, rne);
    bzla_node_release(bzla, rtn);
    bzla_node_release(bzla, rtp);
  }
  return result;
}

BzlaNode *
bzla_exp_fp_fp(Bzla *bzla,
               BzlaNode *e0_sign,
               BzlaNode *e1_exp,
               BzlaNode *e2_sig)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(e0_sign);
  assert(e1_exp);
  assert(e2_sig);
  assert(bzla == bzla_node_real_addr(e0_sign)->bzla);
  assert(bzla == bzla_node_real_addr(e1_exp)->bzla);
  assert(bzla == bzla_node_real_addr(e2_sig)->bzla);
  assert(bzla_node_is_bv(bzla, e0_sign));
  assert(bzla_node_is_bv(bzla, e1_exp));
  assert(bzla_node_is_bv(bzla, e2_sig));
  assert(bzla_node_bv_get_width(bzla, e0_sign) == 1);

  uint32_t ewidth, swidth;
  BzlaNode *result, *tmp, *concat;
  BzlaSortId sort;

  e0_sign = bzla_simplify_exp(bzla, e0_sign);
  e1_exp  = bzla_simplify_exp(bzla, e1_exp);
  e2_sig  = bzla_simplify_exp(bzla, e2_sig);

  tmp    = bzla_exp_bv_concat(bzla, e0_sign, e1_exp);
  concat = bzla_exp_bv_concat(bzla, tmp, e2_sig);

  ewidth = bzla_node_bv_get_width(bzla, e1_exp);
  swidth = 1 + bzla_node_bv_get_width(bzla, e2_sig);
  sort   = bzla_sort_fp(bzla, ewidth, swidth);
  result = bzla_exp_fp_to_fp_from_bv(bzla, concat, sort);

  bzla_node_release(bzla, concat);
  bzla_node_release(bzla, tmp);
  bzla_sort_release(bzla, sort);
  return result;
}

BzlaNode *
bzla_exp_fp_abs(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_ABS_NODE, node);
  else
    result = bzla_node_create_fp_abs(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_neg(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_NEG_NODE, node);
  else
    result = bzla_node_create_fp_neg(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_normal(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_NORM_NODE, node);
  else
    result = bzla_node_create_fp_is_normal(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_subnormal(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_SUBNORM_NODE, node);
  else
    result = bzla_node_create_fp_is_subnormal(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_zero(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_ZERO_NODE, node);
  else
    result = bzla_node_create_fp_is_zero(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_inf(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_INF_NODE, node);
  else
    result = bzla_node_create_fp_is_inf(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_nan(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_NAN_NODE, node);
  else
    result = bzla_node_create_fp_is_nan(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_neg(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_NEG_NODE, node);
  else
    result = bzla_node_create_fp_is_neg(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_is_pos(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_unary_exp(bzla, BZLA_FP_IS_POS_NODE, node);
  else
    result = bzla_node_create_fp_is_pos(bzla, node);
  return result;
}

BzlaNode *
bzla_exp_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_MIN_NODE, e0, e1);
  else
    result = bzla_node_create_fp_min(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_MAX_NODE, e0, e1);
  else
    result = bzla_node_create_fp_max(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_REM_NODE, e0, e1);
  else
    result = bzla_node_create_fp_rem(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_fpeq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  BzlaNode *isnan0, *isnan1, *not_isnan0, *not_isnan1;
  BzlaNode *iszero0, *iszero1;
  BzlaNode *eq, *and, *and1, * or ;
  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  isnan0     = bzla_exp_fp_is_nan(bzla, e0);
  isnan1     = bzla_exp_fp_is_nan(bzla, e1);
  not_isnan0 = bzla_exp_bv_not(bzla, isnan0);
  not_isnan1 = bzla_exp_bv_not(bzla, isnan1);
  and        = bzla_exp_bv_and(bzla, not_isnan0, not_isnan1);

  eq      = bzla_exp_eq(bzla, e0, e1);
  iszero0 = bzla_exp_fp_is_zero(bzla, e0);
  iszero1 = bzla_exp_fp_is_zero(bzla, e1);
  and1    = bzla_exp_bv_and(bzla, iszero0, iszero1);
  or      = bzla_exp_bv_or(bzla, eq, and1);

  result = bzla_exp_bv_and(bzla, and, or);

  bzla_node_release(bzla, or);
  bzla_node_release(bzla, and1);
  bzla_node_release(bzla, iszero0);
  bzla_node_release(bzla, iszero1);
  bzla_node_release(bzla, eq);
  bzla_node_release(bzla, and);
  bzla_node_release(bzla, not_isnan0);
  bzla_node_release(bzla, not_isnan1);
  bzla_node_release(bzla, isnan0);
  bzla_node_release(bzla, isnan1);

  return result;
}

BzlaNode *
bzla_exp_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_LTE_NODE, e0, e1);
  else
    result = bzla_node_create_fp_lte(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_LT_NODE, e0, e1);
  else
    result = bzla_node_create_fp_lt(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_gte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e0, e1));

  return bzla_exp_fp_lte(bzla, e1, e0);
}

BzlaNode *
bzla_exp_fp_gt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);

  BzlaNode *result;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_fp_exp(bzla, e0, e1));

  result = bzla_exp_fp_lt(bzla, e1, e0);
  return result;
}

BzlaNode *
bzla_exp_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_SQRT_NODE, e0, e1);
  else
    result = bzla_node_create_fp_sqrt(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_rti(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_FP_RTI_NODE, e0, e1);
  else
    result = bzla_node_create_fp_rti(bzla, e0, e1);
  return result;
}

BzlaNode *
bzla_exp_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_ternary_exp(bzla, BZLA_FP_ADD_NODE, e0, e1, e2);
  else
    result = bzla_node_create_fp_add(bzla, e0, e1, e2);
  return result;
}

BzlaNode *
bzla_exp_fp_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  BzlaNode *neg;
  BzlaNode *result;
  e0     = bzla_simplify_exp(bzla, e0);
  e1     = bzla_simplify_exp(bzla, e1);
  e2     = bzla_simplify_exp(bzla, e2);
  neg    = bzla_exp_fp_neg(bzla, e2);
  result = bzla_exp_fp_add(bzla, e0, e1, neg);
  bzla_node_release(bzla, neg);
  return result;
}

BzlaNode *
bzla_exp_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_ternary_exp(bzla, BZLA_FP_MUL_NODE, e0, e1, e2);
  else
    result = bzla_node_create_fp_mul(bzla, e0, e1, e2);
  return result;
}

BzlaNode *
bzla_exp_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_ternary_exp(bzla, BZLA_FP_DIV_NODE, e0, e1, e2);
  else
    result = bzla_node_create_fp_div(bzla, e0, e1, e2);
  return result;
}

BzlaNode *
bzla_exp_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  e3 = bzla_simplify_exp(bzla, e3);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_fp_fma_exp(bzla, e0, e1, e2, e3);
  else
    result = bzla_node_create_fp_fma(bzla, e0, e1, e2, e3);
  return result;
}

BzlaNode *
bzla_exp_fp_to_sbv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  return bzla_node_create_fp_to_sbv(bzla, e0, e1, sort);
}

BzlaNode *
bzla_exp_fp_to_ubv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  return bzla_node_create_fp_to_ubv(bzla, e0, e1, sort);
}

BzlaNode *
bzla_exp_fp_to_fp_from_bv(Bzla *bzla, BzlaNode *node, BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla_node_bv_get_width(bzla, node)
         == bzla_sort_fp_get_bv_width(bzla, sort));
  BzlaNode *result;
  node = bzla_simplify_exp(bzla, node);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
  {
    result =
        bzla_rewrite_unary_to_fp_exp(bzla, BZLA_FP_TO_FP_BV_NODE, node, sort);
  }
  else
  {
    result = bzla_node_create_fp_to_fp_from_bv(bzla, node, sort);
  }
  return result;
}

BzlaNode *
bzla_exp_fp_to_fp_from_fp(Bzla *bzla,
                          BzlaNode *e0,
                          BzlaNode *e1,
                          BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
  {
    result = bzla_rewrite_binary_to_fp_exp(
        bzla, BZLA_FP_TO_FP_FP_NODE, e0, e1, sort);
  }
  else
  {
    result = bzla_node_create_fp_to_fp_from_fp(bzla, e0, e1, sort);
  }
  return result;
}

BzlaNode *
bzla_exp_fp_to_fp_from_sbv(Bzla *bzla,
                           BzlaNode *e0,
                           BzlaNode *e1,
                           BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla_node_is_bv(bzla, e1));

  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  if (bzla_node_bv_get_width(bzla, e1) == 1)
  {
    /* We need special handling for bit-vectors of size one since symFPU does
     * not allow conversions from signed bit-vectors of size one.  */
    BzlaNode *one     = bzla_exp_bv_one(bzla, 1);
    BzlaNode *cond    = bzla_exp_eq(bzla, e1, one);
    BzlaNode *fromubv = bzla_exp_fp_to_fp_from_ubv(bzla, e0, e1, sort);
    BzlaNode *neg     = bzla_exp_fp_neg(bzla, fromubv);
    result            = bzla_exp_cond(bzla, cond, neg, fromubv);
    bzla_node_release(bzla, neg);
    bzla_node_release(bzla, fromubv);
    bzla_node_release(bzla, cond);
    bzla_node_release(bzla, one);
  }
  else
  {
    if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    {
      result = bzla_rewrite_binary_to_fp_exp(
          bzla, BZLA_FP_TO_FP_SBV_NODE, e0, e1, sort);
    }
    else
    {
      result = bzla_node_create_fp_to_fp_from_sbv(bzla, e0, e1, sort);
    }
  }
  return result;
}

BzlaNode *
bzla_exp_fp_to_fp_from_ubv(Bzla *bzla,
                           BzlaNode *e0,
                           BzlaNode *e1,
                           BzlaSortId sort)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  BzlaNode *result;
  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
  {
    result = bzla_rewrite_binary_to_fp_exp(
        bzla, BZLA_FP_TO_FP_UBV_NODE, e0, e1, sort);
  }
  else
  {
    result = bzla_node_create_fp_to_fp_from_ubv(bzla, e0, e1, sort);
  }
  return result;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_read(Bzla *bzla, BzlaNode *e_array, BzlaNode *e_index)
{
  assert(bzla == bzla_node_real_addr(e_array)->bzla);
  assert(bzla == bzla_node_real_addr(e_index)->bzla);

  e_array = bzla_simplify_exp(bzla, e_array);
  e_index = bzla_simplify_exp(bzla, e_index);
  assert(bzla_dbg_precond_read_exp(bzla, e_array, e_index));
  return bzla_exp_apply_n(bzla, e_array, &e_index, 1);
}

BzlaNode *
bzla_exp_write(Bzla *bzla,
               BzlaNode *e_array,
               BzlaNode *e_index,
               BzlaNode *e_value)
{
  assert(bzla);
  assert(bzla_node_is_array(bzla_simplify_exp(bzla, e_array)));
  assert(bzla == bzla_node_real_addr(e_array)->bzla);
  assert(bzla == bzla_node_real_addr(e_index)->bzla);
  assert(bzla == bzla_node_real_addr(e_value)->bzla);

  e_array = bzla_simplify_exp(bzla, e_array);
  e_index = bzla_simplify_exp(bzla, e_index);
  e_value = bzla_simplify_exp(bzla, e_value);
  assert(bzla_dbg_precond_write_exp(bzla, e_array, e_index, e_value));

  BzlaNode *args = bzla_exp_args(bzla, &e_index, 1);
  BzlaNode *res  = bzla_exp_update(bzla, e_array, args, e_value);
  bzla_node_release(bzla, args);
  res->is_array = 1;
  return res;
}

/*------------------------------------------------------------------------*/

BzlaNode *
bzla_exp_fun(Bzla *bzla, BzlaNode *params[], uint32_t paramc, BzlaNode *exp)
{
  assert(bzla);
  assert(paramc > 0);
  assert(params);
  assert(exp);
  assert(bzla == bzla_node_real_addr(exp)->bzla);
  assert(!bzla_node_is_uf(exp));

  uint32_t i, j;
  BzlaNode *fun      = bzla_simplify_exp(bzla, exp);
  BzlaNode *prev_fun = 0;

  for (i = 1; i <= paramc; i++)
  {
    j = paramc - i;
    assert(params[j]);
    assert(bzla == bzla_node_real_addr(params[j])->bzla);
    assert(bzla_node_is_param(params[j]));
    fun = bzla_exp_lambda(bzla, params[j], fun);
    if (prev_fun) bzla_node_release(bzla, prev_fun);
    prev_fun = fun;
  }

  return fun;
}

BzlaNode *
bzla_exp_apply(Bzla *bzla, BzlaNode *fun, BzlaNode *args)
{
  assert(bzla);
  assert(fun);
  assert(args);
  assert(bzla == bzla_node_real_addr(fun)->bzla);
  assert(bzla == bzla_node_real_addr(args)->bzla);

  fun  = bzla_simplify_exp(bzla, fun);
  args = bzla_simplify_exp(bzla, args);
  assert(bzla_node_is_fun(fun));
  assert(bzla_node_is_args(args));

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    return bzla_rewrite_binary_exp(bzla, BZLA_APPLY_NODE, fun, args);

  return bzla_node_create_apply(bzla, fun, args);
}

BzlaNode *
bzla_exp_apply_n(Bzla *bzla, BzlaNode *fun, BzlaNode *args[], uint32_t argc)
{
  assert(bzla);
  assert(argc > 0);
  assert(args);
  assert(fun);

  BzlaNode *exp, *_args;

  _args = bzla_exp_args(bzla, args, argc);
  fun   = bzla_simplify_exp(bzla, fun);
  _args = bzla_simplify_exp(bzla, _args);

  exp = bzla_exp_apply(bzla, fun, _args);
  bzla_node_release(bzla, _args);

  return exp;
}

BzlaNode *
bzla_exp_args(Bzla *bzla, BzlaNode *args[], uint32_t argc)
{
  return bzla_node_create_args(bzla, args, argc);
}

BzlaNode *
bzla_exp_update(Bzla *bzla, BzlaNode *fun, BzlaNode *args, BzlaNode *value)
{
  return bzla_node_create_update(bzla, fun, args, value);
}

BzlaNode *
bzla_exp_lambda(Bzla *bzla, BzlaNode *e_param, BzlaNode *e_exp)
{
  assert(bzla);
  assert(bzla_node_is_regular(e_param));
  assert(bzla == e_param->bzla);
  assert(bzla_node_is_param(e_param));
  assert(e_exp);
  assert(bzla == bzla_node_real_addr(e_exp)->bzla);

  e_param = bzla_simplify_exp(bzla, e_param);
  e_exp   = bzla_simplify_exp(bzla, e_exp);

  BzlaNode *result;
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    result = bzla_rewrite_binary_exp(bzla, BZLA_LAMBDA_NODE, e_param, e_exp);
  else
    result = bzla_node_create_lambda(bzla, e_param, e_exp);
  assert(bzla_node_is_fun(result));
  return result;
}

BzlaNode *
bzla_exp_lambda_write(Bzla *bzla,
                      BzlaNode *e_array,
                      BzlaNode *e_index,
                      BzlaNode *e_value)
{
  BzlaNode *param, *e_cond, *e_if, *e_else, *bvcond, *args;
  BzlaLambdaNode *lambda;
  BzlaPtrHashBucket *b;

  param  = bzla_exp_param(bzla, bzla_node_get_sort_id(e_index), 0);
  e_cond = bzla_exp_eq(bzla, param, e_index);
  e_if   = bzla_node_copy(bzla, e_value);
  e_else = bzla_exp_read(bzla, e_array, param);
  bvcond = bzla_exp_cond(bzla, e_cond, e_if, e_else);
  lambda = (BzlaLambdaNode *) bzla_exp_lambda(bzla, param, bvcond);
  if (!lambda->static_rho)
  {
    lambda->static_rho =
        bzla_hashptr_table_new(bzla->mm,
                               (BzlaHashPtr) bzla_node_hash_by_id,
                               (BzlaCmpPtr) bzla_node_compare_by_id);
    args           = bzla_exp_args(bzla, &e_index, 1);
    b              = bzla_hashptr_table_add(lambda->static_rho, args);
    b->data.as_ptr = bzla_node_copy(bzla, e_value);
  }
  bzla_node_release(bzla, e_if);
  bzla_node_release(bzla, e_else);
  bzla_node_release(bzla, e_cond);
  bzla_node_release(bzla, bvcond);
  bzla_node_release(bzla, param);

  lambda->is_array = 1;
  return (BzlaNode *) lambda;
}

/*------------------------------------------------------------------------*/

static BzlaNode *
quantifier_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *param, BzlaNode *body)
{
  assert(bzla);
  assert(kind == BZLA_FORALL_NODE || kind == BZLA_EXISTS_NODE);
  assert(param);

  param = bzla_simplify_exp(bzla, param);
  body  = bzla_simplify_exp(bzla, body);

  assert(bzla_node_is_regular(param));
  assert(bzla_node_is_param(param));
  assert(body);
  assert(bzla_sort_is_bool(bzla, bzla_node_real_addr(body)->sort_id));
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0)
    return bzla_rewrite_binary_exp(bzla, kind, param, body);
  return bzla_node_create_quantifier(bzla, kind, param, body);
}

static BzlaNode *
quantifier_n_exp(Bzla *bzla,
                 BzlaNodeKind kind,
                 BzlaNode *params[],
                 uint32_t n,
                 BzlaNode *body)
{
  assert(bzla);
  assert(kind == BZLA_FORALL_NODE || kind == BZLA_EXISTS_NODE);
  assert(params);
  assert(n > 0);
  assert(body);
  assert(bzla == bzla_node_real_addr(body)->bzla);

  uint32_t i, j;
  BzlaNode *res, *tmp;

  res = bzla_node_copy(bzla, body);
  for (j = 1, i = n - 1; j <= n; j++, i--)
  {
    assert(params[i]);
    assert(bzla == bzla_node_real_addr(params[i])->bzla);
    assert(bzla_node_is_param(params[i]));
    tmp = quantifier_exp(bzla, kind, params[i], res);
    bzla_node_release(bzla, res);
    res = tmp;
  }
  return res;
}

BzlaNode *
bzla_exp_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  return quantifier_exp(bzla, BZLA_FORALL_NODE, param, body);
}

BzlaNode *
bzla_exp_forall_n(Bzla *bzla, BzlaNode *params[], uint32_t n, BzlaNode *body)
{
  return quantifier_n_exp(bzla, BZLA_FORALL_NODE, params, n, body);
}

BzlaNode *
bzla_exp_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  return bzla_node_invert(
      quantifier_exp(bzla, BZLA_FORALL_NODE, param, bzla_node_invert(body)));
}

BzlaNode *
bzla_exp_exists_n(Bzla *bzla, BzlaNode *params[], uint32_t n, BzlaNode *body)
{
  return bzla_node_invert(quantifier_n_exp(
      bzla, BZLA_FORALL_NODE, params, n, bzla_node_invert(body)));
}
