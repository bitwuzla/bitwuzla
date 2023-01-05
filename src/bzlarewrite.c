/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlarewrite.h"

#include <assert.h>

#include "bzlabeta.h"
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzladbg.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlalog.h"
#include "utils/bzlahashint.h"
#include "utils/bzlahashptr.h"
#include "utils/bzlamem.h"
#include "utils/bzlanodeiter.h"
#include "utils/bzlautil.h"

// TODO: mul: power of 2 optimizations

/* TODO: lots of word level simplifications:
 * a[7:4] == b[7:4] && a[3:0] == b[3:0] <=> a == b
 * {a,b} == {c,d} with |a|=|c| <=> a == c && b == d
 * ...
 */
/* TODO a + 2 * a <=> 3 * a <=> and see below */
/* TODO strength reduction: a * 2 == a << 1 (really ?) */
/* TODO strength reduction: a * 3 == (a << 1) + a (really ?) */
/* TODO strength reduction: a / 2 == (a >> 1) (yes!) */
/* TODO strength reduction: a / 3 =>  higher bits zero (check!) */
/* TODO MAX-1 < a <=> a == MAX */

/* TODO (x < ~x) <=> !msb(x) */
/* TODO (~x < x) <=> msb(x) */

/* TODO to support GAUSS bubble up odd terms:
 * (2 * a + 3 * y) + 4 * x => 3 * y + (2 * a + 4 * x)
 * or alternatively normalize arithmetic terms/polynomials
 * or simply always replace by equation.
 */

/* TODO simplify (c * x + 2 * y) + x == 5 at GAUSS application
 * by first (c + 1) * x + 2 * y == 5 and then check whether 'c'
 * is even.
 */

/* TODO Howto handle 2 * x == 4 && 4 * x + 8 * y == 0 ?
 * Maybe: x[30:0] == 2 && 4 * {x[31],2[30:0]} + 8 * y == 0?
 * Then: x[30:0] == 2 && 8[31:0] + 8 *y == 0?
 * Then: x[30:0] = 2 && 8 * y = -8
 * Finally:  x[30:0] = 2 && y[29:0] = -1
 * etc.
 */

/* recursive rewriting bound */
#define BZLA_REC_RW_BOUND (1 << 12)

/* iterative rewriting bounds */
#define BZLA_WRITE_CHAIN_NODE_RW_BOUND (1 << 5)
#define BZLA_READ_OVER_WRITE_DOWN_PROPAGATION_LIMIT (1 << 11)
#define BZLA_APPLY_PROPAGATION_LIMIT (1 << 13)

/* other rewriting bounds */
#define BZLA_FIND_AND_NODE_CONTRADICTION_LIMIT (1 << 4)

#define BZLA_INC_REC_RW_CALL(bzla)                             \
  do                                                           \
  {                                                            \
    (bzla)->rec_rw_calls++;                                    \
    if ((bzla)->rec_rw_calls > (bzla)->stats.max_rec_rw_calls) \
      (bzla)->stats.max_rec_rw_calls = (bzla)->rec_rw_calls;   \
  } while (0)

#define BZLA_DEC_REC_RW_CALL(bzla)    \
  do                                  \
  {                                   \
    assert((bzla)->rec_rw_calls > 0); \
    (bzla)->rec_rw_calls--;           \
  } while (0)

// TODO: special_const_binary rewriting may return 0, hence the check if
//       (result), may be obsolete if special_const_binary will be split
#ifndef NDEBUG
#define ADD_RW_RULE(rw_rule, ...)                                             \
  if (applies_##rw_rule(bzla, __VA_ARGS__))                                   \
  {                                                                           \
    assert(!result);                                                          \
    result = apply_##rw_rule(bzla, __VA_ARGS__);                              \
    if (result)                                                               \
    {                                                                         \
      if (bzla->stats.rw_rules_applied)                                       \
      {                                                                       \
        BzlaPtrHashBucket *b =                                                \
            bzla_hashptr_table_get(bzla->stats.rw_rules_applied, #rw_rule);   \
        if (!b)                                                               \
          b = bzla_hashptr_table_add(bzla->stats.rw_rules_applied, #rw_rule); \
        b->data.as_int += 1;                                                  \
      }                                                                       \
      goto DONE;                                                              \
    }                                                                         \
  }
#else
#define ADD_RW_RULE(rw_rule, ...)                \
  if (applies_##rw_rule(bzla, __VA_ARGS__))      \
  {                                              \
    assert(!result);                             \
    result = apply_##rw_rule(bzla, __VA_ARGS__); \
    if (result) goto DONE;                       \
  }
#endif
//{fprintf (stderr, "apply: %s (%s)\n", #rw_rule, __FUNCTION__);

#define BZLA_START_REWRITE_TIMER \
  double timer_start = (bzla->rec_rw_calls == 0 ? bzla_util_time_stamp() : 0)

#define BZLA_STOP_REWRITE_TIMER                                 \
  if (bzla->rec_rw_calls == 0)                                  \
  {                                                             \
    bzla->time.rewrite += bzla_util_time_stamp() - timer_start; \
  }

/* -------------------------------------------------------------------------- */
/* rewrite cache */

static BzlaNode *
check_rw_cache(Bzla *bzla,
               BzlaNodeKind kind,
               int32_t id0,
               int32_t id1,
               int32_t id2,
               int32_t id3)
{
  BzlaNode *result = 0;

  int32_t cached_result_id =
      bzla_rw_cache_get(bzla->rw_cache, kind, id0, id1, id2, id3);
  if (cached_result_id)
  {
    result = bzla_node_get_by_id(bzla, cached_result_id);
    if (result)
    {
      bzla->rw_cache->num_get++;
      result = bzla_node_copy(bzla, bzla_node_get_simplified(bzla, result));
    }
  }
  return result;
}

/* -------------------------------------------------------------------------- */
/* util functions */

static bool
is_const_zero_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  exp = bzla_simplify_exp(bzla, exp);
  if (!bzla_node_is_bv_const(exp)) return false;
  return bzla_bv_is_zero(bzla_node_bv_const_get_bits(exp));
}

#if 0
static bool
is_const_ones_exp (Bzla * bzla, BzlaNode * exp)
{
  assert (bzla);
  assert (exp);

  exp = bzla_simplify_exp (bzla, exp);
  if (!bzla_node_is_bv_const (exp)) return false;

  return bzla_is_ones_const (bzla_node_bv_const_get_bits (exp));
}
#endif

static bool
is_bv_const_zero_or_ones_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  bool result;
  BzlaBitVector *bits;

  exp = bzla_simplify_exp(bzla, exp);

  if (!bzla_node_is_bv_const(exp)) return false;

  bits   = bzla_node_bv_const_get_bits(exp);
  result = bzla_bv_is_zero(bits) || bzla_bv_is_ones(bits);

  return result;
}

static bool
is_odd_bv_const_exp(BzlaNode *exp)
{
  BzlaBitVector *bits;

  if (!bzla_node_is_bv_const(exp)) return false;
  if (bzla_node_is_inverted(exp)) return false;

  bits = bzla_node_bv_const_get_bits(exp);
  return bzla_bv_get_bit(bits, 0) == 1;
}

static bool
is_xor_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);

  BzlaNode *e0, *e1, *e0_0, *e0_1, *e1_0, *e1_1;

  exp = bzla_simplify_exp(bzla, exp);
  (void) bzla;

  if (bzla_node_real_addr(exp)->kind != BZLA_BV_AND_NODE) return false;

  e0 = bzla_node_real_addr(exp)->e[0];
  if (!(bzla_node_is_inverted(e0)
        && bzla_node_real_addr(e0)->kind == BZLA_BV_AND_NODE))
    return false;

  e1 = bzla_node_real_addr(exp)->e[1];
  if (!(bzla_node_is_inverted(e1)
        && bzla_node_real_addr(e1)->kind == BZLA_BV_AND_NODE))
    return false;

  e0_0 = bzla_node_real_addr(e0)->e[0];
  e0_1 = bzla_node_real_addr(e0)->e[1];
  e1_0 = bzla_node_real_addr(e1)->e[0];
  e1_1 = bzla_node_real_addr(e1)->e[1];

  /* we assume that the children of commutative operators are sorted by id */
  /* are children of e0 the same children as of e1 (ignoring sign) ? */
  /* if not we terminate with false */
  if (bzla_node_real_addr(e0_0) != bzla_node_real_addr(e1_0)) return false;
  if (bzla_node_real_addr(e0_1) != bzla_node_real_addr(e1_1)) return false;

  /* we check for two cases */
  /* first case: !(!a && !b) && !(a && b) */
  if (!bzla_node_is_inverted(exp))
  {
    if (bzla_node_is_inverted(e0_0) == bzla_node_is_inverted(e0_1)
        && bzla_node_is_inverted(e1_0) == bzla_node_is_inverted(e1_1)
        && bzla_node_is_inverted(e0_0) != bzla_node_is_inverted(e1_0))
      return true;
  }
  /* second case: !((!a && b) && !(a && !b)) */
  else
  {
    if (bzla_node_is_inverted(e0_0) != bzla_node_is_inverted(e1_0)
        && bzla_node_is_inverted(e0_1) != bzla_node_is_inverted(e1_1)
        && bzla_node_is_inverted(e0_0) != bzla_node_is_inverted(e0_1))
      return true;
  }
  return false;
}

static bool
is_xnor_exp(Bzla *bzla, BzlaNode *exp)
{
  assert(bzla);
  assert(exp);
  exp = bzla_simplify_exp(bzla, exp);
  return is_xor_exp(bzla, bzla_node_invert(exp));
}

static bool
slice_simplifiable(BzlaNode *exp)
{
  exp = bzla_node_real_addr(exp);
  return bzla_node_is_bv_var(exp) || bzla_node_is_bv_const(exp)
         || bzla_node_is_bv_slice(exp);
}

static bool
is_always_unequal(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  BzlaNode *e0_const = 0, *e0_node = 0, *e1_const = 0, *e1_node = 0;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla);
  assert(e0);
  assert(e1);
  /* we need this so that a + 0 is rewritten to a,
   * and constants are normalized (all inverted constants are odd) */
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  if (!real_e0 || !real_e1) return 0;

  if (bzla_node_is_fun(real_e0))
  {
    assert(bzla_node_is_fun(real_e1));
    return false;
  }

  assert(!bzla_node_is_fun(real_e1));

  if (e0 == bzla_node_invert(e1)) return true;

  if (bzla_node_is_bv_const(real_e0) && bzla_node_is_bv_const(real_e1)
      && e0 != e1)
    return true;

  if (bzla_node_is_bv_add(real_e0))
  {
    if (bzla_node_is_bv_const(real_e0->e[0]))
    {
      e0_const = real_e0->e[0];
      e0_node  = real_e0->e[1];
    }
    else if (bzla_node_is_bv_const(real_e0->e[1]))
    {
      e0_const = real_e0->e[1];
      e0_node  = real_e0->e[0];
    }

    if (e0_const && !is_const_zero_exp(bzla, e0_const)
        && bzla_node_cond_invert(e0, e0_node) == e1)
      return true;
  }

  if (bzla_node_is_bv_add(real_e1))
  {
    if (bzla_node_is_bv_const(real_e1->e[0]))
    {
      e1_const = real_e1->e[0];
      e1_node  = real_e1->e[1];
    }
    else if (bzla_node_is_bv_const(real_e1->e[1]))
    {
      e1_const = real_e1->e[1];
      e1_node  = real_e1->e[0];
    }

    if (e1_const && !is_const_zero_exp(bzla, e1_const)
        && bzla_node_cond_invert(e1, e1_node) == e1)
      return true;
  }

  if (e0_const && e1_const
      && bzla_node_is_inverted(e0) == bzla_node_is_inverted(e1))
  {
    return e0_node == e1_node && e0_const != e1_const;
  }

  return false;
}

static int32_t
cmp_node_id(const void *p, const void *q)
{
  BzlaNode *a = *(BzlaNode **) p;
  BzlaNode *b = *(BzlaNode **) q;
  return bzla_node_get_id(a) - bzla_node_get_id(b);
}

static bool
find_and_contradiction_exp(
    Bzla *bzla, BzlaNode *exp, BzlaNode *e0, BzlaNode *e1, uint32_t *calls)
{
  assert(bzla);
  assert(exp);
  assert(e0);
  assert(e1);
  assert(calls);
  (void) bzla;

  if (*calls >= BZLA_FIND_AND_NODE_CONTRADICTION_LIMIT) return false;

  if (!bzla_node_is_inverted(exp) && exp->kind == BZLA_BV_AND_NODE)
  {
    if (exp->e[0] == bzla_node_invert(e0) || exp->e[0] == bzla_node_invert(e1)
        || exp->e[1] == bzla_node_invert(e0)
        || exp->e[1] == bzla_node_invert(e1))
      return true;
    *calls += 1;
    return find_and_contradiction_exp(bzla, exp->e[0], e0, e1, calls)
           || find_and_contradiction_exp(bzla, exp->e[1], e0, e1, calls);
  }
  return false;
}

static bool
is_concat_simplifiable(BzlaNode *exp)
{
  return bzla_node_is_bv_var(exp) || bzla_node_is_bv_const(exp);
}

static bool
is_write_exp(BzlaNode *exp,
             BzlaNode **array,
             BzlaNode **index,
             BzlaNode **value)
{
  assert(exp);
  assert(bzla_node_is_regular(exp));

  BzlaNode *param, *body, *eq, *app;

  if (!bzla_node_is_lambda(exp) || bzla_node_fun_get_arity(exp->bzla, exp) > 1)
    return false;

  param = exp->e[0];
  body  = bzla_node_binder_get_body(exp);

  if (bzla_node_is_inverted(body) || !bzla_node_is_bv_cond(body)) return false;

  /* check condition */
  eq = body->e[0];
  if (bzla_node_is_inverted(eq) || !bzla_node_is_bv_eq(eq) || !eq->parameterized
      || (eq->e[0] != param && eq->e[1] != param))
    return false;

  /* check value */
  if (bzla_node_real_addr(body->e[1])->parameterized) return false;

  /* check apply on unmodified array */
  app = body->e[2];
  if (bzla_node_is_inverted(app) || !bzla_node_is_apply(app)
      || bzla_node_args_get_arity(app->bzla, app->e[1]) > 1
      || app->e[1]->e[0] != param)
    return false;

  if (array) *array = app->e[0];
  if (index) *index = eq->e[1] == param ? eq->e[0] : eq->e[1];
  if (value) *value = body->e[1];
  return true;
}

static bool
is_true_cond(BzlaNode *cond)
{
  assert(cond);
  assert(bzla_node_is_bv_const(cond));
  return bzla_bv_is_true(bzla_node_bv_const_get_bits(cond));
}

#if 0
static bool
is_bit_mask (BzlaNode * exp, uint32_t * upper, uint32_t * lower)
{
  uint32_t i, len, inv, bit;
  int32_t first, last;
  BzlaBitVector *bits;
  BzlaNode *real_exp;

  real_exp = bzla_node_real_addr (exp);

  *upper = 0; *lower = 0;
  first = -1; last = -1;

  if (!bzla_node_is_bv_const (real_exp))
    return false;

  bits = bzla_node_bv_const_get_bits (real_exp);
  inv = bzla_node_is_inverted (exp);
  len = bzla_node_bv_get_width (real_exp->bzla, real_exp);
  for (i = 0; i < len; i++)
    {
      bit = bzla_bv_get_bit (bits, i);
      if (inv) bit ^= 1;

      if (bit && first == -1)
	first = i;
      else if (!bit && first > -1 && last == -1)
	last = i - 1;

      if (bit && last > -1)
	return false;
    }
  if (last == -1)
    last = len - 1;

  *upper = last;
  *lower = first;
  return true;
}
#endif

static bool
is_urem_exp(Bzla *bzla,
            BzlaNode *e0,
            BzlaNode *e1,
            BzlaNode **res_e0,
            BzlaNode **res_e1)
{
  BzlaNode *mul, *udiv, *x, *y;

  if (bzla_node_bv_is_neg(bzla, e0, &mul))
    x = e1;
  else if (bzla_node_bv_is_neg(bzla, e1, &mul))
    x = e0;
  else
    return false;

  if (bzla_node_is_inverted(mul) || !bzla_node_is_bv_mul(mul)) return false;

  if (!bzla_node_is_inverted(mul->e[0]) && bzla_node_is_bv_udiv(mul->e[0]))
  {
    udiv = mul->e[0];
    y    = mul->e[0];
  }
  else if (!bzla_node_is_inverted(mul->e[1]) && bzla_node_is_bv_udiv(mul->e[1]))
  {
    udiv = mul->e[1];
    y    = mul->e[0];
  }
  else
    return false;

  if (udiv->e[0] == x && udiv->e[1] == y)
  {
    if (res_e0) *res_e0 = x;
    if (res_e1) *res_e1 = y;
    return true;
  }
  return false;
}

/* -------------------------------------------------------------------------- */

static BzlaNode *rewrite_bv_slice_exp(Bzla *, BzlaNode *, uint32_t, uint32_t);
static BzlaNode *rewrite_eq_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_ult_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_and_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_add_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_mul_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_udiv_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_urem_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_concat_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_sll_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_slt_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_bv_srl_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_abs_exp(Bzla *, BzlaNode *);
static BzlaNode *rewrite_fp_tester_exp(Bzla *, BzlaNodeKind kind, BzlaNode *);
static BzlaNode *rewrite_fp_neg_exp(Bzla *, BzlaNode *);
static BzlaNode *rewrite_fp_min_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_max_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_lte_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_lt_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_rem_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_sqrt_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_rti_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_add_exp(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_mul_exp(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_div_exp(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_fp_to_fp_from_bv_exp(Bzla *bzla,
                                              BzlaNode *e0,
                                              BzlaSortId sort);
static BzlaNode *rewrite_fp_to_fp_from_fp_exp(Bzla *bzla,
                                              BzlaNode *e0,
                                              BzlaNode *e1,
                                              BzlaSortId sort);
static BzlaNode *rewrite_fp_to_fp_from_sbv_exp(Bzla *bzla,
                                               BzlaNode *e0,
                                               BzlaNode *e1,
                                               BzlaSortId sort);
static BzlaNode *rewrite_fp_to_fp_from_ubv_exp(Bzla *bzla,
                                               BzlaNode *e0,
                                               BzlaNode *e1,
                                               BzlaSortId sort);
static BzlaNode *rewrite_apply_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_lambda_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_forall_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_exists_exp(Bzla *, BzlaNode *, BzlaNode *);
static BzlaNode *rewrite_cond_exp(Bzla *, BzlaNode *, BzlaNode *, BzlaNode *);

/* -------------------------------------------------------------------------- */
/* const term rewriting                                                       */
/* -------------------------------------------------------------------------- */

/*
 * match:  binary bv op with two constants
 * result: bit-vector constant
 */
static inline bool
applies_const_binary_bv_exp(Bzla *bzla,
                            BzlaNodeKind kind,
                            BzlaNode *e0,
                            BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_bv_const(e0) && bzla_node_is_bv_const(e1);
}

static inline BzlaNode *
apply_const_binary_bv_exp(Bzla *bzla,
                          BzlaNodeKind kind,
                          BzlaNode *e0,
                          BzlaNode *e1)
{
  assert(applies_const_binary_bv_exp(bzla, kind, e0, e1));

  bool invert_b0, invert_b1;
  BzlaBitVector *b0, *b1, *bresult;
  BzlaMemMgr *mm;
  BzlaNode *result, *real_e0, *real_e1;

  mm      = bzla->mm;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  invert_b0 = bzla_node_is_inverted(e0);
  invert_b1 = bzla_node_is_inverted(e1);
  b0        = bzla_node_bv_const_get_bits(real_e0);
  b1        = bzla_node_bv_const_get_bits(real_e1);
  if (invert_b0) b0 = bzla_bv_not(mm, b0);
  if (invert_b1) b1 = bzla_bv_not(mm, b1);

  switch (kind)
  {
    case BZLA_BV_AND_NODE: bresult = bzla_bv_and(mm, b0, b1); break;
    case BZLA_BV_EQ_NODE: bresult = bzla_bv_eq(mm, b0, b1); break;
    case BZLA_BV_ADD_NODE: bresult = bzla_bv_add(mm, b0, b1); break;
    case BZLA_BV_MUL_NODE: bresult = bzla_bv_mul(mm, b0, b1); break;
    case BZLA_BV_ULT_NODE: bresult = bzla_bv_ult(mm, b0, b1); break;
    case BZLA_BV_UDIV_NODE: bresult = bzla_bv_udiv(mm, b0, b1); break;
    case BZLA_BV_UREM_NODE: bresult = bzla_bv_urem(mm, b0, b1); break;
    case BZLA_BV_SLL_NODE: bresult = bzla_bv_sll(mm, b0, b1); break;
    case BZLA_BV_SLT_NODE: bresult = bzla_bv_slt(mm, b0, b1); break;
    case BZLA_BV_SRL_NODE: bresult = bzla_bv_srl(mm, b0, b1); break;
    default:
      assert(kind == BZLA_BV_CONCAT_NODE);
      bresult = bzla_bv_concat(mm, b0, b1);
      break;
  }
  if (invert_b0) bzla_bv_free(mm, b0);
  if (invert_b1) bzla_bv_free(mm, b1);
  result = bzla_exp_bv_const(bzla, bresult);
  bzla_bv_free(mm, bresult);
  return result;
}

/*
 * match:  unary fp op with one floating-point constant
 * result: floating-point constant
 */
static inline bool
applies_const_unary_fp_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_fp_const(e0);
}

static inline BzlaNode *
apply_const_unary_fp_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  assert(applies_const_unary_fp_exp(bzla, kind, e0));
  assert(bzla_node_is_regular(e0));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_ABS_NODE: fpres = bzla_fp_abs(bzla, bzla_fp_get_fp(e0)); break;
    default:
      assert(kind == BZLA_FP_NEG_NODE);
      fpres = bzla_fp_neg(bzla, bzla_fp_get_fp(e0));
  }
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  unary tester fp op with one floating-point constant
 * result: bool constant
 */
static inline bool
applies_const_fp_tester_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_fp_const(e0);
}

static inline BzlaNode *
apply_const_fp_tester_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  assert(applies_const_fp_tester_exp(bzla, kind, e0));
  assert(bzla_node_is_regular(e0));

  bool bres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_IS_INF_NODE:
      bres = bzla_fp_is_inf(bzla, bzla_fp_get_fp(e0));
      break;
    case BZLA_FP_IS_NAN_NODE:
      bres = bzla_fp_is_nan(bzla, bzla_fp_get_fp(e0));
      break;
    case BZLA_FP_IS_NEG_NODE:
      bres = bzla_fp_is_neg(bzla, bzla_fp_get_fp(e0));
      break;
    case BZLA_FP_IS_POS_NODE:
      bres = bzla_fp_is_pos(bzla, bzla_fp_get_fp(e0));
      break;
    case BZLA_FP_IS_NORM_NODE:
      bres = bzla_fp_is_normal(bzla, bzla_fp_get_fp(e0));
      break;
    case BZLA_FP_IS_SUBNORM_NODE:
      bres = bzla_fp_is_subnormal(bzla, bzla_fp_get_fp(e0));
      break;
    default:
      assert(kind == BZLA_FP_IS_ZERO_NODE);
      bres = bzla_fp_is_zero(bzla, bzla_fp_get_fp(e0));
  }
  result = bres ? bzla_exp_true(bzla) : bzla_exp_false(bzla);
  return result;
}

/*
 * match:  unary fp to_fp from bv op with one bit-vector constant
 * result: floating-point constant
 */
static inline bool
applies_const_fp_to_fp_from_bv_exp(Bzla *bzla, BzlaNode *e0, BzlaSortId sort)
{
  (void) bzla;
  (void) sort;
  return bzla_node_is_bv_const(e0);
}

static inline BzlaNode *
apply_const_fp_to_fp_from_bv_exp(Bzla *bzla, BzlaNode *e0, BzlaSortId sort)
{
  assert(applies_const_fp_to_fp_from_bv_exp(bzla, e0, sort));

  BzlaFloatingPoint *fpres;
  BzlaBitVector *bits;
  BzlaNode *result;

  bits   = bzla_node_bv_const_get_bits(e0);
  fpres  = bzla_fp_from_bv(bzla, sort, bits);
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  fp to_fp from fp op with rounding mode and floating-point constant
 * result: floating-point constant
 */
static inline bool
applies_const_fp_to_fp_from_fp_exp(Bzla *bzla,
                                   BzlaNode *e0,
                                   BzlaNode *e1,
                                   BzlaSortId sort)
{
  (void) bzla;
  (void) sort;
  return bzla_node_is_rm_const(e0) && bzla_node_is_fp_const(e1);
}

static inline BzlaNode *
apply_const_fp_to_fp_from_fp_exp(Bzla *bzla,
                                 BzlaNode *e0,
                                 BzlaNode *e1,
                                 BzlaSortId sort)
{
  assert(applies_const_fp_to_fp_from_fp_exp(bzla, e0, e1, sort));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  fpres = bzla_fp_convert(
      bzla, sort, bzla_node_rm_const_get_rm(e0), bzla_fp_get_fp(e1));
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  fp to_fp from signed bit-vector (machine integer) op with rounding
 *         mode and bit-vector constant
 * result: floating-point constant
 */
static inline bool
applies_const_fp_to_fp_from_sbv_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  (void) bzla;
  (void) kind;
  (void) sort;
  return bzla_node_is_rm_const(e0) && bzla_node_is_bv_const(e1);
}

static inline BzlaNode *
apply_const_fp_to_fp_from_sbv_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  assert(applies_const_fp_to_fp_from_sbv_exp(bzla, kind, e0, e1, sort));

  BzlaFloatingPoint *fpres;
  BzlaBitVector *bits;
  BzlaNode *result;

  bits = bzla_node_bv_const_get_bits(e1);
  if (kind == BZLA_FP_TO_FP_SBV_NODE)
  {
    fpres = bzla_fp_convert_from_sbv(
        bzla, sort, bzla_node_rm_const_get_rm(e0), bits);
  }
  else
  {
    assert(kind == BZLA_FP_TO_FP_UBV_NODE);
    fpres = bzla_fp_convert_from_ubv(
        bzla, sort, bzla_node_rm_const_get_rm(e0), bits);
  }
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  binary fp op with two floating-point constant
 * result: bool constant
 */
static inline bool
applies_const_binary_fp_bool_exp(Bzla *bzla,
                                 BzlaNodeKind kind,
                                 BzlaNode *e0,
                                 BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_fp_const(e0) && bzla_node_is_fp_const(e1);
}

static inline BzlaNode *
apply_const_binary_fp_bool_exp(Bzla *bzla,
                               BzlaNodeKind kind,
                               BzlaNode *e0,
                               BzlaNode *e1)
{
  assert(applies_const_binary_fp_bool_exp(bzla, kind, e0, e1));
  assert(bzla_node_is_regular(e0));

  bool bres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_LTE_NODE:
      bres = bzla_fp_lte(bzla, bzla_fp_get_fp(e0), bzla_fp_get_fp(e1));
      break;
    case BZLA_FP_LT_NODE:
      bres = bzla_fp_lt(bzla, bzla_fp_get_fp(e0), bzla_fp_get_fp(e1));
      break;
    default:
      assert(kind == BZLA_FP_EQ_NODE);
      bres = bzla_fp_eq(bzla, bzla_fp_get_fp(e0), bzla_fp_get_fp(e1));
  }
  result = bres ? bzla_exp_true(bzla) : bzla_exp_false(bzla);
  return result;
}

/*
 * match:  binary fp op with two floating-point constants
 * result: floating-point constant
 */
static inline bool
applies_const_binary_fp_rm_exp(Bzla *bzla,
                               BzlaNodeKind kind,
                               BzlaNode *e0,
                               BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_rm_const(e0) && bzla_node_is_fp_const(e1);
}

static inline BzlaNode *
apply_const_binary_fp_rm_exp(Bzla *bzla,
                             BzlaNodeKind kind,
                             BzlaNode *e0,
                             BzlaNode *e1)
{
  assert(applies_const_binary_fp_rm_exp(bzla, kind, e0, e1));
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_SQRT_NODE:
      fpres =
          bzla_fp_sqrt(bzla, bzla_node_rm_const_get_rm(e0), bzla_fp_get_fp(e1));
      break;
    default:
      assert(kind == BZLA_FP_RTI_NODE);
      fpres =
          bzla_fp_rti(bzla, bzla_node_rm_const_get_rm(e0), bzla_fp_get_fp(e1));
  }
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  binary fp op with one rounding mode and one floating-point constant
 * result: floating-point constant
 */
static inline bool
applies_const_binary_fp_exp(Bzla *bzla,
                            BzlaNodeKind kind,
                            BzlaNode *e0,
                            BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_fp_const(e0) && bzla_node_is_fp_const(e1);
}

static inline BzlaNode *
apply_const_binary_fp_exp(Bzla *bzla,
                          BzlaNodeKind kind,
                          BzlaNode *e0,
                          BzlaNode *e1)
{
  assert(applies_const_binary_fp_exp(bzla, kind, e0, e1));
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_REM_NODE:
      fpres = bzla_fp_rem(bzla, bzla_fp_get_fp(e0), bzla_fp_get_fp(e1));
      break;
    default: assert(0);  // temporary
  }
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  ternary fp op with one rounding mode and two floating-point constants
 * result: floating-point constant
 */
static inline bool
applies_const_ternary_fp_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_rm_const(e0) && bzla_node_is_fp_const(e1)
         && bzla_node_is_fp_const(e2);
}

static inline BzlaNode *
apply_const_ternary_fp_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_const_ternary_fp_exp(bzla, kind, e0, e1, e2));
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));
  assert(bzla_node_is_regular(e2));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_ADD_NODE:
      fpres = bzla_fp_add(bzla,
                          bzla_node_rm_const_get_rm(e0),
                          bzla_fp_get_fp(e1),
                          bzla_fp_get_fp(e2));
      break;
    case BZLA_FP_MUL_NODE:
      fpres = bzla_fp_mul(bzla,
                          bzla_node_rm_const_get_rm(e0),
                          bzla_fp_get_fp(e1),
                          bzla_fp_get_fp(e2));
      break;
    default:
      assert(kind == BZLA_FP_DIV_NODE);
      fpres = bzla_fp_div(bzla,
                          bzla_node_rm_const_get_rm(e0),
                          bzla_fp_get_fp(e1),
                          bzla_fp_get_fp(e2));
  }
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  fp fma op with one rounding mode and three floating-point constants
 * result: floating-point constant
 */
static inline bool
applies_const_fp_fma_exp(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
  (void) bzla;
  return bzla_node_is_rm_const(e0) && bzla_node_is_fp_const(e1)
         && bzla_node_is_fp_const(e2) && bzla_node_is_fp_const(e3);
}

static inline BzlaNode *
apply_const_fp_fma_exp(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
  assert(applies_const_fp_fma_exp(bzla, e0, e1, e2, e3));
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));
  assert(bzla_node_is_regular(e2));
  assert(bzla_node_is_regular(e3));

  BzlaFloatingPoint *fpres;
  BzlaNode *result;

  fpres  = bzla_fp_fma(bzla,
                      bzla_node_rm_const_get_rm(e0),
                      bzla_fp_get_fp(e1),
                      bzla_fp_get_fp(e2),
                      bzla_fp_get_fp(e3));
  result = bzla_exp_fp_const_fp(bzla, fpres);
  bzla_fp_free(bzla, fpres);
  return result;
}

/*
 * match:  binary op with one constant
 * result: constant
 */
static inline bool
applies_special_const_lhs_binary_exp(Bzla *bzla,
                                     BzlaNodeKind kind,
                                     BzlaNode *e0,
                                     BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return bzla_node_is_bv_const(e0) && !bzla_node_is_bv_const(e1);
}

static inline BzlaNode *
apply_special_const_lhs_binary_exp(Bzla *bzla,
                                   BzlaNodeKind kind,
                                   BzlaNode *e0,
                                   BzlaNode *e1)
{
  assert(applies_special_const_lhs_binary_exp(bzla, kind, e0, e1));

  char tmpstr[2] = {'\0', '\0'}, *bvstr;
  uint32_t pos, len, width_e0;
  bool invert_b0;
  BzlaBitVector *b0, *bv;
  BzlaMemMgr *mm;
  BzlaSpecialConstBitVector sc;
  BzlaNode *result, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BzlaNode *tmp4, *eq;
  BzlaNodePtrStack stack;
  BzlaSortId sort;

  result    = 0;
  mm        = bzla->mm;
  real_e0   = bzla_node_real_addr(e0);
  real_e1   = bzla_node_real_addr(e1);
  invert_b0 = bzla_node_is_inverted(e0);
  b0        = bzla_node_bv_const_get_bits(real_e0);
  width_e0  = bzla_node_bv_get_width(bzla, real_e0);

  if (invert_b0) b0 = bzla_bv_not(mm, b0);
  sc = bzla_bv_is_special_const(b0);
  if (invert_b0) bzla_bv_free(mm, b0);

  switch (sc)
  {
    case BZLA_SPECIAL_CONST_BV_ZERO:
      switch (kind)
      {
        case BZLA_BV_EQ_NODE:
          if (width_e0 == 1)
          {
            result = bzla_exp_bv_not(bzla, e1);
          }
          else if (is_xor_exp(bzla, e1))
          {
            /* 0 == (a ^ b)  -->  a = b */
            if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
            {
              BZLA_INC_REC_RW_CALL(bzla);
              result = rewrite_eq_exp(
                  bzla,
                  bzla_node_real_addr(
                      bzla_node_real_addr(bzla_node_real_addr(e1)->e[0])->e[0]),
                  bzla_node_real_addr(
                      bzla_node_real_addr(bzla_node_real_addr(e1)->e[0])
                          ->e[1]));
              BZLA_DEC_REC_RW_CALL(bzla);
            }
          }
          else if (bzla_node_is_inverted(e1)
                   && real_e1->kind == BZLA_BV_AND_NODE)
          {
            /* 0 == a | b  -->  a == 0 && b == 0 */
            if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
            {
              BZLA_INC_REC_RW_CALL(bzla);
              left  = rewrite_eq_exp(bzla, bzla_node_invert(real_e1->e[0]), e0);
              right = rewrite_eq_exp(bzla, bzla_node_invert(real_e1->e[1]), e0);
              result = rewrite_bv_and_exp(bzla, left, right);
              BZLA_DEC_REC_RW_CALL(bzla);
              bzla_node_release(bzla, left);
              bzla_node_release(bzla, right);
            }
          }
          break;
        case BZLA_BV_ULT_NODE:
          /* 0 < a --> a != 0 */
          BZLA_INC_REC_RW_CALL(bzla);
          result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
          BZLA_DEC_REC_RW_CALL(bzla);
          break;
        case BZLA_BV_SLT_NODE:
          /* max_signed < a -> false */
          if (width_e0 == 1) result = bzla_exp_false(bzla);
          break;
        case BZLA_BV_ADD_NODE: result = bzla_node_copy(bzla, e1); break;
        case BZLA_BV_MUL_NODE:
        case BZLA_BV_SLL_NODE:
        case BZLA_BV_SRL_NODE:
        case BZLA_BV_UREM_NODE:
        case BZLA_BV_AND_NODE:
          result = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
          break;
        case BZLA_BV_UDIV_NODE:
          tmp2 = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
          tmp4 = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(real_e0));
          BZLA_INC_REC_RW_CALL(bzla);
          eq     = rewrite_eq_exp(bzla, e1, tmp2);
          result = rewrite_cond_exp(bzla, eq, tmp4, tmp2);
          BZLA_DEC_REC_RW_CALL(bzla);
          bzla_node_release(bzla, tmp2);
          bzla_node_release(bzla, eq);
          bzla_node_release(bzla, tmp4);
          break;
        default: break;
      }
      break;

    case BZLA_SPECIAL_CONST_BV_ONE_ONES:
      assert(width_e0 == 1);
      if (kind == BZLA_BV_AND_NODE || kind == BZLA_BV_EQ_NODE
          || kind == BZLA_BV_MUL_NODE)
      {
        result = bzla_node_copy(bzla, e1);
      }
      else if (kind == BZLA_BV_ULT_NODE)
      {
        result = bzla_exp_false(bzla);
      }
      else if (kind == BZLA_BV_SLT_NODE)
      {
        /* min_signed < a -> a != min_signed */
        BZLA_INC_REC_RW_CALL(bzla);
        result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_ONE:
      if (kind == BZLA_BV_MUL_NODE)
      {
        result = bzla_node_copy(bzla, e1);
      }
      else if (width_e0 == 2 && kind == BZLA_BV_SLT_NODE)
      {
        /* max_signed < a -> false */
        result = bzla_exp_false(bzla);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_ONES:
      if (kind == BZLA_BV_EQ_NODE)
      {
        if (is_xnor_exp(bzla, e1)) /* 1+ == (a XNOR b)  -->  a = b */
        {
          if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
          {
            BZLA_INC_REC_RW_CALL(bzla);
            result = rewrite_eq_exp(
                bzla,
                bzla_node_real_addr(
                    bzla_node_real_addr(bzla_node_real_addr(e1)->e[0])->e[0]),
                bzla_node_real_addr(
                    bzla_node_real_addr(bzla_node_real_addr(e1)->e[0])->e[1]));
            BZLA_DEC_REC_RW_CALL(bzla);
          }
        }
        else if (!bzla_node_is_inverted(e1) && e1->kind == BZLA_BV_AND_NODE)
        { /* 1+ == a & b  -->  a == 1+ && b == 1+ */
          if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
          {
            BZLA_INC_REC_RW_CALL(bzla);
            left   = rewrite_eq_exp(bzla, e1->e[0], e0);
            right  = rewrite_eq_exp(bzla, e1->e[1], e0);
            result = rewrite_bv_and_exp(bzla, left, right);
            BZLA_DEC_REC_RW_CALL(bzla);
            bzla_node_release(bzla, left);
            bzla_node_release(bzla, right);
          }
        }
      }
      else if (kind == BZLA_BV_AND_NODE)
      {
        result = bzla_node_copy(bzla, e1);
      }
      else if (kind == BZLA_BV_ULT_NODE)
      {
        /* UNSIGNED_MAX < x */
        result = bzla_exp_false(bzla);
      }
      else if (kind == BZLA_BV_MUL_NODE)
      {
        result = bzla_exp_bv_neg(bzla, e1);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_MIN_SIGNED:
      if (kind == BZLA_BV_SLT_NODE)
      {
        /* min_signed < a -> a != min_signed */
        BZLA_INC_REC_RW_CALL(bzla);
        result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_MAX_SIGNED:
      if (kind == BZLA_BV_SLT_NODE)
      {
        /* max_signed < a -> false */
        result = bzla_exp_false(bzla);
      }
      break;

    default:
      assert(sc == BZLA_SPECIAL_CONST_BV_NONE);
      if (kind == BZLA_BV_EQ_NODE && real_e1->kind == BZLA_BV_AND_NODE
          && bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
      {
        BZLA_INC_REC_RW_CALL(bzla);
        BZLA_INIT_STACK(bzla->mm, stack);
        if (bzla_node_is_inverted(e0))
          bv = bzla_bv_not(bzla->mm, bzla_node_bv_const_get_bits(real_e0));
        else
          bv = bzla_bv_copy(bzla->mm, bzla_node_bv_const_get_bits(real_e0));

        pos = 0;
        /* const == a | b */
        if (bzla_node_is_inverted(e1))
        {
          while (pos < width_e0)
          {
            bvstr     = bzla_bv_to_char(bzla->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn(bvstr + pos, tmpstr);
            bzla_mem_freestr(bzla->mm, bvstr);
            tmp1 = rewrite_bv_slice_exp(bzla,
                                        bzla_node_invert(real_e1->e[0]),
                                        width_e0 - 1 - pos,
                                        width_e0 - pos - len);
            tmp2 = rewrite_bv_slice_exp(bzla,
                                        bzla_node_invert(real_e1->e[1]),
                                        width_e0 - 1 - pos,
                                        width_e0 - pos - len);
            sort = bzla_sort_bv(bzla, len);
            if (tmpstr[0] == '0')
            {
              tmp3 = bzla_exp_bv_zero(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp1, tmp3));
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp2, tmp3));
              bzla_node_release(bzla, tmp3);
            }
            else
            {
              assert(tmpstr[0] == '1');
              tmp3 = bzla_exp_bv_or(bzla, tmp1, tmp2);
              tmp4 = bzla_exp_bv_ones(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp3, tmp4));
              bzla_node_release(bzla, tmp3);
              bzla_node_release(bzla, tmp4);
            }
            bzla_sort_release(bzla, sort);
            bzla_node_release(bzla, tmp1);
            bzla_node_release(bzla, tmp2);
            pos += len;
          }
        }
        else
        {
          assert(!bzla_node_is_inverted(e1));
          /* const == a & b */
          while (pos < width_e0)
          {
            bvstr     = bzla_bv_to_char(bzla->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn(bvstr + pos, tmpstr);
            bzla_mem_freestr(bzla->mm, bvstr);
            tmp1 = rewrite_bv_slice_exp(
                bzla, e1->e[0], width_e0 - 1 - pos, width_e0 - pos - len);
            tmp2 = rewrite_bv_slice_exp(
                bzla, e1->e[1], width_e0 - 1 - pos, width_e0 - pos - len);
            sort = bzla_sort_bv(bzla, len);
            if (tmpstr[0] == '1')
            {
              tmp3 = bzla_exp_bv_ones(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp1, tmp3));
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp2, tmp3));
              bzla_node_release(bzla, tmp3);
            }
            else
            {
              assert(tmpstr[0] == '0');
              tmp3 = rewrite_bv_and_exp(bzla, tmp1, tmp2);
              tmp4 = bzla_exp_bv_zero(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp3, tmp4));
              bzla_node_release(bzla, tmp3);
              bzla_node_release(bzla, tmp4);
            }
            bzla_sort_release(bzla, sort);
            bzla_node_release(bzla, tmp1);
            bzla_node_release(bzla, tmp2);
            pos += len;
          }
        }

        result = bzla_exp_true(bzla);
        assert(!BZLA_EMPTY_STACK(stack));
        do
        {
          tmp1 = BZLA_POP_STACK(stack);
          tmp2 = rewrite_bv_and_exp(bzla, result, tmp1);
          bzla_node_release(bzla, result);
          result = tmp2;
          bzla_node_release(bzla, tmp1);
        } while (!BZLA_EMPTY_STACK(stack));
        bzla_bv_free(bzla->mm, bv);
        BZLA_RELEASE_STACK(stack);
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;
  }

  return result;
}

/*
 * match:  binary op with one constant
 * result: constant
 */
static inline bool
applies_special_const_rhs_binary_exp(Bzla *bzla,
                                     BzlaNodeKind kind,
                                     BzlaNode *e0,
                                     BzlaNode *e1)
{
  (void) bzla;
  (void) kind;
  return !bzla_node_is_bv_const(e0) && bzla_node_is_bv_const(e1);
}

static inline BzlaNode *
apply_special_const_rhs_binary_exp(Bzla *bzla,
                                   BzlaNodeKind kind,
                                   BzlaNode *e0,
                                   BzlaNode *e1)
{
  assert(applies_special_const_rhs_binary_exp(bzla, kind, e0, e1));

  char tmpstr[2] = {'\0', '\0'}, *bvstr;
  uint32_t pos, len, width_e0, width_e1;
  bool invert_b1;
  BzlaBitVector *b1, *bv;
  BzlaMemMgr *mm;
  BzlaSpecialConstBitVector sc;
  BzlaNode *result = 0, *real_e0, *real_e1, *left, *right, *tmp1, *tmp2, *tmp3;
  BzlaNode *tmp4;
  BzlaNodePtrStack stack;
  BzlaSortId sort;

  mm        = bzla->mm;
  real_e0   = bzla_node_real_addr(e0);
  real_e1   = bzla_node_real_addr(e1);
  invert_b1 = bzla_node_is_inverted(e1);
  b1        = bzla_node_bv_const_get_bits(real_e1);
  width_e0  = bzla_node_bv_get_width(bzla, real_e0);
  width_e1  = bzla_node_bv_get_width(bzla, real_e1);

  if (invert_b1) b1 = bzla_bv_not(mm, b1);
  sc = bzla_bv_is_special_const(b1);
  if (invert_b1) bzla_bv_free(mm, b1);

  switch (sc)
  {
    case BZLA_SPECIAL_CONST_BV_ZERO:
      switch (kind)
      {
        case BZLA_BV_EQ_NODE:
          if (width_e0 == 1)
          {
            result = bzla_exp_bv_not(bzla, e0);
          }
          else if (is_xor_exp(bzla, e0))
          {
            /* (a ^ b) == 0 -->  a = b */
            if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
            {
              BZLA_INC_REC_RW_CALL(bzla);
              result = rewrite_eq_exp(
                  bzla,
                  bzla_node_real_addr(
                      bzla_node_real_addr(bzla_node_real_addr(e0)->e[0])->e[0]),
                  bzla_node_real_addr(
                      bzla_node_real_addr(bzla_node_real_addr(e0)->e[0])
                          ->e[1]));
              BZLA_DEC_REC_RW_CALL(bzla);
            }
          }
          else if (bzla_node_is_inverted(e0)
                   && real_e0->kind == BZLA_BV_AND_NODE)
          {
            /*  a | b == 0  -->  a == 0 && b == 0 */
            if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
            {
              BZLA_INC_REC_RW_CALL(bzla);
              left  = rewrite_eq_exp(bzla, bzla_node_invert(real_e0->e[0]), e1);
              right = rewrite_eq_exp(bzla, bzla_node_invert(real_e0->e[1]), e1);
              result = rewrite_bv_and_exp(bzla, left, right);
              BZLA_DEC_REC_RW_CALL(bzla);
              bzla_node_release(bzla, left);
              bzla_node_release(bzla, right);
            }
          }
          break;
        case BZLA_BV_SLL_NODE:
        case BZLA_BV_SRL_NODE:
        case BZLA_BV_UREM_NODE:
        case BZLA_BV_ADD_NODE: result = bzla_node_copy(bzla, e0); break;
        case BZLA_BV_MUL_NODE:
        case BZLA_BV_AND_NODE:
          result = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
          break;
        case BZLA_BV_ULT_NODE:
          /* x < 0 -> false */
          result = bzla_exp_false(bzla);
          break;
        case BZLA_BV_SLT_NODE:
          if (width_e0 == 1)
          {
            /* a < max_signed -> a != max_signed */
            BZLA_INC_REC_RW_CALL(bzla);
            result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
            BZLA_DEC_REC_RW_CALL(bzla);
          }
          break;
        case BZLA_BV_UDIV_NODE:
          result = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(real_e0));
          break;
        default: break;
      }
      break;

    case BZLA_SPECIAL_CONST_BV_ONE_ONES:
      assert(width_e1 == 1);
      if (kind == BZLA_BV_AND_NODE || kind == BZLA_BV_EQ_NODE
          || kind == BZLA_BV_MUL_NODE || kind == BZLA_BV_UDIV_NODE)
      {
        result = bzla_node_copy(bzla, e0);
      }
      else if (kind == BZLA_BV_SLT_NODE)
      {
        /* a < min_signed -> false */
        result = bzla_exp_false(bzla);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_ONE:
      if (kind == BZLA_BV_MUL_NODE || kind == BZLA_BV_UDIV_NODE)
        result = bzla_node_copy(bzla, e0);
      else if (kind == BZLA_BV_UREM_NODE)
        result = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
      else if (kind == BZLA_BV_ULT_NODE)
      {
        BZLA_INC_REC_RW_CALL(bzla);
        tmp1   = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
        result = rewrite_eq_exp(bzla, e0, tmp1);
        bzla_node_release(bzla, tmp1);
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      else if (width_e0 == 2 && kind == BZLA_BV_SLT_NODE)
      {
        /* a < max_signed -> a != max_signed */
        BZLA_INC_REC_RW_CALL(bzla);
        result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;
      break;

    case BZLA_SPECIAL_CONST_BV_ONES:
      if (kind == BZLA_BV_EQ_NODE)
      {
        if (is_xnor_exp(bzla, e0))
        {
          /* (a XNOR b) == 1 -->  a = b */
          if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
          {
            BZLA_INC_REC_RW_CALL(bzla);
            result = rewrite_eq_exp(
                bzla,
                bzla_node_real_addr(
                    bzla_node_real_addr(bzla_node_real_addr(e0)->e[0])->e[0]),
                bzla_node_real_addr(
                    bzla_node_real_addr(bzla_node_real_addr(e0)->e[0])->e[1]));
            BZLA_DEC_REC_RW_CALL(bzla);
          }
        }
        else if (!bzla_node_is_inverted(e0) && e0->kind == BZLA_BV_AND_NODE)
        {
          /* a & b == 1+ -->  a == 1+ && b == 1+ */
          if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
          {
            BZLA_INC_REC_RW_CALL(bzla);
            left   = rewrite_eq_exp(bzla, e0->e[0], e1);
            right  = rewrite_eq_exp(bzla, e0->e[1], e1);
            result = rewrite_bv_and_exp(bzla, left, right);
            BZLA_DEC_REC_RW_CALL(bzla);
            bzla_node_release(bzla, left);
            bzla_node_release(bzla, right);
          }
        }
      }
      else if (kind == BZLA_BV_AND_NODE)
        result = bzla_node_copy(bzla, e0);
      else if (kind == BZLA_BV_ULT_NODE)
      {
        BZLA_INC_REC_RW_CALL(bzla);
        result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      else if (kind == BZLA_BV_MUL_NODE)
        result = bzla_exp_bv_neg(bzla, e0);
      break;

    case BZLA_SPECIAL_CONST_BV_MIN_SIGNED:
      if (kind == BZLA_BV_SLT_NODE)
      {
        /* a < min_signed -> false */
        result = bzla_exp_false(bzla);
      }
      break;

    case BZLA_SPECIAL_CONST_BV_MAX_SIGNED:
      if (kind == BZLA_BV_SLT_NODE)
      {
        /* a < max_signed -> a != max_signed */
        BZLA_INC_REC_RW_CALL(bzla);
        result = bzla_node_invert(rewrite_eq_exp(bzla, e0, e1));
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;

    default:
      assert(sc == BZLA_SPECIAL_CONST_BV_NONE);
      if (kind == BZLA_BV_EQ_NODE && real_e0->kind == BZLA_BV_AND_NODE
          && bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
      {
        BZLA_INC_REC_RW_CALL(bzla);
        BZLA_INIT_STACK(bzla->mm, stack);
        if (bzla_node_is_inverted(e1))
          bv = bzla_bv_not(bzla->mm, bzla_node_bv_const_get_bits(real_e1));
        else
          bv = bzla_bv_copy(bzla->mm, bzla_node_bv_const_get_bits(real_e1));

        pos = 0;
        /* a | b == const */
        if (bzla_node_is_inverted(e0))
        {
          while (pos < width_e1)
          {
            bvstr     = bzla_bv_to_char(bzla->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn(bvstr + pos, tmpstr);
            bzla_mem_freestr(bzla->mm, bvstr);
            tmp1 = rewrite_bv_slice_exp(bzla,
                                        bzla_node_invert(real_e0->e[0]),
                                        width_e1 - 1 - pos,
                                        width_e1 - pos - len);
            tmp2 = rewrite_bv_slice_exp(bzla,
                                        bzla_node_invert(real_e0->e[1]),
                                        width_e1 - 1 - pos,
                                        width_e1 - pos - len);
            sort = bzla_sort_bv(bzla, len);
            if (tmpstr[0] == '0')
            {
              tmp3 = bzla_exp_bv_zero(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp1, tmp3));
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp2, tmp3));
              bzla_node_release(bzla, tmp3);
            }
            else
            {
              assert(tmpstr[0] == '1');
              tmp3 = bzla_exp_bv_or(bzla, tmp1, tmp2);
              tmp4 = bzla_exp_bv_ones(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp3, tmp4));
              bzla_node_release(bzla, tmp3);
              bzla_node_release(bzla, tmp4);
            }
            bzla_sort_release(bzla, sort);
            bzla_node_release(bzla, tmp1);
            bzla_node_release(bzla, tmp2);
            pos += len;
          }
        }
        else
        {
          assert(!bzla_node_is_inverted(e0));
          /* a & b == const */
          while (pos < width_e1)
          {
            bvstr     = bzla_bv_to_char(bzla->mm, bv);
            tmpstr[0] = bvstr[pos];
            len       = (uint32_t) strspn(bvstr + pos, tmpstr);
            bzla_mem_freestr(bzla->mm, bvstr);
            tmp1 = rewrite_bv_slice_exp(
                bzla, e0->e[0], width_e1 - 1 - pos, width_e1 - pos - len);
            tmp2 = rewrite_bv_slice_exp(
                bzla, e0->e[1], width_e1 - 1 - pos, width_e1 - pos - len);
            sort = bzla_sort_bv(bzla, len);
            if (tmpstr[0] == '1')
            {
              tmp3 = bzla_exp_bv_ones(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp1, tmp3));
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp2, tmp3));
              bzla_node_release(bzla, tmp3);
            }
            else
            {
              assert(tmpstr[0] == '0');
              tmp3 = rewrite_bv_and_exp(bzla, tmp1, tmp2);
              tmp4 = bzla_exp_bv_zero(bzla, sort);
              BZLA_PUSH_STACK(stack, rewrite_eq_exp(bzla, tmp3, tmp4));
              bzla_node_release(bzla, tmp3);
              bzla_node_release(bzla, tmp4);
            }
            bzla_sort_release(bzla, sort);
            bzla_node_release(bzla, tmp1);
            bzla_node_release(bzla, tmp2);
            pos += len;
          }
        }

        result = bzla_exp_true(bzla);
        assert(!BZLA_EMPTY_STACK(stack));
        do
        {
          tmp1 = BZLA_POP_STACK(stack);
          tmp2 = rewrite_bv_and_exp(bzla, result, tmp1);
          bzla_node_release(bzla, result);
          result = tmp2;
          bzla_node_release(bzla, tmp1);
        } while (!BZLA_EMPTY_STACK(stack));
        bzla_bv_free(bzla->mm, bv);
        BZLA_RELEASE_STACK(stack);
        BZLA_DEC_REC_RW_CALL(bzla);
      }
      break;
  }

  return result;
}

/* -------------------------------------------------------------------------- */
/* linear term rewriting                                                      */
/* -------------------------------------------------------------------------- */

/* Can we rewrite 'term' as 'factor*lhs + rhs' where 'lhs' is a variable,
 * and 'factor' is odd?  We check whether this is possible but do not use
 * more than 'bound' recursive calls.  */
static bool
rewrite_linear_bv_term_bounded(Bzla *bzla,
                               BzlaNode *term,
                               BzlaBitVector **factor_ptr,
                               BzlaNode **lhs_ptr,
                               BzlaNode **rhs_ptr,
                               uint32_t *bound_ptr)
{
  BzlaNode *tmp, *other;
  BzlaBitVector *factor;

  if (*bound_ptr <= 0) return false;
  if (!bzla_node_is_bv(bzla, term)) return false;

  *bound_ptr -= 1;

  if (bzla_node_is_inverted(term))
  {
    /* term = ~subterm
     *      = -1 - subterm
     *      = -1 - (factor * lhs + rhs)
     *      = (-factor) * lhs + (-1 -rhs)
     *      = (-factor) * lhs + ~rhs
     */
    if (!rewrite_linear_bv_term_bounded(
            bzla, bzla_node_invert(term), &factor, lhs_ptr, rhs_ptr, bound_ptr))
      return false;

    *rhs_ptr    = bzla_node_invert(*rhs_ptr);
    *factor_ptr = bzla_bv_neg(bzla->mm, factor);
    bzla_bv_free(bzla->mm, factor);
  }
  else if (term->kind == BZLA_BV_ADD_NODE)
  {
    if (rewrite_linear_bv_term_bounded(
            bzla, term->e[0], factor_ptr, lhs_ptr, &tmp, bound_ptr))
    {
      /* term = e0 + e1
       *      = (factor * lhs + rhs) + e1
       *      = factor * lhs + (e1 + rhs)
       */
      other = term->e[1];
    }
    else if (rewrite_linear_bv_term_bounded(
                 bzla, term->e[1], factor_ptr, lhs_ptr, &tmp, bound_ptr))
    {
      /* term = e0 + e1
       *      = e0 + (factor * lhs + rhs)
       *      = factor * lhs + (e0 + rhs)
       */
      other = term->e[0];
    }
    else
    {
      return false;
    }

    *rhs_ptr = rewrite_bv_add_exp(bzla, other, tmp);
    bzla_node_release(bzla, tmp);
  }
  else if (term->kind == BZLA_BV_MUL_NODE)
  {
    if (is_odd_bv_const_exp(term->e[0]))
    {
      if (!rewrite_linear_bv_term_bounded(
              bzla, term->e[1], &factor, lhs_ptr, &tmp, bound_ptr))
      {
        return false;
      }

      /* term = e0 * e1
       *      = e0 * (factor * lhs + rhs)
       *      = (e0 * factor) * lhs + e0 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[0];
    }
    else if (is_odd_bv_const_exp(term->e[1]))
    {
      if (!rewrite_linear_bv_term_bounded(
              bzla, term->e[0], &factor, lhs_ptr, &tmp, bound_ptr))
      {
        return false;
      }

      /* term = e0 * e1
       *      = (factor * lhs + rhs) * e1
       *      = (e1 * factor) * lhs + e1 * rhs
       *      = (other * factor) * lhs + other * rhs
       */
      other = term->e[1];
    }
    else
    {
      return false;
    }

    assert(!bzla_node_is_inverted(other));
    *factor_ptr =
        bzla_bv_mul(bzla->mm, bzla_node_bv_const_get_bits(other), factor);
    bzla_bv_free(bzla->mm, factor);
    *rhs_ptr = rewrite_bv_mul_exp(bzla, other, tmp);
    bzla_node_release(bzla, tmp);
  }
  else if (term->kind == BZLA_VAR_NODE)
  {
    *lhs_ptr    = bzla_node_copy(bzla, term);
    *rhs_ptr    = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(term));
    *factor_ptr = bzla_bv_one(bzla->mm, bzla_node_bv_get_width(bzla, term));
  }
  else
  {
    return false;
  }

  return true;
}

bool
bzla_rewrite_linear_bv_term(Bzla *bzla,
                            BzlaNode *term,
                            BzlaBitVector **fp,
                            BzlaNode **lp,
                            BzlaNode **rp)
{
  assert(bzla);
  assert(term);
  assert(fp);
  assert(lp);
  assert(rp);
  uint32_t bound = 100;
  bool res;
  res = rewrite_linear_bv_term_bounded(bzla, term, fp, lp, rp, &bound);
  if (res) bzla->stats.linear_equations++;
  return res;
}

/* -------------------------------------------------------------------------- */
/* rewriting rules                                                            */
/* -------------------------------------------------------------------------- */

/*
 * for each rule we define two functions:
 *   static inline bool
 *   applies_<rw_rule> (Bzla * bzla, ...)
 *   {
 *   }
 *
 *   static inline BzlaNode *
 *   apply_<rw_rule> (Bzla * bzla, ...)
 *   {
 *     assert (applies_<rw_rule> (...));
 *   }
 *
 * where the first one determines if <rw_rule> is applicable, and the second
 * one applies the rule.
 *
 * for adding rw rules to a rewrite function use the ADD_RW_RULE macro.
 */

/* SLICE rules                                                                */
/* -------------------------------------------------------------------------- */

/*
 * match:  exp[len(exp) - 1:0]
 * result: exp
 */
static inline bool
applies_full_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  (void) bzla;
  return bzla_node_bv_get_width(bzla, exp) == upper - lower + 1;
}

static inline BzlaNode *
apply_full_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(applies_full_slice(bzla, exp, upper, lower));
  (void) bzla;
  (void) upper;
  (void) lower;
  return bzla_node_copy(bzla, exp);
}

/*
 * match: exp[upper:lower], where exp is a constant
 * result: constant
 */
static inline bool
applies_const_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  (void) bzla;
  (void) upper;
  (void) lower;
  return bzla_node_is_bv_const(exp);
}

static inline BzlaNode *
apply_const_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(applies_const_slice(bzla, exp, upper, lower));

  BzlaBitVector *bits;
  BzlaNode *result;

  bits =
      bzla_bv_slice(bzla->mm, bzla_node_bv_const_get_bits(exp), upper, lower);
  result = bzla_exp_bv_const(bzla, bits);
  bzla_bv_free(bzla->mm, bits);
  return result;
}

/*
 * match:  (exp[u:l])[upper:lower]
 * result: exp[l+upper:l+lower]
 */
static inline bool
applies_slice_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_slice(exp);
}

static inline BzlaNode *
apply_slice_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(applies_slice_slice(bzla, exp, upper, lower));

  BzlaNode *result, *real_exp;

  real_exp = bzla_node_real_addr(exp);
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_slice_exp(bzla,
                                bzla_node_cond_invert(exp, real_exp->e[0]),
                                bzla_node_bv_slice_get_lower(real_exp) + upper,
                                bzla_node_bv_slice_get_lower(real_exp) + lower);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: (a::b)[len(b)-1:0]
 * result: b
 */
static inline bool
applies_concat_lower_slice(Bzla *bzla,
                           BzlaNode *exp,
                           uint32_t upper,
                           uint32_t lower)
{
  (void) bzla;
  return bzla_node_is_bv_concat(exp) && lower == 0
         && bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[1])
                == upper - lower + 1;
}

static inline BzlaNode *
apply_concat_lower_slice(Bzla *bzla,
                         BzlaNode *exp,
                         uint32_t upper,
                         uint32_t lower)
{
  assert(applies_concat_lower_slice(bzla, exp, upper, lower));
  (void) upper;
  (void) lower;

  BzlaNode *result;

  result = bzla_node_cond_invert(exp, bzla_node_real_addr(exp)->e[1]);
  return bzla_node_copy(bzla, result);
}

/*
 * match: (a::b)[len(a)+len(b)-1:len(b)]
 * result: a
 */
static inline bool
applies_concat_upper_slice(Bzla *bzla,
                           BzlaNode *exp,
                           uint32_t upper,
                           uint32_t lower)
{
  return bzla_node_is_bv_concat(exp)
         && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) < 3
         && upper == bzla_node_bv_get_width(bzla, exp) - 1
         && bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[0])
                == upper - lower + 1;
}

static inline BzlaNode *
apply_concat_upper_slice(Bzla *bzla,
                         BzlaNode *exp,
                         uint32_t upper,
                         uint32_t lower)
{
  assert(applies_concat_upper_slice(bzla, exp, upper, lower));
  (void) upper;
  (void) lower;

  BzlaNode *result;

  result = bzla_node_cond_invert(exp, bzla_node_real_addr(exp)->e[0]);
  return bzla_node_copy(bzla, result);
}

/*
 * match:  (a::b)[upper:lower], where lower >= len(b)
 * result: a[upper-len(b):lower-len(b)]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_upper_slice(Bzla *bzla,
                               BzlaNode *exp,
                               uint32_t upper,
                               uint32_t lower)
{
  (void) upper;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) >= 3
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_is_bv_concat(exp)
         && lower
                >= bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[1]);
}

static inline BzlaNode *
apply_concat_rec_upper_slice(Bzla *bzla,
                             BzlaNode *exp,
                             uint32_t upper,
                             uint32_t lower)
{
  assert(applies_concat_rec_upper_slice(bzla, exp, upper, lower));

  uint32_t len;
  BzlaNode *result, *real_exp;

  real_exp = bzla_node_real_addr(exp);
  len      = bzla_node_bv_get_width(bzla, real_exp->e[1]);
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_slice_exp(bzla,
                                bzla_node_cond_invert(exp, real_exp->e[0]),
                                upper - len,
                                lower - len);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (a::b)[upper:lower], where upper < len(b)
 * result: b[upper:lower]
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_lower_slice(Bzla *bzla,
                               BzlaNode *exp,
                               uint32_t upper,
                               uint32_t lower)
{
  (void) lower;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) >= 3
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_is_bv_concat(exp)
         && upper
                < bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[1]);
}

static inline BzlaNode *
apply_concat_rec_lower_slice(Bzla *bzla,
                             BzlaNode *exp,
                             uint32_t upper,
                             uint32_t lower)
{
  assert(applies_concat_rec_lower_slice(bzla, exp, upper, lower));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_slice_exp(
      bzla,
      bzla_node_cond_invert(exp, bzla_node_real_addr(exp)->e[1]),
      upper,
      lower);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (a::b)[upper:lower], where lower = 0 and upper >= len(b)
 * result: a[upper-len(b):0]::b
 *
 * concats are normalized at rewrite level 3,
 * we recursively check if slice and child of concat matches
 */
static inline bool
applies_concat_rec_slice(Bzla *bzla,
                         BzlaNode *exp,
                         uint32_t upper,
                         uint32_t lower)
{
  return bzla_node_is_bv_concat(exp)
         && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) >= 3
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && lower == 0
         && upper
                >= bzla_node_bv_get_width(bzla, bzla_node_real_addr(exp)->e[1]);
}

static inline BzlaNode *
apply_concat_rec_slice(Bzla *bzla,
                       BzlaNode *exp,
                       uint32_t upper,
                       uint32_t lower)
{
  assert(applies_concat_rec_slice(bzla, exp, upper, lower));
  (void) lower;

  uint32_t len;
  BzlaNode *result, *real_exp, *tmp;

  real_exp = bzla_node_real_addr(exp);
  len      = bzla_node_bv_get_width(bzla, real_exp->e[1]);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp = rewrite_bv_slice_exp(
      bzla, bzla_node_cond_invert(exp, real_exp->e[0]), upper - len, 0);
  result = rewrite_bv_concat_exp(
      bzla, tmp, bzla_node_cond_invert(exp, real_exp->e[1]));
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  (a & b)[upper:lower]
 * result: a[upper:lower] & b[upper:lower]
 */
static inline bool
applies_and_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) >= 3
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(exp)
         && (slice_simplifiable(bzla_node_real_addr(exp)->e[0])
             || slice_simplifiable(bzla_node_real_addr(exp)->e[1]));
}

static inline BzlaNode *
apply_and_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(applies_and_slice(bzla, exp, upper, lower));

  BzlaNode *result, *left, *right, *real_exp;

  real_exp = bzla_node_real_addr(exp);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_slice_exp(bzla, real_exp->e[0], upper, lower);
  right  = rewrite_bv_slice_exp(bzla, real_exp->e[1], upper, lower);
  result = bzla_exp_bv_and(bzla, left, right);
  bzla_node_release(bzla, right);
  bzla_node_release(bzla, left);
  result = bzla_node_cond_invert(exp, result);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (c ? a : b)[upper:lower]
 * result: c ? a[upper:lower] : b[upper:lower]
 */
static inline bool
applies_bcond_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  (void) upper;
  (void) lower;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) >= 3
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(exp)
         && (slice_simplifiable(bzla_node_real_addr(exp)->e[1])
             || slice_simplifiable(bzla_node_real_addr(exp)->e[2]));
}

static inline BzlaNode *
apply_bcond_slice(Bzla *bzla, BzlaNode *exp, uint32_t upper, uint32_t lower)
{
  assert(applies_bcond_slice(bzla, exp, upper, lower));

  BzlaNode *t, *e, *result, *real_exp;

  real_exp = bzla_node_real_addr(exp);
  BZLA_INC_REC_RW_CALL(bzla);
  t      = rewrite_bv_slice_exp(bzla, real_exp->e[1], upper, lower);
  e      = rewrite_bv_slice_exp(bzla, real_exp->e[2], upper, lower);
  result = rewrite_cond_exp(bzla, real_exp->e[0], t, e);
  bzla_node_release(bzla, e);
  bzla_node_release(bzla, t);
  result = bzla_node_cond_invert(exp, result);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

static inline bool
applies_zero_lower_slice(Bzla *bzla,
                         BzlaNode *exp,
                         uint32_t upper,
                         uint32_t lower)
{
  (void) upper;
  return bzla_opt_get(bzla, BZLA_OPT_RW_EXTRACT_ARITH)
         && bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && lower == 0
         && upper < bzla_node_bv_get_width(bzla, exp) / 2
         && (bzla_node_is_bv_mul(exp) || bzla_node_is_bv_add(exp));
  //	     || bzla_node_is_bv_and (exp));
}

static inline BzlaNode *
apply_zero_lower_slice(Bzla *bzla,
                       BzlaNode *exp,
                       uint32_t upper,
                       uint32_t lower)
{
  BzlaNode *result, *real_exp, *tmp1, *tmp2;

  real_exp = bzla_node_real_addr(exp);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp1   = rewrite_bv_slice_exp(bzla, real_exp->e[0], upper, lower);
  tmp2   = rewrite_bv_slice_exp(bzla, real_exp->e[1], upper, lower);
  result = bzla_rewrite_binary_exp(bzla, real_exp->kind, tmp1, tmp2);
  result = bzla_node_cond_invert(exp, result);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp1);
  bzla_node_release(bzla, tmp2);
  return result;
}

/* EQ rules                                                                   */
/* -------------------------------------------------------------------------- */

/*
 * match:  a = a
 * result: true
 */
static inline bool
applies_true_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_true_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_true_eq(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
}

/*
 * match:  a = b, where a != b
 * result: false
 */
static inline bool
applies_false_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return is_always_unequal(bzla, e0, e1);
}

static inline BzlaNode *
apply_false_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_false_eq(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_false(bzla);
}

/*
 * match:  a + b = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline bool
applies_add_left_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && e0->kind == BZLA_BV_ADD_NODE && e0->e[0] == e1;
}

static inline BzlaNode *
apply_add_left_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_left_eq(bzla, e0, e1));
  (void) e1;

  BzlaNode *tmp, *result;

  tmp = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, tmp, e0->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  b + a = a
 * result: b = 0
 *
 * This rule does not lead to less substitutions. 'a' cannot
 * be substituted as the occurrence check would fail
 */
static inline bool
applies_add_right_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && e0->kind == BZLA_BV_ADD_NODE && e0->e[1] == e1;
}

static inline BzlaNode *
apply_add_right_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_right_eq(bzla, e0, e1));
  (void) e1;

  BzlaNode *tmp, *result;

  tmp = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, tmp, e0->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  a + b = a + c
 * result: b = c
 */
static inline bool
applies_add_add_1_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && e0->kind == BZLA_BV_ADD_NODE
         && e1->kind == BZLA_BV_ADD_NODE && e0->e[0] == e1->e[0];
}

static inline BzlaNode *
apply_add_add_1_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_add_1_eq(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, e0->e[1], e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a + b = c + a
 * result: b = c
 */
static inline bool
applies_add_add_2_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && e0->kind == BZLA_BV_ADD_NODE
         && e1->kind == BZLA_BV_ADD_NODE && e0->e[0] == e1->e[1];
}

static inline BzlaNode *
apply_add_add_2_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_add_2_eq(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, e0->e[1], e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  b + a = a + c
 * result: b = c
 */
static inline bool
applies_add_add_3_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && e0->kind == BZLA_BV_ADD_NODE
         && e1->kind == BZLA_BV_ADD_NODE && e0->e[1] == e1->e[0];
}

static inline BzlaNode *
apply_add_add_3_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_add_3_eq(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, e0->e[0], e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  b + a = c + a
 * result: b = c
 */
static inline bool
applies_add_add_4_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && e0->kind == BZLA_BV_ADD_NODE
         && e1->kind == BZLA_BV_ADD_NODE && e0->e[1] == e1->e[1];
}

static inline BzlaNode *
apply_add_add_4_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_add_4_eq(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla, e0->e[0], e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  t = a - b   (t = a + ~b + 1)
 * result: t + b = a
 */
static inline bool
applies_sub_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e0;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_regular(e1)
         && bzla_node_is_bv_add(e1)
         && ((bzla_node_is_regular(e1->e[0])
              && bzla_node_bv_is_neg(bzla, e1->e[0], 0))
             || (bzla_node_is_regular(e1->e[1])
                 && bzla_node_bv_is_neg(bzla, e1->e[1], 0)));
}

static inline BzlaNode *
apply_sub_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_sub_eq(bzla, e0, e1));

  BzlaNode *result;
  BzlaNode *neg = 0, *other;

  if (bzla_node_bv_is_neg(bzla, e1->e[0], &neg))
    other = e1->e[1];
  else
  {
    bzla_node_bv_is_neg(bzla, e1->e[1], &neg);
    other = e1->e[0];
  }
  assert(neg);

  BZLA_INC_REC_RW_CALL(bzla);
  BzlaNode *lhs = rewrite_bv_add_exp(bzla, e0, neg);
  result        = rewrite_eq_exp(bzla, lhs, other);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, lhs);
  return result;
}

#if 0
/*
 * match:  a & b = ~a & ~b
 * result: a = ~b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_1_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
	 && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && !bzla_node_is_inverted (e0)
	 && !bzla_node_is_inverted (e1)
	 && e0->kind == BZLA_BV_AND_NODE
	 && e1->kind == BZLA_BV_AND_NODE
	 && e0->e[0] == bzla_node_invert (e1->e[0])
	 && e0->e[1] == bzla_node_invert (e1->e[1])
	 && bzla_node_is_inverted (e0->e[0]) ==
	    bzla_node_is_inverted (e0->e[1]);
}

static inline BzlaNode * 
apply_and_and_1_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_and_and_1_eq (bzla, e0, e1));
  assert (bzla_node_is_inverted (e1->e[0]) == bzla_node_is_inverted (e1->e[1]));
  (void) e1;

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL (bzla);
  result = rewrite_eq_exp (bzla, e0->e[0], bzla_node_invert (e0->e[1]));
  BZLA_DEC_REC_RW_CALL (bzla);
  return result;
}

/*
 * match:  ~a & b = a & ~b
 * result: a = b
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_2_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
	 && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && !bzla_node_is_inverted (e0)
	 && !bzla_node_is_inverted (e1)
	 && e0->kind == BZLA_BV_AND_NODE
	 && e1->kind == BZLA_BV_AND_NODE
	 && e0->e[0] == bzla_node_invert (e1->e[0])
	 && e0->e[1] == bzla_node_invert (e1->e[1])
	 && bzla_node_is_inverted (e0->e[0]) !=
	    bzla_node_is_inverted (e0->e[1]);
}

static inline BzlaNode * 
apply_and_and_2_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_and_and_2_eq (bzla, e0, e1));
  assert (bzla_node_is_inverted (e1->e[0]) != bzla_node_is_inverted (e1->e[1]));
  (void) e1;

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL (bzla);
  result = rewrite_eq_exp (bzla, bzla_node_real_addr (e0->e[0]),
				bzla_node_real_addr (e0->e[1]));
  BZLA_DEC_REC_RW_CALL (bzla);
  return result;
}

/*
 * match:  a & b = a & ~b
 * result: a = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_3_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
	 && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && !bzla_node_is_inverted (e0)
	 && !bzla_node_is_inverted (e1)
	 && e0->kind == BZLA_BV_AND_NODE
	 && e1->kind == BZLA_BV_AND_NODE
	 && e0->e[0] == e1->e[0] 
	 && e0->e[1] == bzla_node_invert (e1->e[1]);
}

static inline BzlaNode * 
apply_and_and_3_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_and_and_3_eq (bzla, e0, e1));
  (void) e1;

  BzlaNode *tmp, *result;

  tmp = bzla_exp_bv_zero (bzla, bzla_node_get_sort_id (e0));
  BZLA_INC_REC_RW_CALL (bzla);
  result = rewrite_eq_exp (bzla, e0->e[0], tmp);
  BZLA_DEC_REC_RW_CALL (bzla);
  bzla_node_release (bzla, tmp);
  return result;
}

/*
 * match:  a & b = ~a & b
 * result: b = 0
 *
 * Commutative operators are normalized ignoring signs, so we do not have to
 * check cases like a & b ==  ~b & a as they are represented as a & b == a & ~b
 */
static inline bool
applies_and_and_4_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
	 && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && !bzla_node_is_inverted (e0)
	 && !bzla_node_is_inverted (e1)
	 && e0->kind == BZLA_BV_AND_NODE
	 && e1->kind == BZLA_BV_AND_NODE
	 && e0->e[0] == bzla_node_invert (e1->e[0])
	 && e0->e[1] == e1->e[1];
}

static inline BzlaNode *
apply_and_and_4_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_and_and_4_eq (bzla, e0, e1));
  (void) e1;

  BzlaNode *tmp, *result;

  tmp = bzla_exp_bv_zero (bzla, bzla_node_get_sort_id (e0));
  BZLA_INC_REC_RW_CALL (bzla);
  result = rewrite_eq_exp (bzla, e0->e[1], tmp);
  BZLA_DEC_REC_RW_CALL (bzla);
  bzla_node_release (bzla, tmp);
  return result;
}
#endif

/*
 * match:  b ? a : t = d, where a != d
 * result: !b AND d = t
 */
static inline bool
applies_bcond_uneq_if_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && bzla_node_is_bv_cond(e0) && is_always_unequal(bzla, e0->e[1], e1);
}

static inline BzlaNode *
apply_bcond_uneq_if_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_uneq_if_eq(bzla, e0, e1));

  BzlaNode *tmp, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_eq_exp(bzla, e0->e[2], e1);
  result = rewrite_bv_and_exp(bzla, bzla_node_invert(e0->e[0]), tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  b ? a : t = d, where t != d
 * result: b AND a = t
 */
static inline bool
applies_bcond_uneq_else_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && bzla_node_is_bv_cond(e0) && is_always_unequal(bzla, e0->e[2], e1);
}

static inline BzlaNode *
apply_bcond_uneq_else_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_uneq_else_eq(bzla, e0, e1));

  BzlaNode *tmp, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_eq_exp(bzla, e0->e[1], e1);
  result = rewrite_bv_and_exp(bzla, e0->e[0], tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  a = b ? a : c
 * result: b OR a = c
 *
 * match:  a = ~(b ? a : c)
 * result: !b AND a = ~c
 */
static inline bool
applies_bcond_if_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(e1)
         && bzla_node_real_addr(e1)->e[1] == e0;
}

static inline BzlaNode *
apply_bcond_if_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_if_eq(bzla, e0, e1));

  BzlaNode *tmp, *result, *real_e1;

  real_e1 = bzla_node_real_addr(e1);

  BZLA_INC_REC_RW_CALL(bzla);
  if (bzla_node_is_inverted(e1))
  {
    tmp    = rewrite_eq_exp(bzla, bzla_node_invert(real_e1->e[2]), e0);
    result = rewrite_bv_and_exp(bzla, bzla_node_invert(real_e1->e[0]), tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp(bzla, real_e1->e[2], e0);
    result = bzla_exp_bv_or(bzla, real_e1->e[0], tmp);
  }
  bzla_node_release(bzla, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a = b ? c : a
 * result: !b OR a = c
 *
 * match:  a = ~(b ? c : a)
 * result: b AND a = ~c
 */
static inline bool
applies_bcond_else_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(e1)
         && bzla_node_real_addr(e1)->e[2] == e0;
}

static inline BzlaNode *
apply_bcond_else_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_else_eq(bzla, e0, e1));

  BzlaNode *tmp, *result, *real_e1;

  real_e1 = bzla_node_real_addr(e1);

  BZLA_INC_REC_RW_CALL(bzla);
  if (bzla_node_is_inverted(e1))
  {
    tmp    = rewrite_eq_exp(bzla, bzla_node_invert(real_e1->e[1]), e0);
    result = rewrite_bv_and_exp(bzla, real_e1->e[0], tmp);
  }
  else
  {
    tmp    = rewrite_eq_exp(bzla, real_e1->e[1], e0);
    result = bzla_exp_bv_or(bzla, bzla_node_invert(real_e1->e[0]), tmp);
  }
  bzla_node_release(bzla, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (x ? a : b) = (x : c : d), where either a = c or b = d
 * result: x ? a = c : b = d
 */
static inline bool
applies_bcond_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(real_e0)
         && bzla_node_is_bv_cond(real_e1)
         && bzla_node_is_inverted(e0)
                == bzla_node_is_inverted(e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode *
apply_bcond_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_eq(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_eq_exp(bzla,
                        bzla_node_cond_invert(e0, real_e0->e[1]),
                        bzla_node_cond_invert(e1, real_e1->e[1]));
  right  = rewrite_eq_exp(bzla,
                         bzla_node_cond_invert(e0, real_e0->e[2]),
                         bzla_node_cond_invert(e1, real_e1->e[2]));
  result = rewrite_cond_exp(bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

/*
 * match:  a * b + a * c
 * result: a * (b + c)
 */
static inline bool
applies_add_mul_distrib(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_mul(e0)
         && bzla_node_is_bv_mul(e1)
         && (e0->e[0] == e1->e[0] || e0->e[0] == e1->e[1]
             || e0->e[1] == e1->e[0] || e0->e[1] == e1->e[1]);
}

static inline BzlaNode *
apply_add_mul_distrib(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_add_mul_distrib(bzla, e0, e1));

  BzlaNode *add, *mul, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  if (e0->e[0] == e1->e[0])
  {
    add = rewrite_bv_add_exp(bzla, e0->e[1], e1->e[1]);
    mul = e0->e[0];
  }
  else if (e0->e[0] == e1->e[1])
  {
    add = rewrite_bv_add_exp(bzla, e0->e[1], e1->e[0]);
    mul = e0->e[0];
  }
  else if (e0->e[1] == e1->e[0])
  {
    add = rewrite_bv_add_exp(bzla, e0->e[0], e1->e[1]);
    mul = e0->e[1];
  }
  else
  {
    assert(e0->e[1] == e1->e[1]);
    add = rewrite_bv_add_exp(bzla, e0->e[0], e1->e[0]);
    mul = e0->e[1];
  }

  result = rewrite_bv_mul_exp(bzla, mul, add);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, add);
  return result;
}

/*
 * match:  a * (b + c) = a * b + a * c
 * result: true
 */
static inline bool
applies_distrib_add_mul_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool result;
  BzlaNode *tmp = 0;

  result = bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
           && !bzla_node_is_inverted(e0) && !bzla_node_is_inverted(e1)
           && bzla_node_is_bv_mul(e0) && bzla_node_is_bv_add(e1)
           && applies_add_mul_distrib(bzla, e1->e[0], e1->e[1])
           && (tmp = apply_add_mul_distrib(bzla, e1->e[0], e1->e[1]))
           && tmp == e0;
  if (tmp) bzla_node_release(bzla, tmp);
  return result;
}

static inline BzlaNode *
apply_distrib_add_mul_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_distrib_add_mul_eq(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
}

/*
 * match:  a :: b = c
 * result: a[u:l] = c[u:l] AND (a::b)[l:0] = c[l:0]
 * with: u: len(c)-1
 *       l: len(c)-len(a)+1
 *
 * push eq down over concats
 */
static inline bool
applies_concat_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_real_addr(e0)->kind == BZLA_BV_CONCAT_NODE;
}

static inline BzlaNode *
apply_concat_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_concat_eq(bzla, e0, e1));

  uint32_t upper, lower;
  BzlaNode *real_e0, *tmp2, *tmp4, *result, *eq1, *eq2;

  real_e0 = bzla_node_real_addr(e0);

  BZLA_INC_REC_RW_CALL(bzla);
  upper = bzla_node_bv_get_width(bzla, real_e0) - 1;
  lower = upper - bzla_node_bv_get_width(bzla, real_e0->e[0]) + 1;

  tmp2 = rewrite_bv_slice_exp(bzla, e1, upper, lower);
  lower--;
  tmp4 = rewrite_bv_slice_exp(bzla, e1, lower, 0);

  /* creating two slices on e1 does not really improve the situation here,
   * hence only create a result if a slice on e1 yields a result different
   * from a slice (through further rewriting) */
  if (!(bzla_node_is_bv_slice(tmp2) && bzla_node_is_bv_slice(tmp4)))
  {
    eq1 = rewrite_eq_exp(bzla, bzla_node_cond_invert(e0, real_e0->e[0]), tmp2);
    eq2 = rewrite_eq_exp(bzla, bzla_node_cond_invert(e0, real_e0->e[1]), tmp4);
    result = rewrite_bv_and_exp(bzla, eq1, eq2);
    bzla_node_release(bzla, eq1);
    bzla_node_release(bzla, eq2);
  }
  else
    result = 0;

  bzla_node_release(bzla, tmp2);
  bzla_node_release(bzla, tmp4);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

#if 0
static inline bool
applies_zero_eq_and_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  BzlaNode *real_e1;
  real_e1 = bzla_node_real_addr (e1);
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
	 && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && is_const_zero_exp (bzla, e0)
	 && bzla_node_is_bv_and (real_e1)
	 && (bzla_node_is_bv_const (real_e1->e[0])
	     || bzla_node_is_bv_const (real_e1->e[1]));
}

static inline BzlaNode *
apply_zero_eq_and_eq (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  (void) e0;
  uint32_t len, upper, lower;
  BzlaNode *result, *real_e1, *masked, *zero, *slice; 
  BzlaSortId sort;

  real_e1 = bzla_node_real_addr (e1);

  if (is_bit_mask (real_e1->e[0], &upper, &lower))
    masked = real_e1->e[1];
  else if (is_bit_mask (real_e1->e[1], &upper, &lower))
    masked = real_e1->e[0];
  else
    return 0;

  len = upper - lower + 1;

  BZLA_INC_REC_RW_CALL (bzla);
  sort = bzla_sort_bv (bzla, len);
  zero = bzla_exp_bv_zero (bzla, sort);
  bzla_sort_release (bzla, sort);
  slice = rewrite_slice_exp (bzla, masked, upper, lower);
  result = rewrite_eq_exp (bzla, zero, slice);
  BZLA_DEC_REC_RW_CALL (bzla);
  bzla_node_release (bzla, zero);
  bzla_node_release (bzla, slice);
  return result;
}
#endif

/* ULT rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a < a
 * result: false
 */
static inline bool
applies_false_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_false_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_false_lt(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_false(bzla);
}

/*
 * match:  a < b, where len(a) = 1
 * result: !a AND b
 */
static inline bool
applies_bool_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_ult(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, bzla_node_invert(e0), e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (a::b) < (a::c)
 * result: b < c
 */
static inline bool
applies_concat_upper_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_concat(e0)
         && e0->kind == e1->kind && e0->e[0] == e1->e[0];
}

static inline BzlaNode *
apply_concat_upper_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_concat_upper_ult(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_ult_exp(bzla, e0->e[1], e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (b::a) < (c::a)
 * result: b < c
 */
static inline bool
applies_concat_lower_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_concat(e0)
         && e0->kind == e1->kind && e0->e[1] == e1->e[1];
}

static inline BzlaNode *
apply_concat_lower_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_concat_lower_ult(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_ult_exp(bzla, e0->e[0], e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (x ? a : b) < (x : c : d), where either a = c or b = d
 * result: x ? a < c : b < d
 */
static inline bool
applies_bcond_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(real_e0)
         && bzla_node_is_bv_cond(real_e1)
         && bzla_node_is_inverted(e0)
                == bzla_node_is_inverted(e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode *
apply_bcond_ult(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_ult(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_ult_exp(bzla,
                            bzla_node_cond_invert(e0, real_e0->e[1]),
                            bzla_node_cond_invert(e1, real_e1->e[1]));
  right  = rewrite_bv_ult_exp(bzla,
                             bzla_node_cond_invert(e0, real_e0->e[2]),
                             bzla_node_cond_invert(e1, real_e1->e[2]));
  result = rewrite_cond_exp(bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

/* SLT rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a < b, where len(a) = 1
 * result: a AND !b
 */
static inline bool
applies_bool_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_slt(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, e0, bzla_node_invert(e1));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (b::a) < (c::a)
 * result: b < c
 */
static inline bool
applies_concat_lower_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_concat(e0)
         && e0->kind == e1->kind && e0->e[1] == e1->e[1];
}

static inline BzlaNode *
apply_concat_lower_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_concat_lower_slt(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_slt_exp(bzla, e0->e[0], e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (x ? a : b) < (x : c : d), where either a = c or b = d
 * result: x ? a < c : b < d
 */
static inline bool
applies_bcond_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(real_e0)
         && bzla_node_is_bv_cond(real_e1)
         && bzla_node_is_inverted(e0)
                == bzla_node_is_inverted(e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode *
apply_bcond_slt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_slt(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_slt_exp(bzla,
                            bzla_node_cond_invert(e0, real_e0->e[1]),
                            bzla_node_cond_invert(e1, real_e1->e[1]));
  right  = rewrite_bv_slt_exp(bzla,
                             bzla_node_cond_invert(e0, real_e0->e[2]),
                             bzla_node_cond_invert(e1, real_e1->e[2]));
  result = rewrite_cond_exp(bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

/* AND rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a & a
 * result: a
 */
static inline bool
applies_idem1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_idem1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_idem1_and(bzla, e0, e1));
  (void) e1;
  return bzla_node_copy(bzla, e0);
}

/*
 * match:  a & ~a
 * result: 0
 */
static inline bool
applies_contr1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_invert(e0) == e1;
}

static inline BzlaNode *
apply_contr1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_contr1_and(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match: a & b & c & d, where a = ~c OR a = ~d OR b = ~c OR b = ~d
 * result: false
 *
 * second rule of contradiction
 */
static inline bool
applies_contr2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_is_bv_and(e0) && bzla_node_is_bv_and(e1)
         && !bzla_node_is_inverted(e0) && !bzla_node_is_inverted(e1)
         && (e0->e[0] == bzla_node_invert(e1->e[0])
             || e0->e[0] == bzla_node_invert(e1->e[1])
             || e0->e[1] == bzla_node_invert(e1->e[0])
             || e0->e[1] == bzla_node_invert(e1->e[1]));
}

static inline BzlaNode *
apply_contr2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_contr2_and(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match: a & b & c & d, where a = c or b = c
 * result: a & b & d
 *
 * symmetric rule of idempotency
 */
static inline bool
applies_idem2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(e0)
         && bzla_node_is_bv_and(e1) && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1)
         && (real_e0->e[0] == real_e1->e[0] || real_e0->e[1] == real_e1->e[0]);
}

static inline BzlaNode *
apply_idem2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_idem2_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, e0, bzla_node_real_addr(e1)->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a & b & c & d, where a = d OR b = d
 * result: a & b & c
 *
 * use commutativity
 */
static inline bool
applies_comm_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(e0)
         && bzla_node_is_bv_and(e1) && !bzla_node_is_inverted(e0)
         && !bzla_node_is_inverted(e1)
         && (real_e0->e[0] == real_e1->e[1] || real_e0->e[1] == real_e1->e[1]);
}

static inline BzlaNode *
apply_comm_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_comm_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, e0, bzla_node_real_addr(e1)->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a & b & ~(c & d), where a = c OR a = d OR b = c OR b = d
 * result: a & b
 */
static inline bool
applies_subsum1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla_node_is_bv_and(e0) && bzla_node_is_bv_and(e1)
         && !bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1)
         && (real_e0->e[0] == bzla_node_invert(real_e1->e[0])
             || real_e0->e[0] == bzla_node_invert(real_e1->e[1])
             || real_e0->e[1] == bzla_node_invert(real_e1->e[0])
             || real_e0->e[1] == bzla_node_invert(real_e1->e[1]));
}

static inline BzlaNode *
apply_subsum1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subsum1_and(bzla, e0, e1));
  (void) e1;
  return bzla_node_copy(bzla, e0);
}

/*
 * match: a & b & ~(c & d), where a = c OR b = c
 * result: a & b & ~d
 *
 * symmetric rule of substitution
 */
static inline bool
applies_subst1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_bv_and(real_e1) && !bzla_node_is_inverted(e0)
         && bzla_node_is_inverted(e1)
         && (real_e1->e[0] == real_e0->e[1] || real_e1->e[0] == real_e0->e[0]);
}

static inline BzlaNode *
apply_subst1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subst1_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(
      bzla, e0, bzla_node_invert(bzla_node_real_addr(e1)->e[1]));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a & b & ~(c & d), where a = d OR b = d
 * result: a & b & ~c
 *
 * symmetric rule of substitution
 */
static inline bool
applies_subst2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_bv_and(real_e1) && !bzla_node_is_inverted(e0)
         && bzla_node_is_inverted(e1)
         && (real_e1->e[1] == real_e0->e[1] || real_e1->e[1] == real_e0->e[0]);
}

static inline BzlaNode *
apply_subst2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subst2_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(
      bzla, e0, bzla_node_invert(bzla_node_real_addr(e1)->e[0]));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a XNOR b, where len(a) = 1
 * result: a = b
 */
static inline bool
applies_bool_xnor_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_bv_and(real_e1) && bzla_node_is_inverted(e0)
         && bzla_node_is_inverted(e1)
         && bzla_node_bv_get_width(bzla, real_e0) == 1
         && bzla_node_is_inverted(real_e0->e[0])
                != bzla_node_is_inverted(real_e0->e[1])
         && bzla_node_is_inverted(real_e1->e[0])
                != bzla_node_is_inverted(real_e1->e[1])
         && ((real_e0->e[0] == bzla_node_invert(real_e1->e[0])
              && real_e0->e[1] == bzla_node_invert(real_e1->e[1]))
             || (real_e0->e[0] == bzla_node_invert(real_e1->e[1])
                 && real_e0->e[1] == bzla_node_invert(real_e1->e[0])));
}

static inline BzlaNode *
apply_bool_xnor_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_xnor_and(bzla, e0, e1));
  (void) e1;

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(bzla,
                          bzla_node_real_addr(bzla_node_real_addr(e0)->e[0]),
                          bzla_node_real_addr(bzla_node_real_addr(e0)->e[1]));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: ~(a & b) & ~(c & d), where (a = c AND b = ~d) OR (a = d AND b = ~c)
 * result: ~a
 *
 * rule of resolution
 */
static inline bool
applies_resol1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_bv_and(real_e1) && bzla_node_is_inverted(e0)
         && bzla_node_is_inverted(e1)
         && ((real_e0->e[0] == real_e1->e[0]
              && real_e0->e[1] == bzla_node_invert(real_e1->e[1]))
             || (real_e0->e[0] == real_e1->e[1]
                 && real_e0->e[1] == bzla_node_invert(real_e1->e[0])));
}

static inline BzlaNode *
apply_resol1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_resol1_and(bzla, e0, e1));
  (void) e1;
  return bzla_node_invert(bzla_node_copy(bzla, bzla_node_real_addr(e0)->e[0]));
}

/*
 * match: ~(a & b) & ~(c & d), where (~a = c AND b = d) OR (a = d AND ~b = c)
 * result: ~a
 *
 * rule of resolution
 */
static inline bool
applies_resol2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_bv_and(real_e1) && bzla_node_is_inverted(e0)
         && bzla_node_is_inverted(e1)
         && ((real_e1->e[1] == real_e0->e[1]
              && real_e1->e[0] == bzla_node_invert(real_e0->e[0]))
             || (real_e1->e[1] == real_e0->e[0]
                 && real_e1->e[0] == bzla_node_invert(real_e0->e[1])));
}

static inline BzlaNode *
apply_resol2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_resol2_and(bzla, e0, e1));
  (void) e0;
  return bzla_node_invert(bzla_node_copy(bzla, bzla_node_real_addr(e1)->e[1]));
}

/*
 * match: ~(a & b) & c, where a == ~c OR b == ~c
 * result: c
 *
 * first rule of subsumption
 */
static inline bool
applies_subsum2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla_node_is_bv_and(real_e0) && bzla_node_is_inverted(e0)
         && (real_e0->e[0] == bzla_node_invert(e1)
             || real_e0->e[1] == bzla_node_invert(e1));
}

static inline BzlaNode *
apply_subsum2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subsum2_and(bzla, e0, e1));
  (void) e0;
  return bzla_node_copy(bzla, e1);
}

/*
 * match: ~(a & b) & c, where b = c
 * result: ~a & c
 *
 * asymmetric rule of substitution
 */
static inline bool
applies_subst3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_inverted(e0) && real_e0->e[1] == e1;
}

static inline BzlaNode *
apply_subst3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subst3_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(
      bzla, bzla_node_invert(bzla_node_real_addr(e0)->e[0]), e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: ~(a & b) & c, where a = c
 * result: ~b & c
 *
 * asymmetric rule of substitution
 */
static inline bool
applies_subst4_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(real_e0)
         && bzla_node_is_inverted(e0) && real_e0->e[0] == e1;
}

static inline BzlaNode *
apply_subst4_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_subst4_and(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(
      bzla, bzla_node_invert(bzla_node_real_addr(e0)->e[1]), e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a & b & c, where a = ~c OR b = ~c
 * result: 0
 *
 * first rule of contradiction
 */
static inline bool
applies_contr3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_is_bv_and(e0) && !bzla_node_is_inverted(e0)
         && (e0->e[0] == bzla_node_invert(e1)
             || e0->e[1] == bzla_node_invert(e1));
}

static inline BzlaNode *
apply_contr3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_contr3_and(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match: a & b & c, where a = c OR b = c
 * result: a
 *
 * asymmetric rule of idempotency
 */
static inline bool
applies_idem3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_is_bv_and(e0) && !bzla_node_is_inverted(e0)
         && (e0->e[0] == e1 || e0->e[1] == e1);
}

static inline BzlaNode *
apply_idem3_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_idem3_and(bzla, e0, e1));
  (void) e1;
  return bzla_node_copy(bzla, e0);
}

/*
 * match: a & b & c, where a and c are constants
 * result: d & b, where d is a new constant obtained from a & c
 */
static inline bool
applies_const1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(e0)
         && !bzla_node_is_inverted(e0) && bzla_node_is_bv_const(e1)
         && bzla_node_is_bv_const(e0->e[0]);
}

static inline BzlaNode *
apply_const1_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const1_and(bzla, e0, e1));
  assert(!bzla_node_is_bv_const(e0->e[1]));

  BzlaNode *tmp, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_and_exp(bzla, e1, e0->e[0]);
  result = rewrite_bv_and_exp(bzla, tmp, e0->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: a & b & c, where b and c are constants
 * result: d & a, where d is a new constant obtained from b & c
 */
static inline bool
applies_const2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_and(e0)
         && !bzla_node_is_inverted(e0) && bzla_node_is_bv_const(e1)
         && bzla_node_is_bv_const(e0->e[1]);
}

static inline BzlaNode *
apply_const2_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const2_and(bzla, e0, e1));
  assert(!bzla_node_is_bv_const(e0->e[0]));

  BzlaNode *tmp, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_and_exp(bzla, e1, e0->e[1]);
  result = rewrite_bv_and_exp(bzla, tmp, e0->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: (a < b) & (b < a)
 * result: false
 */
static inline bool
applies_lt_false_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return ((bzla_node_is_bv_ult(e0) && bzla_node_is_bv_ult(e1))
          || (bzla_node_is_bv_slt(e0) && bzla_node_is_bv_slt(e1)))
         && !bzla_node_is_inverted(e0) && !bzla_node_is_inverted(e1)
         && e0->e[0] == e1->e[1] && e0->e[1] == e1->e[0];
}

static inline BzlaNode *
apply_lt_false_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_lt_false_and(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_false(bzla);
}

/*
 * match: ~(a < b) & ~(b < a)
 * result: a = b
 */
static inline bool
applies_lt_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && ((bzla_node_is_bv_ult(real_e0) && bzla_node_is_bv_ult(real_e1))
             || (bzla_node_is_bv_slt(real_e0) && bzla_node_is_bv_slt(real_e1)))
         && bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1)
         && real_e0->e[0] == real_e1->e[1] && real_e0->e[1] == real_e1->e[0];
}

static inline BzlaNode *
apply_lt_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_lt_and(bzla, e0, e1));
  (void) e1;

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_eq_exp(
      bzla, bzla_node_real_addr(e0)->e[0], bzla_node_real_addr(e0)->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * recursively find contradicting ands
 */
static inline bool
applies_contr_rec_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  uint32_t calls = 0;
  return find_and_contradiction_exp(bzla, e0, e0, e1, &calls)
         || find_and_contradiction_exp(bzla, e1, e0, e1, &calls);
}

static inline BzlaNode *
apply_contr_rec_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_contr_rec_and(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match:  (0::a) & (b::0)
 * result: 0
 *
 * match:  (0::a) & (b::1)
 * result: 0::a
 *
 * match: (1::a) & (b::1)
 * result: b::a
 */
static inline bool
applies_concat_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool result;
  BzlaNode *real_e0, *real_e1, *e00, *e01, *e10, *e11;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  result = bzla->rec_rw_calls < BZLA_REC_RW_BOUND
           && bzla_node_is_bv_concat(real_e0) && bzla_node_is_bv_concat(real_e1)
           && bzla_node_get_sort_id(real_e0->e[0])
                  == bzla_node_get_sort_id(real_e1->e[0]);

  if (!result) return result;

  e00 = bzla_node_cond_invert(e0, real_e0->e[0]);
  e01 = bzla_node_cond_invert(e0, real_e0->e[1]);
  e10 = bzla_node_cond_invert(e1, real_e1->e[0]);
  e11 = bzla_node_cond_invert(e1, real_e1->e[1]);
  return ((is_bv_const_zero_or_ones_exp(bzla, e00)
           && is_bv_const_zero_or_ones_exp(bzla, e11))
          || (is_bv_const_zero_or_ones_exp(bzla, e01)
              && is_bv_const_zero_or_ones_exp(bzla, e10)));
}

static inline BzlaNode *
apply_concat_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_concat_and(bzla, e0, e1));

  BzlaNode *real_e0, *real_e1, *e00, *e01, *e10, *e11, *left, *right, *result;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  e00     = bzla_node_cond_invert(e0, real_e0->e[0]);
  e01     = bzla_node_cond_invert(e0, real_e0->e[1]);
  e10     = bzla_node_cond_invert(e1, real_e1->e[0]);
  e11     = bzla_node_cond_invert(e1, real_e1->e[1]);

  BZLA_INC_REC_RW_CALL(bzla);
  left   = bzla_exp_bv_and(bzla, e00, e10);
  right  = bzla_exp_bv_and(bzla, e01, e11);
  result = rewrite_bv_concat_exp(bzla, left, right);
  bzla_node_release(bzla, right);
  bzla_node_release(bzla, left);
  BZLA_DEC_REC_RW_CALL(bzla);

  return result;
}

static inline bool
applies_push_ite_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(e0)
         && (bzla_node_is_bv_const_zero(bzla, bzla_node_real_addr(e0)->e[1])
             || bzla_node_is_bv_const_zero(bzla,
                                           bzla_node_real_addr(e0)->e[2]));
}

static inline BzlaNode *
apply_push_ite_and(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_push_ite_and(bzla, e0, e1));

  BzlaNode *result, *and_left, *and_right, *real_e0;

  real_e0 = bzla_node_real_addr(e0);
  BZLA_INC_REC_RW_CALL(bzla);
  and_left =
      rewrite_bv_and_exp(bzla, bzla_node_cond_invert(e0, real_e0->e[1]), e1);
  and_right =
      rewrite_bv_and_exp(bzla, bzla_node_cond_invert(e0, real_e0->e[2]), e1);

  result = rewrite_cond_exp(bzla, real_e0->e[0], and_left, and_right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, and_left);
  bzla_node_release(bzla, and_right);
  return result;
}

#if 0
/*
 * match:
 * result:
 */
static inline bool
applies_and (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && !bzla_node_is_inverted (e0)
	 && bzla_node_is_bv_cond (e0);
}

static inline BzlaNode * 
apply_and (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_and (bzla, e0, e1));

}

// TODO (ma): uses shallow substitute, which does not really work
  if (!bzla_node_is_inverted (e0) &&
      e0->kind == BZLA_BV_EQ_NODE &&
      bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
    {
      BzlaNode * e1_simp = condrewrite (bzla, e1, e0);
      if (e1_simp != e1)
	{
	  BZLA_INC_REC_RW_CALL (bzla);
	  result = rewrite_bv_and_exp (bzla, e0, e1_simp);
	  BZLA_DEC_REC_RW_CALL (bzla);
	}
      else
	result = 0;
      bzla_node_release (bzla, e1_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }

  if (!bzla_node_is_inverted (e1) &&
      e1->kind == BZLA_BV_EQ_NODE &&
      bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
    {
      BzlaNode * e0_simp = condrewrite (bzla, e0, e1);
      if (e0_simp != e0)
	{
	  BZLA_INC_REC_RW_CALL (bzla);
	  result = rewrite_bv_and_exp (bzla, e0_simp, e1);
	  BZLA_DEC_REC_RW_CALL (bzla);
	}
      else
	result = 0;
      bzla_node_release (bzla, e0_simp);
      if (result)
	{
	  assert (!normalized);
	  return result;
	}
    }
#endif

/* ADD rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a + b, where len(a) = 1
 * result: a XOR b
 */
static inline bool
applies_bool_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_add(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = bzla_exp_bv_xor(bzla, e0, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a - b OR -a + b, where a = b
 * result: 0
 */
static inline bool
applies_neg_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return !bzla_node_is_inverted(e1) && bzla_node_is_bv_add(e1)
         && ((e0 == bzla_node_invert(e1->e[0])
              && bzla_node_is_bv_const_one(bzla, e1->e[1]))
             || (e0 == bzla_node_invert(e1->e[1])
                 && bzla_node_is_bv_const_one(bzla, e1->e[0])));
}

static inline BzlaNode *
apply_neg_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_neg_add(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match: 0 + b
 * result: b
 */
static inline bool
applies_zero_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return is_const_zero_exp(bzla, e0);
}

static inline BzlaNode *
apply_zero_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_zero_add(bzla, e0, e1));
  (void) e0;
  return bzla_node_copy(bzla, e1);
}

/*
 * match: c0 + (c1 + b), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline bool
applies_const_lhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_add(e1)
         && bzla_node_is_bv_const(e1->e[0]);
}

static inline BzlaNode *
apply_const_lhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_lhs_add(bzla, e0, e1));
  assert(!bzla_node_is_bv_const(e1->e[1]));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_add_exp(bzla, e0, e1->e[0]);
  result = rewrite_bv_add_exp(bzla, tmp, e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 + (b + c1), where c0 and c1 are constants
 * result: c + b, where c is a new constant from c0 + c1
 *
 * recursion is no problem here, as one call leads to
 * folding of constants, and the other call can not
 * trigger the same kind of recursion anymore.
 */
static inline bool
applies_const_rhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_add(e1)
         && bzla_node_is_bv_const(e1->e[1]);
}

static inline BzlaNode *
apply_const_rhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_rhs_add(bzla, e0, e1));
  assert(!bzla_node_is_bv_const(e1->e[0]));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_add_exp(bzla, e0, e1->e[1]);
  result = rewrite_bv_add_exp(bzla, tmp, e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

#if 0
  // TODO: problematic as long we do not do 'addneg normalization'
  //
  // e0 + e1 == ~(e00 + e01) + e1
  //         == (-(e00 + e01) -1) + e1
  //         == - e00 - e01 - 1 + e1
  //         == (~e00 + 1) + (~e01 + 1) - 1 + e1
  //         == ((~e00 + ~e01) + 1) + e1
  //
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla_node_is_inverted (e0) &&
      bzla->rec_rw_calls < BZLA_REC_RW_BOUND &&
      (temp = bzla_node_real_addr (e0))->kind == BZLA_BV_ADD_NODE)
    {
      BzlaNode * e00 = temp->e[0];
      BzlaNode * e01 = temp->e[1];
      BzlaNode * one, * sum;
      BZLA_INC_REC_RW_CALL (bzla);
      one = bzla_exp_bv_one (bzla, bzla_node_get_sort_id (temp));
      temp = bzla_exp_bv_add (bzla,
        bzla_node_invert (e00), bzla_node_invert (e01));
      sum = bzla_exp_bv_add (bzla, temp, one);
      result = bzla_exp_bv_add (bzla, sum, e1);
      BZLA_DEC_REC_RW_CALL (bzla);
      bzla_node_release (bzla, sum);
      bzla_node_release (bzla, temp);
      bzla_node_release (bzla, one);
      return result;
    }

  // TODO: problematic as long we do not do 'addneg normalization'
  //
  // e0 + e1 == e0 + ~(e10 + e11)
  //         == e0 + (-(e10 + e11) -1)
  //         == e0 - e10 - e11 - 1
  //         == e0 + (~e10 + 1) + (~e11 + 1) - 1
  //         == e0 + ((~e10 + ~e11) + 1)
  //
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla_node_is_inverted (e1) &&
      bzla->rec_rw_calls < BZLA_REC_RW_BOUND &&
      (temp = bzla_node_real_addr (e1))->kind == BZLA_BV_ADD_NODE)
    {
      BzlaNode * e10 = temp->e[0];
      BzlaNode * e11 = temp->e[1];
      BzlaNode * one, * sum;
      BZLA_INC_REC_RW_CALL (bzla);
      one = bzla_exp_bv_one (bzla, bzla_node_get_sort_id (temp));
      temp = bzla_exp_bv_add (bzla, 
        bzla_node_invert (e10), bzla_node_invert (e11));
      sum = bzla_exp_bv_add (bzla, temp, one);
      result = bzla_exp_bv_add (bzla, e0, sum);
      BZLA_DEC_REC_RW_CALL (bzla);
      bzla_node_release (bzla, sum);
      bzla_node_release (bzla, temp);
      bzla_node_release (bzla, one);
      return result;
    }
#endif

/*
 * match:  ~(c * a) + b
 * result: ((-c) * a - 1) + b
 */
static inline bool
applies_const_neg_lhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_inverted(e0)
         && bzla_node_is_bv_mul(real_e0)
         && bzla_node_is_bv_const(real_e0->e[0]);
}

static inline BzlaNode *
apply_const_neg_lhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_neg_lhs_add(bzla, e0, e1));

  BzlaNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = bzla_node_real_addr(e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BZLA_INC_REC_RW_CALL(bzla);
  n00    = bzla_exp_bv_neg(bzla, e00);
  n01    = bzla_node_copy(bzla, e01);
  one    = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(real_e0));
  tmp    = rewrite_bv_mul_exp(bzla, n00, n01);
  sum    = bzla_exp_bv_sub(bzla, tmp, one);
  result = rewrite_bv_add_exp(bzla, sum, e1);
  bzla_node_release(bzla, sum);
  bzla_node_release(bzla, tmp);
  bzla_node_release(bzla, one);
  bzla_node_release(bzla, n00);
  bzla_node_release(bzla, n01);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  ~(a * c) + b
 * result: (a * (-c) - 1) + b
 */
static inline bool
applies_const_neg_rhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_inverted(e0)
         && bzla_node_is_bv_mul(real_e0)
         && bzla_node_is_bv_const(real_e0->e[1]);
}

static inline BzlaNode *
apply_const_neg_rhs_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_neg_rhs_add(bzla, e0, e1));

  BzlaNode *result, *real_e0, *e00, *e01, *n00, *n01, *one, *sum, *tmp;

  real_e0 = bzla_node_real_addr(e0);
  e00     = real_e0->e[0];
  e01     = real_e0->e[1];

  BZLA_INC_REC_RW_CALL(bzla);
  n00    = bzla_node_copy(bzla, e00);
  n01    = bzla_exp_bv_neg(bzla, e01);
  one    = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(real_e0));
  tmp    = rewrite_bv_mul_exp(bzla, n00, n01);
  sum    = bzla_exp_bv_sub(bzla, tmp, one);
  result = rewrite_bv_add_exp(bzla, sum, e1);
  bzla_node_release(bzla, sum);
  bzla_node_release(bzla, tmp);
  bzla_node_release(bzla, one);
  bzla_node_release(bzla, n00);
  bzla_node_release(bzla, n01);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  (a + (b << a))
 * result: (a | (b << a))
 */
static inline bool
applies_sll_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && bzla_node_is_bv_sll(e1) && e0 == e1->e[1];
}

static inline BzlaNode *
apply_sll_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_sll_add(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = bzla_node_invert(
      rewrite_bv_and_exp(bzla, bzla_node_invert(e0), bzla_node_invert(e1)));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a + (a * b)
 * result: (a * (b + 1))
 */
static inline bool
applies_mul_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && bzla_node_is_bv_mul(e1) && (e1->e[0] == e0 || e1->e[1] == e0);
}

static inline BzlaNode *
apply_mul_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_mul_add(bzla, e0, e1));

  BzlaNode *result, *b, *b_inc;

  b = e1->e[0] == e0 ? e1->e[1] : e1->e[0];

  BZLA_INC_REC_RW_CALL(bzla);

  b_inc  = bzla_exp_bv_inc(bzla, b);
  result = rewrite_bv_mul_exp(bzla, e0, b_inc);
  bzla_node_release(bzla, b_inc);

  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

static inline bool
applies_push_ite_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(e0)
         && !bzla_node_is_inverted(e0)
         && (bzla_node_is_bv_const_zero(bzla, e0->e[1])
             || bzla_node_is_bv_const_zero(bzla, e0->e[2]));
}

static inline BzlaNode *
apply_push_ite_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_push_ite_add(bzla, e0, e1));

  BzlaNode *result, *add_left, *add_right;

  BZLA_INC_REC_RW_CALL(bzla);
  add_left  = rewrite_bv_add_exp(bzla, e0->e[1], e1);
  add_right = rewrite_bv_add_exp(bzla, e0->e[2], e1);

  assert(add_left == e1 || add_right == e1);

  result = rewrite_cond_exp(bzla, e0->e[0], add_left, add_right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, add_left);
  bzla_node_release(bzla, add_right);
  return result;
}

/*
 * match:  a + a
 * result: 2 * a
 */
static inline bool
applies_mult_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && e0 == e1
         && bzla_node_bv_get_width(bzla, e0) >= 2;
}

static inline BzlaNode *
apply_mult_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_mult_add(bzla, e0, e1));
  (void) e1;

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = bzla_exp_bv_int(bzla, 2, bzla_node_get_sort_id(e0));
  result = rewrite_bv_mul_exp(bzla, e0, tmp);
  bzla_node_release(bzla, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a + ~a
 * result: -1
 */
static inline bool
applies_not_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_real_addr(e0) == bzla_node_real_addr(e1) && e0 != e1;
}

static inline BzlaNode *
apply_not_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_not_add(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(e0));
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/*
 * match:  (x ? a : b) + (x : c : d), where either a = c or b = d
 * result: x ? a + c : b + d
 */
static inline bool
applies_bcond_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(real_e0)
         && bzla_node_is_bv_cond(real_e1)
         && bzla_node_is_inverted(e0)
                == bzla_node_is_inverted(e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode *
apply_bcond_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_add(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_add_exp(bzla,
                            bzla_node_cond_invert(e0, real_e0->e[1]),
                            bzla_node_cond_invert(e1, real_e1->e[1]));
  right  = rewrite_bv_add_exp(bzla,
                             bzla_node_cond_invert(e0, real_e0->e[2]),
                             bzla_node_cond_invert(e1, real_e1->e[2]));
  result = rewrite_cond_exp(bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

static inline bool
applies_urem_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return is_urem_exp(bzla, e0, e1, 0, 0);
}

static inline BzlaNode *
apply_urem_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_urem_add(bzla, e0, e1));

  BzlaNode *x, *y;
  is_urem_exp(bzla, e0, e1, &x, &y);
  return rewrite_bv_urem_exp(bzla, x, y);
}

/* MUL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a * b, wher len(a) = 1
 * result: a & b
 */
static inline bool
applies_bool_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_mul(bzla, e0, e1));

  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, e0, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: c0 * (c1 * b), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_lhs_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_mul(e1)
         && bzla_node_is_bv_const(e1->e[0]);
}

static inline BzlaNode *
apply_const_lhs_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_lhs_mul(bzla, e0, e1));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_mul_exp(bzla, e0, e1->e[0]);
  result = rewrite_bv_mul_exp(bzla, tmp, e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 * (b * c1), where c0 and c1 are constants
 * result: c * b, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_rhs_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_mul(e1)
         && bzla_node_is_bv_const(e1->e[1]);
}

static inline BzlaNode *
apply_const_rhs_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_rhs_mul(bzla, e0, e1));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_mul_exp(bzla, e0, e1->e[1]);
  result = rewrite_bv_mul_exp(bzla, tmp, e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 * (a + c1)
 * result: c0 * a + c, where c is a new constant from c0 * c1
 */
static inline bool
applies_const_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e0)
         && !bzla_node_is_inverted(e1) && bzla_node_is_bv_add(e1)
         && (bzla_node_is_bv_const(e1->e[0])
             || bzla_node_is_bv_const(e1->e[1]));
}

static inline BzlaNode *
apply_const_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_mul(bzla, e0, e1));

  BzlaNode *result, *left, *right;

  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_mul_exp(bzla, e0, e1->e[0]);
  right  = rewrite_bv_mul_exp(bzla, e0, e1->e[1]);
  result = rewrite_bv_add_exp(bzla, left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

/*
 *
 *
 */
static inline bool
applies_push_ite_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(e0)
         && !bzla_node_is_inverted(e0)
         && (bzla_node_is_bv_const_zero(bzla, e0->e[1])
             || bzla_node_is_bv_const_zero(bzla, e0->e[2]));
}

static inline BzlaNode *
apply_push_ite_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_push_ite_mul(bzla, e0, e1));

  BzlaNode *result, *mul_left, *mul_right;

  BZLA_INC_REC_RW_CALL(bzla);
  mul_left  = rewrite_bv_mul_exp(bzla, e0->e[1], e1);
  mul_right = rewrite_bv_mul_exp(bzla, e0->e[2], e1);

  assert(bzla_node_is_bv_const_zero(bzla, mul_left)
         || bzla_node_is_bv_const_zero(bzla, mul_right));

  result = rewrite_cond_exp(bzla, e0->e[0], mul_left, mul_right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, mul_left);
  bzla_node_release(bzla, mul_right);
  return result;
}

static inline bool
applies_sll_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_sll(e0)
         && !bzla_node_is_inverted(e0);
}

static inline BzlaNode *
apply_sll_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_sll_mul(bzla, e0, e1));

  BzlaNode *result, *mul;

  BZLA_INC_REC_RW_CALL(bzla);
  mul    = rewrite_bv_mul_exp(bzla, e0->e[0], e1);
  result = rewrite_bv_sll_exp(bzla, mul, e0->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, mul);
  return result;
}

static inline bool
applies_neg_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && (bzla_node_bv_is_neg(bzla, e0, 0)
             || bzla_node_bv_is_neg(bzla, e1, 0));
}

static inline BzlaNode *
apply_neg_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_neg_mul(bzla, e0, e1));

  bool is_neg0, is_neg1;
  BzlaNode *result, *tmp, *a, *b;

  is_neg0 = bzla_node_bv_is_neg(bzla, e0, &a);
  is_neg1 = bzla_node_bv_is_neg(bzla, e1, &b);

  BZLA_INC_REC_RW_CALL(bzla);
  if (is_neg0 && is_neg1)
  {
    result = rewrite_bv_mul_exp(bzla, a, b);
  }
  else if (is_neg0)
  {
    tmp    = rewrite_bv_mul_exp(bzla, a, e1);
    result = bzla_exp_bv_neg(bzla, tmp);
    bzla_node_release(bzla, tmp);
  }
  else
  {
    assert(is_neg1);
    tmp    = rewrite_bv_mul_exp(bzla, e0, b);
    result = bzla_exp_bv_neg(bzla, tmp);
    bzla_node_release(bzla, tmp);
  }
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

static inline bool
applies_ones_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && (bzla_node_is_bv_const_ones(bzla, e0)
             || bzla_node_is_bv_const_ones(bzla, e1));
}

static inline BzlaNode *
apply_ones_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_ones_mul(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  if (bzla_node_is_bv_const_ones(bzla, e0))
  {
    result = bzla_exp_bv_neg(bzla, e1);
  }
  else
  {
    result = bzla_exp_bv_neg(bzla, e0);
  }
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

#if 0
  // TODO: why should we disable this?
  //
  if (bzla->rec_rw_calls < BZLA_REC_RW_BOUND)
    {
      if (is_const_ones_exp (bzla, e0))
	result = e1;
      else
      if (is_const_ones_exp (bzla, e1))
	result = e0;
      else
	result = 0;
	
      if (result)
	{
	  BzlaNode * tmp, * one = bzla_exp_bv_one (bzla, bzla_node_get_sort_id (result));
	  BZLA_INC_REC_RW_CALL (bzla);
	  tmp = bzla_exp_bv_add (bzla, bzla_node_invert (result), one);
	  BZLA_DEC_REC_RW_CALL (bzla);
	  bzla_node_release (bzla, one);
	  result = tmp;
	  goto HAVE_RESULT_BUT_MIGHT_NEED_TO_RELEASE_SOMETHING;
	}
    }
#endif

#if 0
// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/* match:  (x ? a : b) * (x : c : d), where either a = c or b = d
 * result: x ? a * c : b * d 
 */
static inline bool
applies_bcond_mul (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr (e0);
  real_e1 = bzla_node_real_addr (e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
	 && bzla_node_is_bv_cond (real_e0)
	 && bzla_node_is_bv_cond (real_e1)
	 && bzla_node_is_inverted (e0) == bzla_node_is_inverted (e1) // TODO: needed?
	 && real_e0->e[0] == real_e1->e[0]
	 && (real_e0->e[1] == real_e1->e[1]
	     || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode * 
apply_bcond_mul (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  assert (applies_bcond_mul (bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr (e0);
  real_e1 = bzla_node_real_addr (e1);
  BZLA_INC_REC_RW_CALL (bzla);
  left = rewrite_bv_mul_exp (bzla,
			  bzla_node_cond_invert (e0, real_e0->e[1]),
			  bzla_node_cond_invert (e1, real_e1->e[1]));
  right = rewrite_bv_mul_exp (bzla,
			   bzla_node_cond_invert (e0, real_e0->e[2]),
			   bzla_node_cond_invert (e1, real_e1->e[2]));
  result = rewrite_cond_exp (bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL (bzla);
  bzla_node_release (bzla, left);
  bzla_node_release (bzla, right);
  return result;
}
#endif

/* UDIV rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match: a / b, where len(a) = 1
 * result: ~(~a & b)
 */
static inline bool
applies_bool_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_udiv(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = bzla_node_invert(rewrite_bv_and_exp(bzla, bzla_node_invert(e0), e1));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a / 2^n
 * result: 0 :: a[len(a)-1:n]
 */
static inline bool
applies_power2_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e0;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && bzla_node_is_bv_const(e1)
         && bzla_bv_power_of_two(bzla_node_bv_const_get_bits(e1)) > 0;
}

static inline BzlaNode *
apply_power2_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_power2_udiv(bzla, e0, e1));
  assert(bzla_node_is_regular(e1));

  uint32_t l, n;
  BzlaNode *slice, *pad, *result;
  BzlaSortId sort;

  n = bzla_bv_power_of_two(bzla_node_bv_const_get_bits(e1));
  l = bzla_node_bv_get_width(bzla, e0);
  assert(l > n);

  BZLA_INC_REC_RW_CALL(bzla);
  slice = rewrite_bv_slice_exp(bzla, e0, l - 1, n);
  sort  = bzla_sort_bv(bzla, n);
  pad   = bzla_exp_bv_zero(bzla, sort);
  bzla_sort_release(bzla, sort);
  result = rewrite_bv_concat_exp(bzla, pad, slice);
  BZLA_DEC_REC_RW_CALL(bzla);
  assert(bzla_node_bv_get_width(bzla, result) == l);
  bzla_node_release(bzla, pad);
  bzla_node_release(bzla, slice);
  return result;
}

/*
 * match: a / a
 * result: 1, if a != 0 and UINT32_MAX otherwise
 */
static inline bool
applies_one_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && e0 == e1;
}

static inline BzlaNode *
apply_one_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_one_udiv(bzla, e0, e1));
  (void) e1;

  BzlaNode *result, *tmp1, *tmp2, *tmp3, *eq, *real_e0;

  real_e0 = bzla_node_real_addr(e0);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp1   = bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(real_e0));
  tmp2   = bzla_exp_bv_one(bzla, bzla_node_get_sort_id(real_e0));
  tmp3   = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(real_e0));
  eq     = rewrite_eq_exp(bzla, e0, tmp1);
  result = rewrite_cond_exp(bzla, eq, tmp3, tmp2);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, eq);
  bzla_node_release(bzla, tmp1);
  bzla_node_release(bzla, tmp2);
  bzla_node_release(bzla, tmp3);
  return result;
}

// TODO (ma): conditional rewriting: check if a and c or b and d are constants
/*
 * match:  (x ? a : b) / (x : c : d), where either a = c or b = d
 * result: x ? a / c : b / d
 */
static inline bool
applies_bcond_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_cond(real_e0)
         && bzla_node_is_bv_cond(real_e1)
         && bzla_node_is_inverted(e0)
                == bzla_node_is_inverted(e1)  // TODO: needed?
         && real_e0->e[0] == real_e1->e[0]
         && (real_e0->e[1] == real_e1->e[1] || real_e0->e[2] == real_e1->e[2]);
}

static inline BzlaNode *
apply_bcond_udiv(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bcond_udiv(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0, *real_e1;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left   = rewrite_bv_udiv_exp(bzla,
                             bzla_node_cond_invert(e0, real_e0->e[1]),
                             bzla_node_cond_invert(e1, real_e1->e[1]));
  right  = rewrite_bv_udiv_exp(bzla,
                              bzla_node_cond_invert(e0, real_e0->e[2]),
                              bzla_node_cond_invert(e1, real_e1->e[2]));
  result = rewrite_cond_exp(bzla, real_e0->e[0], left, right);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, left);
  bzla_node_release(bzla, right);
  return result;
}

/* UREM rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match:  a % b, where len(a) = 1
 * result: a & ~b
 */
static inline bool
applies_bool_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_bv_get_width(bzla, e0) == 1;
}

static inline BzlaNode *
apply_bool_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_bool_urem(bzla, e0, e1));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_and_exp(bzla, e0, bzla_node_invert(e1));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a % a
 * result: 0
 */
static inline bool
applies_zero_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_zero_urem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_zero_urem(bzla, e0, e1));
  (void) e1;
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/* CONCAT rules                                                               */
/* -------------------------------------------------------------------------- */

/*
 * match:  (a::c0)::c1
 * result: a::c, where c is a new constant obtained from c0::c1
 */
static inline bool
applies_const_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e1)
         && bzla_node_is_bv_concat(real_e0)
         && bzla_node_is_bv_const(real_e0->e[1]);
}

static inline BzlaNode *
apply_const_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_concat(bzla, e0, e1));

  BzlaNode *result, *tmp, *real_e0;

  real_e0 = bzla_node_real_addr(e0);

  BZLA_INC_REC_RW_CALL(bzla);
  tmp =
      rewrite_bv_concat_exp(bzla, bzla_node_cond_invert(e0, real_e0->e[1]), e1);
  result = rewrite_bv_concat_exp(
      bzla, bzla_node_cond_invert(e0, real_e0->e[0]), tmp);
  bzla_node_release(bzla, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  a[u1:l1]::a[u2:l2], where l1 = u2 + 1
 * result: a[u1:l2]
 */
static inline bool
applies_slice_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *real_e0, *real_e1;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_is_inverted(e0) == bzla_node_is_inverted(e1)
         && bzla_node_is_bv_slice(real_e0) && bzla_node_is_bv_slice(real_e1)
         && real_e0->e[0] == real_e1->e[0]
         && bzla_node_bv_slice_get_lower(real_e0)
                == bzla_node_bv_slice_get_upper(real_e1) + 1;
}

static inline BzlaNode *
apply_slice_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_slice_concat(bzla, e0, e1));

  BzlaNode *result, *real_e0;

  real_e0 = bzla_node_real_addr(e0);
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_slice_exp(bzla,
                                real_e0->e[0],
                                bzla_node_bv_slice_get_upper(real_e0),
                                bzla_node_bv_slice_get_lower(e1));
  BZLA_DEC_REC_RW_CALL(bzla);
  result = bzla_node_cond_invert(e0, result);
  return result;
}

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      !bzla_node_is_inverted (e0) &&
      e0->kind == BZLA_BCOND_NODE &&
      (bzla_is_concat_simplifiable (e0->e[1]) ||
       bzla_is_concat_simplifiable (e0->e[2])))
    {
      BZLA_INC_REC_RW_CALL (bzla);
      t = bzla_exp_bv_concat (bzla, e0->e[1], e1);
      e = bzla_exp_bv_concat (bzla, e0->e[2], e1);
      result = bzla_exp_cond (bzla, e0->e[0], t, e);
      bzla_node_release (bzla, e);
      bzla_node_release (bzla, t);
      BZLA_DEC_REC_RW_CALL (bzla);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla_node_is_inverted (e0) &&
      (real_e0 = bzla_node_real_addr (e0))->kind == BZLA_BCOND_NODE &&
      (bzla_is_concat_simplifiable (real_e0->e[1]) ||
       bzla_is_concat_simplifiable (real_e0->e[2])))
    {
      BZLA_INC_REC_RW_CALL (bzla);
      t = bzla_exp_bv_concat (bzla, bzla_node_invert (real_e0->e[1]), e1);
      e = bzla_exp_bv_concat (bzla, bzla_node_invert (real_e0->e[2]), e1);
      result = bzla_exp_cond (bzla, real_e0->e[0], t, e);
      bzla_node_release (bzla, e);
      bzla_node_release (bzla, t);
      BZLA_DEC_REC_RW_CALL (bzla);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      !bzla_node_is_inverted (e1) &&
      e1->kind == BZLA_BCOND_NODE &&
      (bzla_is_concat_simplifiable (e1->e[1]) ||
       bzla_is_concat_simplifiable (e1->e[2])))
    {
      BZLA_INC_REC_RW_CALL (bzla);
      t = bzla_exp_bv_concat (bzla, e0, e1->e[1]);
      e = bzla_exp_bv_concat (bzla, e0, e1->e[2]);
      result = bzla_exp_cond (bzla, e1->e[0], t, e);
      bzla_node_release (bzla, e);
      bzla_node_release (bzla, t);
      BZLA_DEC_REC_RW_CALL (bzla);
      return result;
    }
#endif

// NOTE: disabled for now, conflicts with rewriting rule of cond
#if 0
  if (bzla_opt_get (bzla, BZLA_OPT_RW_LEVEL) > 2 &&
      bzla_node_is_inverted (e1) &&
      (real_e1 = bzla_node_real_addr (e1))->kind == BZLA_BCOND_NODE &&
      (bzla_is_concat_simplifiable (real_e1->e[1]) ||
       bzla_is_concat_simplifiable (real_e1->e[2])))
    {
      BZLA_INC_REC_RW_CALL (bzla);
      t = bzla_exp_bv_concat (bzla, e0, bzla_node_invert (real_e1->e[1]));
      e = bzla_exp_bv_concat (bzla, e0, bzla_node_invert (real_e1->e[2]));
      result = bzla_exp_cond (bzla, real_e1->e[0], t, e);
      bzla_node_release (bzla, e);
      bzla_node_release (bzla, t);
      BZLA_DEC_REC_RW_CALL (bzla);
      return result;
    }
#endif

/*
 * match: (a & b)::c
 * result: (a::c) & (b::c)
 */
static inline bool
applies_and_lhs_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  BzlaNode *real_e0;
  real_e0 = bzla_node_real_addr(e0);
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_is_bv_and(real_e0)
         && (is_concat_simplifiable(real_e0->e[0])
             || is_concat_simplifiable(real_e0->e[1]));
}

static inline BzlaNode *
apply_and_lhs_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_and_lhs_concat(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e0;

  real_e0 = bzla_node_real_addr(e0);
  BZLA_INC_REC_RW_CALL(bzla);
  left =
      rewrite_bv_concat_exp(bzla, real_e0->e[0], bzla_node_cond_invert(e0, e1));
  right =
      rewrite_bv_concat_exp(bzla, real_e0->e[1], bzla_node_cond_invert(e0, e1));
  result = bzla_exp_bv_and(bzla, left, right);
  result = bzla_node_cond_invert(e0, result);
  bzla_node_release(bzla, right);
  bzla_node_release(bzla, left);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: a::(b & c)
 * result: (a::b) & (a::c)
 */
static inline bool
applies_and_rhs_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e0;
  BzlaNode *real_e1;
  real_e1 = bzla_node_real_addr(e1);
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && bzla_node_is_bv_and(real_e1)
         && (is_concat_simplifiable(real_e1->e[0])
             || is_concat_simplifiable(real_e1->e[1]));
}

static inline BzlaNode *
apply_and_rhs_concat(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_and_rhs_concat(bzla, e0, e1));

  BzlaNode *result, *left, *right, *real_e1;

  real_e1 = bzla_node_real_addr(e1);
  BZLA_INC_REC_RW_CALL(bzla);
  left =
      rewrite_bv_concat_exp(bzla, bzla_node_cond_invert(e1, e0), real_e1->e[0]);
  right =
      rewrite_bv_concat_exp(bzla, bzla_node_cond_invert(e1, e0), real_e1->e[1]);
  result = bzla_exp_bv_and(bzla, left, right);
  result = bzla_node_cond_invert(e1, result);
  bzla_node_release(bzla, right);
  bzla_node_release(bzla, left);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/* SLL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a << c, where c is a constant
 * result: a[len(a)-val(c)-1:0]::0
 */
static inline bool
applies_const_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e0;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e1)
         && bzla_node_bv_get_width(bzla, e1) <= 32;
}

static inline BzlaNode *
apply_const_sll(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_sll(bzla, e0, e1));

  uint32_t shiftlen, width;
  BzlaBitVector *bits;
  BzlaNode *result, *real_e0, *real_e1, *pad, *slice;
  BzlaSortId sort;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  if (is_const_zero_exp(bzla, e1)) return bzla_node_copy(bzla, e0);

  bits  = bzla_node_bv_const_get_bits(real_e1);
  width = bzla_node_bv_get_width(bzla, real_e0);
  assert(bzla_bv_get_width(bits) == width);
  if (bzla_node_is_inverted(e1)) bits = bzla_bv_not(bzla->mm, bits);
  shiftlen = (uint32_t) bzla_bv_to_uint64(bits);
  assert(shiftlen > 0);
  if (bzla_node_is_inverted(e1)) bzla_bv_free(bzla->mm, bits);
  if (shiftlen >= width)
  {
    sort   = bzla_sort_bv(bzla, width);
    result = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
  }
  else
  {
    BZLA_INC_REC_RW_CALL(bzla);
    sort = bzla_sort_bv(bzla, shiftlen);
    pad  = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
    slice = rewrite_bv_slice_exp(
        bzla, e0, bzla_node_bv_get_width(bzla, real_e0) - shiftlen - 1, 0);
    result = rewrite_bv_concat_exp(bzla, slice, pad);
    BZLA_DEC_REC_RW_CALL(bzla);
    bzla_node_release(bzla, pad);
    bzla_node_release(bzla, slice);
  }
  assert(bzla_node_get_sort_id(result) == bzla_node_get_sort_id(real_e0));
  return result;
}

/* SRL rules                                                                  */
/* -------------------------------------------------------------------------- */

/*
 * match:  a >> c, where c is a constant
 * result: 0::a[len(a)-1:val(c)]
 */
static inline bool
applies_const_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e0;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_const(e1)
         && bzla_node_bv_get_width(bzla, e1) <= 32;
}

static inline BzlaNode *
apply_const_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_srl(bzla, e0, e1));

  uint32_t width, shiftlen;
  BzlaBitVector *bits;
  BzlaNode *result, *real_e0, *real_e1, *pad, *slice;
  BzlaSortId sort;

  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  if (is_const_zero_exp(bzla, e1)) return bzla_node_copy(bzla, e0);

  bits  = bzla_node_bv_const_get_bits(real_e1);
  width = bzla_node_bv_get_width(bzla, real_e0);
  assert(bzla_bv_get_width(bits) == width);
  if (bzla_node_is_inverted(e1)) bits = bzla_bv_not(bzla->mm, bits);
  shiftlen = (uint32_t) bzla_bv_to_uint64(bits);
  assert(shiftlen > 0);
  if (bzla_node_is_inverted(e1)) bzla_bv_free(bzla->mm, bits);
  if (shiftlen >= width)
  {
    sort   = bzla_sort_bv(bzla, width);
    result = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
  }
  else
  {
    BZLA_INC_REC_RW_CALL(bzla);
    sort = bzla_sort_bv(bzla, shiftlen);
    pad  = bzla_exp_bv_zero(bzla, sort);
    bzla_sort_release(bzla, sort);
    slice = rewrite_bv_slice_exp(
        bzla, e0, bzla_node_bv_get_width(bzla, real_e0) - 1, shiftlen);
    result = rewrite_bv_concat_exp(bzla, pad, slice);
    BZLA_DEC_REC_RW_CALL(bzla);
    bzla_node_release(bzla, pad);
    bzla_node_release(bzla, slice);
  }
  assert(bzla_node_get_sort_id(result) == bzla_node_get_sort_id(real_e0));
  return result;
}

/*
 * e0 >> e0 == 0
 * match:  e0_[bw] == e1_[bw]
 * result: 0_[bw]
 */
static inline bool
applies_same_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_same_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  assert(applies_same_srl(bzla, e0, e1));
  return bzla_exp_bv_zero(bzla, bzla_node_get_sort_id(e0));
}

/*
 * match:  ~a >> a
 * result: ones >> a
 */
static inline bool
applies_not_same_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return !bzla_node_is_inverted(e1) && bzla_node_invert(e0) == e1;
}

static inline BzlaNode *
apply_not_same_srl(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  assert(applies_not_same_srl(bzla, e0, e1));
  BzlaNode *result, *ones;

  ones = bzla_exp_bv_ones(bzla, bzla_node_get_sort_id(e0));
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_bv_srl_exp(bzla, ones, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, ones);
  return result;
}

/* RM rules                                                                   */
/* -------------------------------------------------------------------------- */

/*
 * match:  binary fp op with two floating-point constant
 * result: bool constant
 */
static inline bool
applies_const_rm_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla_node_is_rm_const(e0) && bzla_node_is_rm_const(e1);
}

static inline BzlaNode *
apply_const_rm_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_rm_eq(bzla, e0, e1));
  assert(bzla_node_is_regular(e0));

  BzlaNode *result;
  bool bres;

  bres   = bzla_node_rm_const_get_rm(e0) == bzla_node_rm_const_get_rm(e1);
  result = bres ? bzla_exp_true(bzla) : bzla_exp_false(bzla);
  return result;
}

/* FP rules                                                                   */
/* -------------------------------------------------------------------------- */

/*
 * match:  fp.abs(fp.abs(a)) or fp.abs(fp.neg(a))
 * result: fp.abs(a)
 */
static inline bool
applies_fp_abs(Bzla *bzla, BzlaNode *e0)
{
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && (bzla_node_is_fp_abs(e0) || bzla_node_is_fp_neg(e0));
}

static inline BzlaNode *
apply_fp_abs(Bzla *bzla, BzlaNode *e0)
{
  assert(applies_fp_abs(bzla, e0));
  assert(bzla_node_is_regular(e0));
  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_fp_abs_exp(bzla, e0->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  fp.isNan(fp.abs(a) or fp.isNaN(fp.neg(a)) or
 *         fp.isNormal(fp.abs(a) or fp.isNormal(fp.neg(a)) or
 *         fp.isSubnormal(fp.abs(a) or fp.isSubnormal(fp.neg(a)) or
 *         fp.isZero(fp.abs(a) or fp.isZero(fp.neg(a)) or
 *         fp.isInfinite(fp.abs(a) or fp.isInfinite(fp.neg(a))
 * result: fp.is*(a)
 */
static inline bool
applies_fp_tester_sign_ops(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  (void) kind;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && kind != BZLA_FP_IS_POS_NODE
         && kind != BZLA_FP_IS_NEG_NODE
         && (bzla_node_is_fp_abs(e0) || bzla_node_is_fp_neg(e0));
}

static inline BzlaNode *
apply_fp_tester_sign_ops(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  assert(applies_fp_tester_sign_ops(bzla, kind, e0));
  assert(bzla_node_is_regular(e0));
  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_fp_tester_exp(bzla, kind, e0->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  fp.neg(fp.neg(a))
 * result: a
 */
static inline bool
applies_fp_neg(Bzla *bzla, BzlaNode *e0)
{
  (void) bzla;
  return bzla_node_is_fp_neg(e0);
}

static inline BzlaNode *
apply_fp_neg(Bzla *bzla, BzlaNode *e0)
{
  assert(applies_fp_neg(bzla, e0));
  assert(bzla_node_is_regular(e0));
  return bzla_node_copy(bzla, e0->e[0]);
}

/*
 * match:  fp.min(a, a) or fp.max(a, a)
 * result: a
 */
static inline bool
applies_fp_min_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_fp_min_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_min_max(bzla, e0, e1));
  (void) e1;
  return bzla_node_copy(bzla, e0);
}

/*
 * match:  fp.leq(a, a)
 * result: not(fp.isNaN(e0))
 */
static inline bool
applies_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && e0 == e1;
}

static inline BzlaNode *
apply_fp_lte(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_lte(bzla, e0, e1));
  (void) e1;
  BzlaNode *result, *isnan;
  BZLA_INC_REC_RW_CALL(bzla);
  isnan  = rewrite_fp_tester_exp(bzla, BZLA_FP_IS_NAN_NODE, e0);
  result = bzla_exp_bv_not(bzla, isnan);
  bzla_node_release(bzla, isnan);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  fp.lt(a, a)
 * result: false
 */
static inline bool
applies_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  return e0 == e1;
}

static inline BzlaNode *
apply_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_lte(bzla, e0, e1));
  (void) e0;
  (void) e1;
  return bzla_exp_false(bzla);
}

/*
 * match:  fp.rem(fp.rem(a, b), b)
 * result: fp.rem(a, b)
 */
static inline bool
applies_fp_rem_same_divisor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));

  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_fp_rem(e0)
         && e0->e[1] == e1;
}

static inline BzlaNode *
apply_fp_rem_same_divisor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_rem_same_divisor(bzla, e0, e1));
  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_fp_rem_exp(bzla, e0->e[0], e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  fp.rem(a, fp.abs(b)) or fp.rem(a, fp.neg(b))
 * result: fp.rem(a, b)
 */
static inline bool
applies_fp_rem_sign_divisor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e0;
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));

  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND
         && (bzla_node_is_fp_abs(e1) || bzla_node_is_fp_neg(e1));
}

static inline BzlaNode *
apply_fp_rem_sign_divisor(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_rem_sign_divisor(bzla, e0, e1));
  BzlaNode *result;
  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_fp_rem_exp(bzla, e0, e1->e[0]);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match:  fp.rem(fp.neg(a), b)
 * result: fp.neg(fp.rem(a, b))
 */
static inline bool
applies_fp_rem_neg(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e1;
  assert(bzla_node_is_regular(e0));
  assert(bzla_node_is_regular(e1));

  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_fp_neg(e0);
}

static inline BzlaNode *
apply_fp_rem_neg(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_fp_rem_neg(bzla, e0, e1));
  BzlaNode *result, *rem;
  BZLA_INC_REC_RW_CALL(bzla);
  rem    = rewrite_fp_rem_exp(bzla, e0->e[0], e1);
  result = rewrite_fp_neg_exp(bzla, rem);
  bzla_node_release(bzla, rem);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/* APPLY rules                                                                */
/* -------------------------------------------------------------------------- */

/*
 * match:  (\lambda x . t)(a), where term t does not contain param x
 * result: t
 */
static inline bool
applies_const_lambda_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e1;
  return bzla_node_is_lambda(e0)
         && !bzla_node_real_addr(bzla_node_binder_get_body(e0))->parameterized;
}

static inline BzlaNode *
apply_const_lambda_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_const_lambda_apply(bzla, e0, e1));
  (void) e1;
  return bzla_node_copy(bzla,
                        bzla_node_binder_get_body(bzla_node_real_addr(e0)));
}

/*
 * match:  (\lambda x . x)(a)
 * result: a
 */
static inline bool
applies_param_lambda_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e1;
  return bzla_node_is_lambda(e0) && !e0->parameterized
         && bzla_node_is_param(bzla_node_binder_get_body(e0));
}

static inline BzlaNode *
apply_param_lambda_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_param_lambda_apply(bzla, e0, e1));

  BzlaNode *result, *body;

  body = bzla_node_binder_get_body(e0);
  bzla_beta_assign_args(bzla, e0, e1);
  result = bzla_node_copy(
      bzla, bzla_node_param_get_assigned_exp(bzla_node_real_addr(body)));
  bzla_beta_unassign_params(bzla, e0);
  result = bzla_node_cond_invert(body, result);
  return result;
}

/*
 * match:  (\lambda x . f(x))(a)
 * result: f(a)
 */
static inline bool
applies_apply_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) e1;
  BzlaNode *real_body;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_lambda(e0)
         && bzla_node_is_apply(
             (real_body = bzla_node_real_addr(bzla_node_binder_get_body(e0))))
         && !real_body->e[0]->parameterized;
}

static inline BzlaNode *
apply_apply_apply(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_apply_apply(bzla, e0, e1));

  BzlaNode *result, *real_body, *body;

  body      = bzla_node_binder_get_body(e0);
  real_body = bzla_node_real_addr(body);
  BZLA_INC_REC_RW_CALL(bzla);
  bzla_beta_assign_args(bzla, e0, e1);
  e1 = bzla_beta_reduce_bounded(bzla, real_body->e[1], 1);
  bzla_beta_unassign_params(bzla, e0);
  e0 = bzla_simplify_exp(bzla, real_body->e[0]);
  assert(bzla_node_is_fun(e0));
  assert(bzla_node_is_args(e1));
  result = rewrite_apply_exp(bzla, e0, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, e1);
  result = bzla_node_cond_invert(body, result);
  return result;
}

/*
 * propagate apply over parameterized bv conditionals
 */
static inline bool
applies_prop_apply_lambda(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e1;
  return bzla_node_is_lambda(e0)
         && bzla_node_is_bv_cond(bzla_node_binder_get_body(e0));
  ;
}

static inline BzlaNode *
apply_prop_apply_lambda(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_prop_apply_lambda(bzla, e0, e1));

  BzlaNode *result, *cur_fun, *next_fun, *cur_args, *e_cond, *array, *args;
  BzlaNode *beta_cond, *cur_cond, *real_cur_cond;
  BzlaNode *cur_branch, *real_cur_branch;
  BzlaNode *index, *write_index, *value;
  bool done, inv_result_tmp;
  uint32_t propagations, apply_propagations, inv_result;

  done               = 0;
  result             = 0;
  propagations       = 0;
  apply_propagations = 0;
  inv_result         = 0;
  inv_result_tmp     = false;

  cur_fun  = e0;
  cur_args = bzla_node_copy(bzla, e1);

  /* try to propagate apply over bv conditionals were conditions evaluate to
   * true if beta reduced with 'cur_args'. */
  cur_cond =
      bzla_node_is_lambda(cur_fun) ? bzla_node_binder_get_body(cur_fun) : 0;
  while (!done && bzla_node_is_lambda(cur_fun) && !cur_fun->parameterized
         && !cur_args->parameterized
         && (real_cur_cond = bzla_node_real_addr(cur_cond))
         && bzla_node_is_bv_cond(real_cur_cond)
         /* if the condition is not parameterized the check was already done
          * while creating 'cur_cond' */
         && bzla_node_real_addr(real_cur_cond->e[0])->parameterized
         && propagations++ < BZLA_APPLY_PROPAGATION_LIMIT)
  {
    assert(cur_cond);
    assert(bzla_node_is_regular(cur_fun));
    assert(bzla_node_is_regular(cur_args));
    assert(!result);

    next_fun = 0;
    /* optimization for lambdas representing array writes */
    if (is_write_exp(cur_fun, &array, &write_index, &value))
    {
      index = cur_args->e[0];
      /* found value at 'index' */
      if (write_index == index)
      {
        result = bzla_node_copy(bzla, value);
        done   = 1;
      }
      /* propagate down to 'array' */
      else if (is_always_unequal(bzla, write_index, index))
      {
        next_fun = array;
        apply_propagations++;
      }
      else
        goto REWRITE_APPLY_GENERAL_CASE;
    }
    /* more general case: any lambda with bv cond as body */
    else
    {
    REWRITE_APPLY_GENERAL_CASE:
      e_cond = real_cur_cond->e[0];

      if (!bzla_node_real_addr(e_cond)->parameterized) break;

      /* 'inv_result_tmp' indicates if the result obtained from the
       * current propagation path needs to be inverted. in case we really
       * find a result, 'inv_result' will be inverted w.r.t.
       * 'inv_result_tmp'. */
      if (bzla_node_is_inverted(cur_cond)) inv_result_tmp = !inv_result_tmp;

      bzla_beta_assign_args(bzla, cur_fun, cur_args);
      beta_cond = bzla_beta_reduce_bounded(bzla, e_cond, 1);
      /* condition of bv cond is either true or false */
      if (bzla_node_is_bv_const(beta_cond))
      {
        if (is_true_cond(beta_cond))
          cur_branch = real_cur_cond->e[1];
        else
          cur_branch = real_cur_cond->e[2];

        real_cur_branch = bzla_node_real_addr(cur_branch);
        /* branch not parameterized, we found a result */
        if (!real_cur_branch->parameterized)
        {
          result = bzla_node_copy(bzla, real_cur_branch);
          done   = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        else if (bzla_node_is_param(real_cur_branch))
        {
          if ((value = bzla_node_param_get_assigned_exp(real_cur_branch)))
            result = bzla_node_copy(bzla, value);
          else
            result = bzla_node_copy(bzla, real_cur_branch);
          done = 1;
          goto HAVE_RESULT_CHECK_INVERTED;
        }
        /* propagate down to next function */
        else if (bzla_node_is_apply(real_cur_branch))
        {
          args = bzla_beta_reduce_bounded(bzla, real_cur_branch->e[1], 1);
          assert(bzla_node_is_regular(args));
          assert(bzla_node_is_args(args));
          /* nested lambda */
          if (bzla_node_is_lambda(real_cur_branch->e[0])
              && real_cur_branch->e[0]->parameterized)
          {
            bzla_beta_assign_args(bzla, real_cur_branch->e[0], args);
            result = bzla_beta_reduce_bounded(bzla, real_cur_branch->e[0], 1);
            bzla_beta_unassign_params(bzla, real_cur_branch->e[0]);
            assert(!bzla_node_is_fun(result));

            /* propagate down to 'next_fun' */
            if (bzla_node_is_apply(result))
            {
              next_fun = bzla_node_real_addr(result)->e[0];
              bzla_node_release(bzla, args);
              args = bzla_node_copy(bzla, bzla_node_real_addr(result)->e[1]);
              /* result is not needed here as it may be further
               * rewritten */
              bzla_node_release(bzla, result);
              result = 0;
            }
            else
              done = 1;
          }
          /* beta reduce parameterized condition and select branch */
          else if (bzla_node_is_fun_cond(real_cur_branch->e[0])
                   && real_cur_branch->e[0]->parameterized)
          {
            assert(real_cur_branch->e[0]->e[0]->parameterized);
            assert(!real_cur_branch->e[0]->e[1]->parameterized);
            assert(!real_cur_branch->e[0]->e[2]->parameterized);
            result =
                bzla_beta_reduce_bounded(bzla, real_cur_branch->e[0]->e[0], 1);

            if (bzla_node_is_bv_const(result))
            {
              if (result == bzla->true_exp)
                next_fun = real_cur_branch->e[0]->e[1];
              else
                next_fun = real_cur_branch->e[0]->e[2];
            }
            bzla_node_release(bzla, result);
            result = 0;
            /* no branch can be selected, we are done */
            if (!next_fun)
            {
              bzla_node_release(bzla, args);
              goto REWRITE_APPLY_NO_RESULT_DONE;
            }
          }
          /* propagate down to 'next_fun' */
          else
          {
            next_fun = real_cur_branch->e[0];
            assert(bzla_node_is_fun(next_fun));
          }

          /* set arguments for new functin application */
          bzla_node_release(bzla, cur_args);
          cur_args = args;

        HAVE_RESULT_CHECK_INVERTED:
          assert(result || next_fun);
          assert(!result || !next_fun);
          assert(!done || result);
          /* at this point we already have a result, which is either
           * a value obtained by beta reducing 'cur_fun' or a
           * function application on 'next_fun' with 'cur_args'.
           * in the latter case, we try to further rewrite the function
           * application. */

          /* if 'cur_branch' is inverted we need to invert the result */
          if (bzla_node_is_inverted(cur_branch))
            inv_result_tmp = !inv_result_tmp;

          /* we got a result, we can savely set 'inv_result' */
          if (inv_result_tmp)
          {
            inv_result     = !inv_result;
            inv_result_tmp = false;
          }
          apply_propagations++;
        }
        /* check if we can further propagate down along a conditional */
        else if (bzla_node_is_bv_cond(real_cur_branch))
        {
          cur_cond = cur_branch;
        }
        /* cur_branch is some other parameterized term that we don't
         * expand */
        // TODO (ma): try to expand more parameterized terms?
        else
          goto REWRITE_APPLY_NO_RESULT_DONE;
      }
      else
      {
      REWRITE_APPLY_NO_RESULT_DONE:
        assert(!result);
        done = 1;
      }
      bzla_beta_unassign_params(bzla, cur_fun);
      bzla_node_release(bzla, beta_cond);
    }

    if (next_fun)
    {
      cur_fun = next_fun;
      cur_cond =
          bzla_node_is_lambda(cur_fun) ? bzla_node_binder_get_body(cur_fun) : 0;
    }
    assert(!result || done);
  }

  /* check if apply was propagated down to 'cur_fun' */
  if (!result && cur_fun != e0)
    result = bzla_node_create_apply(bzla, cur_fun, cur_args);

  bzla_node_release(bzla, cur_args);

  if (result && inv_result) result = bzla_node_invert(result);

  bzla->stats.prop_apply_lambda += apply_propagations;
  return result;
}

/*
 * TODO description
 */
static inline bool
applies_prop_apply_update(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  (void) bzla;
  (void) e1;
  return bzla_node_is_update(e0);
}

static inline BzlaNode *
apply_prop_apply_update(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(applies_prop_apply_update(bzla, e0, e1));

  uint32_t propagations = 0, num_eq;
  bool prop_down;
  BzlaNode *cur, *args, *value, *a1, *a2, *result = 0, *eq;
  BzlaArgsIterator it1, it2;

  cur = e0;
  while (bzla_node_is_update(cur))
  {
    args  = cur->e[1];
    value = cur->e[2];

    if (e1 == args)
    {
      propagations++;
      result = bzla_node_copy(bzla, value);
      break;
    }

    prop_down = false;
    num_eq    = 0;
    assert(e1->sort_id == args->sort_id);
    bzla_iter_args_init(&it1, e1);
    bzla_iter_args_init(&it2, args);
    while (bzla_iter_args_has_next(&it1))
    {
      assert(bzla_iter_args_has_next(&it2));
      a1 = bzla_iter_args_next(&it1);
      a2 = bzla_iter_args_next(&it2);

      if (is_always_unequal(bzla, a1, a2))
      {
        prop_down = true;
        break;
      }

      BZLA_INC_REC_RW_CALL(bzla);
      eq = rewrite_eq_exp(bzla, a1, a2);
      BZLA_DEC_REC_RW_CALL(bzla);
      if (eq == bzla_node_invert(bzla->true_exp))
      {
        bzla_node_release(bzla, eq);
        prop_down = true;
        break;
      }
      else if (eq == bzla->true_exp)
      {
        num_eq++;
      }
      bzla_node_release(bzla, eq);
    }

    if (num_eq == bzla_node_args_get_arity(bzla, args))
    {
      propagations++;
      result = bzla_node_copy(bzla, value);
      break;
    }

    if (prop_down)
    {
      propagations++;
      cur = cur->e[0];
    }
    else
      break;
  }

  /* propagated until 'cur', create apply on 'cur' */
  if (!result)
  {
    if (bzla_node_is_const_array(cur))
    {
      result = bzla_node_copy(bzla, cur->e[1]);
    }
    else
    {
      BZLA_INC_REC_RW_CALL(bzla);
      result = bzla_node_create_apply(bzla, cur, e1);
      BZLA_DEC_REC_RW_CALL(bzla);
    }
  }
  bzla->stats.prop_apply_update += propagations;
  return result;
}

/* LAMBDA rules */

#if 0 
// TODO (ma): this rule cannot be applied yet as it may produce lambdas with
//            different sorts
/*
 * match: (\lambda j . (\lambda k . t)(j))
 * result: \lambda k . t
 */
static inline bool
applies_lambda_lambda (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return !bzla_node_is_inverted (e1)
	 && bzla_node_is_apply (e1)
	 && !e1->e[0]->parameterized
	 && e1->e[1]->arity == 1
	 && e1->e[1]->e[0] == e0;
}

static inline BzlaNode *
apply_lambda_lambda (Bzla * bzla, BzlaNode * e0, BzlaNode * e1)
{
  return bzla_node_copy (bzla, e1->e[0]);
}
#endif

/* QUANTIFIER rules                                                           */
/* -------------------------------------------------------------------------- */

/*
 * TODO description
 */
static inline bool
applies_const_quantifier(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  (void) bzla;
  (void) param;
  return !bzla_node_real_addr(body)->parameterized;
}

static inline BzlaNode *
apply_const_quantifier(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  assert(applies_const_quantifier(bzla, param, body));
  (void) param;
  return bzla_node_copy(bzla, body);
}

/* FORALL rules                                                               */
/* -------------------------------------------------------------------------- */

#if 0

/*
 * match:  (\forall x . t) where x does not occur in t
 * result: t
 */
static inline bool
applies_param_free_forall (Bzla * bzla, BzlaNode * param, BzlaNode * body)
{ 
  (void) bzla;
  (void) body;
  return param->parents == 0;
}

static inline BzlaNode *
apply_param_free_forall (Bzla * bzla, BzlaNode * param, BzlaNode * body)
{
  assert (applies_param_free_forall (bzla, param, body));
  (void) param;
  return bzla_node_copy (bzla, body);
}

#endif

/*
 * match: \forall x . x = t    if x \not \in vars(t)
 * match: \forall x . x != t    if x \not \in vars(t)
 * result: false
 */
static inline bool
applies_eq_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  (void) bzla;
  (void) body;
  BzlaNode *real_body;
  real_body = bzla_node_real_addr(body);
  return bzla_node_is_bv_eq(body) && param->parents == 1  // only parent is body
         && ((real_body->e[0] == param
              && !bzla_node_real_addr(real_body->e[1])->quantifier_below)
             || (real_body->e[1] == param
                 && !bzla_node_real_addr(real_body->e[0])->quantifier_below));
}

static inline BzlaNode *
apply_eq_forall(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  assert(applies_eq_forall(bzla, param, body));
  (void) param;
  (void) body;
  return bzla_exp_false(bzla);
}

#if 0

/* EXISTS rules                                                               */
/* -------------------------------------------------------------------------- */

/*
 * match:  (\exists x . t) where x does not occur in t
 * result: t
 */
static inline bool
applies_param_free_exists (Bzla * bzla, BzlaNode * param, BzlaNode * body)
{ 
  (void) bzla;
  (void) body;
  return param->parents == 0;
}

static inline BzlaNode *
apply_param_free_exists (Bzla * bzla, BzlaNode * param, BzlaNode * body)
{
  assert (applies_param_free_exists (bzla, param, body));
  (void) param;
  return bzla_node_copy (bzla, body);
}

#endif

/*
 * match: \exists x . x = t    if x \not \in vars(t)
 * match: \exists x . x != t    if x \not \in vars(t)
 * result: true
 */
static inline bool
applies_eq_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  (void) bzla;
  (void) body;
  BzlaNode *real_body;
  real_body = bzla_node_real_addr(body);
  return bzla_node_is_bv_eq(body) && param->parents == 1  // only parent is body
         && ((real_body->e[0] == param
              && !bzla_node_real_addr(real_body->e[1])->quantifier_below)
             || (real_body->e[1] == param
                 && !bzla_node_real_addr(real_body->e[0])->quantifier_below));
}

static inline BzlaNode *
apply_eq_exists(Bzla *bzla, BzlaNode *param, BzlaNode *body)
{
  assert(applies_eq_exists(bzla, param, body));
  (void) param;
  (void) body;
  return bzla_exp_true(bzla);
}

/* COND rules                                                                 */
/* -------------------------------------------------------------------------- */

/*
 * match: c ? a : a
 * result: a
 */
static inline bool
applies_equal_branches_cond(Bzla *bzla,
                            BzlaNode *e0,
                            BzlaNode *e1,
                            BzlaNode *e2)
{
  (void) bzla;
  (void) e0;
  return e1 == e2;
}

static inline BzlaNode *
apply_equal_branches_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_equal_branches_cond(bzla, e0, e1, e2));
  (void) e0;
  (void) e2;
  return bzla_node_copy(bzla, e1);
}

/*
 * match: c ? a : b, where c is a constant
 * result: a if c is true, and b otherwise
 */
static inline bool
applies_const_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) bzla;
  (void) e1;
  (void) e2;
  return bzla_node_is_bv_const(e0);
}

static inline BzlaNode *
apply_const_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_const_cond(bzla, e0, e1, e2));
  if (bzla_bv_get_bit(bzla_node_bv_const_get_bits(e0), 0))
    return bzla_node_copy(bzla, e1);
  return bzla_node_copy(bzla, e2);
}

/*
 * match: c0 ? (c0 ? a : b) : c
 * result: c0 ? a : c
 */
static inline bool
applies_cond_if_dom_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e2;
  BzlaNode *real_e1;
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e1)
         && real_e1->e[0] == e0;
}

static inline BzlaNode *
apply_cond_if_dom_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_cond_if_dom_cond(bzla, e0, e1, e2));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_cond_exp(
      bzla, e0, bzla_node_cond_invert(e1, bzla_node_real_addr(e1)->e[1]), e2);
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: c0 ? (c1 ? a : b) : a
 * result: c0 AND ~c1 ? b : a
 */
static inline bool
applies_cond_if_merge_if_cond(Bzla *bzla,
                              BzlaNode *e0,
                              BzlaNode *e1,
                              BzlaNode *e2)
{
  (void) e0;
  BzlaNode *real_e1;
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e1)
         && bzla_node_cond_invert(e1, real_e1->e[1]) == e2;
}

static inline BzlaNode *
apply_cond_if_merge_if_cond(Bzla *bzla,
                            BzlaNode *e0,
                            BzlaNode *e1,
                            BzlaNode *e2)
{
  assert(applies_cond_if_merge_if_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp, *e10, *e12, *real_e1;

  real_e1 = bzla_node_real_addr(e1);
  e10     = real_e1->e[0];
  e12     = bzla_node_cond_invert(e1, real_e1->e[2]);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_and_exp(bzla, e0, bzla_node_invert(e10));
  result = rewrite_cond_exp(bzla, tmp, e12, e2);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 ? (c1 ? b : a) : a
 * result: c0 AND c1 ? b : a
 */
static inline bool
applies_cond_if_merge_else_cond(Bzla *bzla,
                                BzlaNode *e0,
                                BzlaNode *e1,
                                BzlaNode *e2)
{
  (void) e0;
  BzlaNode *real_e1;
  real_e1 = bzla_node_real_addr(e1);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e1)
         && bzla_node_cond_invert(e1, real_e1->e[2]) == e2;
}

static inline BzlaNode *
apply_cond_if_merge_else_cond(Bzla *bzla,
                              BzlaNode *e0,
                              BzlaNode *e1,
                              BzlaNode *e2)
{
  assert(applies_cond_if_merge_else_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp, *e10, *e11, *real_e1;

  real_e1 = bzla_node_real_addr(e1);
  e10     = real_e1->e[0];
  e11     = bzla_node_cond_invert(e1, real_e1->e[1]);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_and_exp(bzla, e0, e10);
  result = rewrite_cond_exp(bzla, tmp, e11, e2);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 ? a : (c0 ? b : c)
 * result: c0 ? a : c
 */
static inline bool
applies_cond_else_dom_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e1;
  BzlaNode *real_e2;
  real_e2 = bzla_node_real_addr(e2);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e2)
         && real_e2->e[0] == e0;
}

static inline BzlaNode *
apply_cond_else_dom_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_cond_else_dom_cond(bzla, e0, e1, e2));

  BzlaNode *result;

  BZLA_INC_REC_RW_CALL(bzla);
  result = rewrite_cond_exp(
      bzla, e0, e1, bzla_node_cond_invert(e2, bzla_node_real_addr(e2)->e[2]));
  BZLA_DEC_REC_RW_CALL(bzla);
  return result;
}

/*
 * match: c0 ? a : (c1 ? a : b)
 * result: ~c0 AND ~c1 ? b : a
 */
static inline bool
applies_cond_else_merge_if_cond(Bzla *bzla,
                                BzlaNode *e0,
                                BzlaNode *e1,
                                BzlaNode *e2)
{
  (void) e0;
  BzlaNode *real_e2;
  real_e2 = bzla_node_real_addr(e2);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e2)
         && bzla_node_cond_invert(e2, real_e2->e[1]) == e1;
}

static inline BzlaNode *
apply_cond_else_merge_if_cond(Bzla *bzla,
                              BzlaNode *e0,
                              BzlaNode *e1,
                              BzlaNode *e2)
{
  assert(applies_cond_else_merge_if_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp, *e20, *e22, *real_e2;

  real_e2 = bzla_node_real_addr(e2);
  e20     = real_e2->e[0];
  e22     = bzla_node_cond_invert(e2, real_e2->e[2]);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp = rewrite_bv_and_exp(bzla, bzla_node_invert(e0), bzla_node_invert(e20));
  result = rewrite_cond_exp(bzla, tmp, e22, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match: c0 ? a : (c1 ? b : a)
 * result: ~c0 AND c1 ? b : a
 */
static inline bool
applies_cond_else_merge_else_cond(Bzla *bzla,
                                  BzlaNode *e0,
                                  BzlaNode *e1,
                                  BzlaNode *e2)
{
  (void) e0;
  BzlaNode *real_e2;
  real_e2 = bzla_node_real_addr(e2);
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_cond(real_e2)
         && bzla_node_cond_invert(e2, real_e2->e[2]) == e1;
}

static inline BzlaNode *
apply_cond_else_merge_else_cond(Bzla *bzla,
                                BzlaNode *e0,
                                BzlaNode *e1,
                                BzlaNode *e2)
{
  assert(applies_cond_else_merge_else_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp, *e20, *e21, *real_e2;

  real_e2 = bzla_node_real_addr(e2);
  e20     = real_e2->e[0];
  e21     = bzla_node_cond_invert(e2, real_e2->e[1]);
  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_bv_and_exp(bzla, bzla_node_invert(e0), e20);
  result = rewrite_cond_exp(bzla, tmp, e21, e1);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? a : b, where len(a) = 1
 * result: (~c OR a) AND (c OR b)
 */
static inline bool
applies_bool_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  (void) e2;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv(bzla, e1)
         && bzla_node_bv_get_width(bzla, e1) == 1;
}

static inline BzlaNode *
apply_bool_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_bool_cond(bzla, e0, e1, e2));

  BzlaNode *tmp1, *tmp2, *result;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp1   = bzla_exp_bv_or(bzla, bzla_node_invert(e0), e1);
  tmp2   = bzla_exp_bv_or(bzla, e0, e2);
  result = rewrite_bv_and_exp(bzla, tmp1, tmp2);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp1);
  bzla_node_release(bzla, tmp2);
  return result;
}

/*
 * match:  c ? (a + 1) : a
 * match:  c ? (1 + a) : a
 * result: a + 0::c
 */
static inline bool
applies_add_if_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && bzla_node_is_bv_add(e1)
         && ((e1->e[0] == e2 && bzla_node_is_bv_const_one(bzla, e1->e[1]))
             || (e1->e[1] == e2 && bzla_node_is_bv_const_one(bzla, e1->e[0])));
}

static inline BzlaNode *
apply_add_if_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_add_if_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = bzla_exp_bv_uext(bzla, e0, bzla_node_bv_get_width(bzla, e1) - 1);
  result = rewrite_bv_add_exp(bzla, e2, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? a : (a + 1)
 * match:  c ? a : (1 + a)
 * result: a + 0::c
 */
static inline bool
applies_add_else_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e2)
         && bzla_node_is_bv_add(e2)
         && ((e2->e[0] == e1 && bzla_node_is_bv_const_one(bzla, e2->e[1]))
             || (e2->e[1] == e1 && bzla_node_is_bv_const_one(bzla, e2->e[0])));
}

static inline BzlaNode *
apply_add_else_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_add_else_cond(bzla, e0, e1, e2));
  (void) e2;

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp = bzla_exp_bv_uext(
      bzla, bzla_node_invert(e0), bzla_node_bv_get_width(bzla, e1) - 1);
  result = rewrite_bv_add_exp(bzla, e1, tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? (a::b) : (a::d)
 * result: a :: (c ? b : d)
 *
 * match:  c ? (a::b) : (d::b)
 * result: (c ? a : d) :: b
 */
static inline bool
applies_concat_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  bool result;
  BzlaNode *real_e1, *real_e2, *e10, *e11, *e20, *e21;

  real_e1 = bzla_node_real_addr(e1);
  real_e2 = bzla_node_real_addr(e2);
  result  = bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
           && bzla->rec_rw_calls < BZLA_REC_RW_BOUND
           && bzla_node_is_bv_concat(real_e1)
           && bzla_node_is_bv_concat(real_e2);

  if (!result) return result;

  e10 = bzla_node_cond_invert(e1, real_e1->e[0]);
  e11 = bzla_node_cond_invert(e1, real_e1->e[1]);
  e20 = bzla_node_cond_invert(e2, real_e2->e[0]);
  e21 = bzla_node_cond_invert(e2, real_e2->e[1]);
  return (e10 == e20 || e11 == e21);
}

static inline BzlaNode *
apply_concat_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_concat_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp1, *tmp2, *real_e1, *real_e2, *e10, *e11, *e20, *e21;
  real_e1 = bzla_node_real_addr(e1);
  real_e2 = bzla_node_real_addr(e2);
  e10     = bzla_node_cond_invert(e1, real_e1->e[0]);
  e11     = bzla_node_cond_invert(e1, real_e1->e[1]);
  e20     = bzla_node_cond_invert(e2, real_e2->e[0]);
  e21     = bzla_node_cond_invert(e2, real_e2->e[1]);

  BZLA_INC_REC_RW_CALL(bzla);
  tmp1   = rewrite_cond_exp(bzla, e0, e10, e20);
  tmp2   = rewrite_cond_exp(bzla, e0, e11, e21);
  result = rewrite_bv_concat_exp(bzla, tmp1, tmp2);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp1);
  bzla_node_release(bzla, tmp2);
  return result;
}

/*
 * match:  c ? a OP b : a OP d, where OP is either +, &, *, /, %
 * result: a OP (c ? b : d)
 */
static inline bool
applies_op_lhs_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && !bzla_node_is_inverted(e2) && e1->kind == e2->kind
         && (bzla_node_is_bv_add(e1) || bzla_node_is_bv_and(e1)
             || bzla_node_is_bv_mul(e1) || bzla_node_is_bv_udiv(e1)
             || bzla_node_is_bv_urem(e1))
         && e1->e[0] == e2->e[0];
}

static inline BzlaNode *
apply_op_lhs_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_op_lhs_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_cond_exp(bzla, e0, e1->e[1], e2->e[1]);
  result = bzla_rewrite_binary_exp(bzla, e1->kind, e1->e[0], tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? a OP b : d OP b, where OP is either +, &, *, /, %
 * result: (c ? a : d) OP b
 */
static inline bool
applies_op_rhs_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && !bzla_node_is_inverted(e2) && e1->kind == e2->kind
         && (bzla_node_is_bv_add(e1) || bzla_node_is_bv_and(e1)
             || bzla_node_is_bv_mul(e1) || bzla_node_is_bv_udiv(e1)
             || bzla_node_is_bv_urem(e1))
         && e1->e[1] == e2->e[1];
}

static inline BzlaNode *
apply_op_rhs_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_op_rhs_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_cond_exp(bzla, e0, e1->e[0], e2->e[0]);
  result = bzla_rewrite_binary_exp(bzla, e1->kind, tmp, e1->e[1]);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? a OP b : d OP a, where OP is either +, &, *
 * result: a OP (c ? b : d)
 */
static inline bool
applies_comm_op_1_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && !bzla_node_is_inverted(e2) && e1->kind == e2->kind
         && (bzla_node_is_bv_add(e1) || bzla_node_is_bv_and(e1)
             || bzla_node_is_bv_mul(e1))
         && e1->e[0] == e2->e[1];
}

static inline BzlaNode *
apply_comm_op_1_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_comm_op_1_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_cond_exp(bzla, e0, e1->e[1], e2->e[0]);
  result = bzla_rewrite_binary_exp(bzla, e1->kind, e1->e[0], tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

/*
 * match:  c ? a OP b : b OP d, where OP is either +, &, *
 * result: b OP (c ? a : d)
 */
static inline bool
applies_comm_op_2_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  (void) e0;
  return bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
         && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && !bzla_node_is_inverted(e1)
         && !bzla_node_is_inverted(e2) && e1->kind == e2->kind
         && (bzla_node_is_bv_add(e1) || bzla_node_is_bv_and(e1)
             || bzla_node_is_bv_mul(e1))
         && e1->e[1] == e2->e[0];
}

static inline BzlaNode *
apply_comm_op_2_cond(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(applies_comm_op_2_cond(bzla, e0, e1, e2));

  BzlaNode *result, *tmp;

  BZLA_INC_REC_RW_CALL(bzla);
  tmp    = rewrite_cond_exp(bzla, e0, e1->e[0], e2->e[1]);
  result = bzla_rewrite_binary_exp(bzla, e1->kind, e1->e[1], tmp);
  BZLA_DEC_REC_RW_CALL(bzla);
  bzla_node_release(bzla, tmp);
  return result;
}

#if 0
/*
 * match:
 * result:
 */
static inline bool
applies_cond (Bzla * bzla, BzlaNode * e0, BzlaNode * e1, BzlaNode * e2)
{
}

static inline BzlaNode * 
apply_cond (Bzla * bzla, BzlaNode * e0, BzlaNode * e1, BzlaNode * e2)
{
  assert (applies_cond (bzla, e0, e1, e2));

}
#endif

/* -------------------------------------------------------------------------- */
/* normalizers                                                                */
/* -------------------------------------------------------------------------- */

static BzlaNode *
mk_norm_node_from_hash_table(Bzla *bzla,
                             BzlaNodeKind kind,
                             BzlaPtrHashTable *nodes)
{
  assert(nodes->count > 0);

  size_t i;
  BzlaNode *cur, *tmp, *result;
  BzlaNodePtrStack stack;
  BzlaPtrHashTableIterator it;
  BzlaHashTableData *d;

  BZLA_INIT_STACK(bzla->mm, stack);
  bzla_iter_hashptr_init(&it, nodes);
  while (bzla_iter_hashptr_has_next(&it))
  {
    cur = it.cur;
    d   = bzla_iter_hashptr_next_data(&it);
    for (i = 0; i < (size_t) d->as_int; i++) BZLA_PUSH_STACK(stack, cur);
  }

  qsort(stack.start, BZLA_COUNT_STACK(stack), sizeof(BzlaNode *), cmp_node_id);

  BZLA_INC_REC_RW_CALL(bzla);
  assert(!BZLA_EMPTY_STACK(stack));
  result = bzla_node_copy(bzla, BZLA_PEEK_STACK(stack, 0));
  for (i = 1; i < BZLA_COUNT_STACK(stack); i++)
  {
    cur = BZLA_PEEK_STACK(stack, i);
    tmp = bzla_rewrite_binary_exp(bzla, kind, result, cur);
    bzla_node_release(bzla, result);
    result = tmp;
  }
  BZLA_DEC_REC_RW_CALL(bzla);
  BZLA_RELEASE_STACK(stack);
  return result;
}

static void
normalize_bin_comm_ass_exp(Bzla *bzla,
                           BzlaNode *e0,
                           BzlaNode *e1,
                           BzlaNode **e0_norm,
                           BzlaNode **e1_norm)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2);
  assert(e0);
  assert(e1);
  assert(!bzla_node_real_addr(e0)->simplified);
  assert(!bzla_node_real_addr(e1)->simplified);
  assert(e0_norm);
  assert(e1_norm);
  assert(!bzla_node_is_inverted(e0));
  assert(!bzla_node_is_inverted(e1));
  assert(bzla_node_is_bv_add(e0) || bzla_node_is_bv_and(e0)
         || bzla_node_is_bv_mul(e0));
  assert(e0->kind == e1->kind);

  BzlaNodeKind kind;
  BzlaNode *cur, *common;
  BzlaNodePtrStack stack;
  BzlaMemMgr *mm;
  BzlaPtrHashTable *left, *right, *comm;
  BzlaPtrHashBucket *b;
  BzlaIntHashTable *cache;
  BzlaHashTableData *d;
  bool normalize_all = true, need_restart = false;

  mm   = bzla->mm;
  kind = e0->kind;

RESTART_NORMALIZE:
  left  = bzla_hashptr_table_new(mm,
                                (BzlaHashPtr) bzla_node_hash_by_id,
                                (BzlaCmpPtr) bzla_node_compare_by_id);
  right = bzla_hashptr_table_new(mm,
                                 (BzlaHashPtr) bzla_node_hash_by_id,
                                 (BzlaCmpPtr) bzla_node_compare_by_id);
  comm  = bzla_hashptr_table_new(mm,
                                (BzlaHashPtr) bzla_node_hash_by_id,
                                (BzlaCmpPtr) bzla_node_compare_by_id);
  cache = bzla_hashint_map_new(mm);

  if (!bzla_opt_get(bzla, BZLA_OPT_RW_NORMALIZE)) goto RETURN_NO_RESULT;

  /* We first try to normalize all nodes, i.e., we do a tree traversal on e0
   * and e1. If we encounter a node more than 32 times, we restart and do a
   * DAG traversal. The 'need_restart' flag indicates whether we actually need
   * to do a DAG traversal after the first pass, which is the case if a node
   * was visited more than once. */
  BZLA_INIT_STACK(mm, stack);
  BZLA_PUSH_STACK(stack, e0);
  do
  {
    cur = BZLA_POP_STACK(stack);
    if (!bzla_node_is_inverted(cur) && cur->kind == kind)
    {
      d = bzla_hashint_map_get(cache, cur->id);
      if (d)
      {
        if (normalize_all)
        {
          need_restart = true;
        }
        else
        {
          BZLA_RELEASE_STACK(stack);
          goto RETURN_NO_RESULT;
        }
      }
      else
      {
        d = bzla_hashint_map_add(cache, cur->id);
      }
      d->as_int += 1;
      if (d->as_int > 32)
      {
        BZLA_RELEASE_STACK(stack);
        goto RESTART_NORMALIZE_ALL;
      }
      BZLA_PUSH_STACK(stack, cur->e[1]);
      BZLA_PUSH_STACK(stack, cur->e[0]);
    }
    else
    {
      if (!(b = bzla_hashptr_table_get(left, cur)))
        b = bzla_hashptr_table_add(left, cur);
      b->data.as_int++;
    }
  } while (!BZLA_EMPTY_STACK(stack));
  bzla_hashint_map_delete(cache);
  cache = bzla_hashint_map_new(mm);

  BZLA_PUSH_STACK(stack, e1);
  do
  {
    cur = BZLA_POP_STACK(stack);
    if (!bzla_node_is_inverted(cur) && cur->kind == kind)
    {
      d = bzla_hashint_map_get(cache, cur->id);
      if (d)
      {
        if (normalize_all)
        {
          need_restart = true;
        }
        else
        {
          BZLA_RELEASE_STACK(stack);
          goto RETURN_NO_RESULT;
        }
      }
      else
      {
        d = bzla_hashint_map_add(cache, cur->id);
      }
      d->as_int += 1;
      if (d->as_int > 32)
      {
        BZLA_RELEASE_STACK(stack);
        goto RESTART_NORMALIZE_ALL;
      }
      BZLA_PUSH_STACK(stack, cur->e[1]);
      BZLA_PUSH_STACK(stack, cur->e[0]);
    }
    else
    {
      b = bzla_hashptr_table_get(left, cur);
      if (b)
      {
        /* we found one common operand */

        /* remove operand from left */
        if (b->data.as_int > 1)
          b->data.as_int--;
        else
        {
          assert(b->data.as_int == 1);
          bzla_hashptr_table_remove(left, cur, 0, 0);
        }

        /* insert into common table */
        if (!(b = bzla_hashptr_table_get(comm, cur)))
          b = bzla_hashptr_table_add(comm, cur);
        b->data.as_int++;
      }
      else
      {
        /* operand is not common */
        if (!(b = bzla_hashptr_table_get(right, cur)))
          b = bzla_hashptr_table_add(right, cur);
        b->data.as_int++;
      }
    }
  } while (!BZLA_EMPTY_STACK(stack));
  BZLA_RELEASE_STACK(stack);

  /* no operand or only one operand in common? leave everything as it is */
  if (comm->count < 2u)
  {
  RETURN_NO_RESULT:
    /* clean up */
    bzla_hashptr_table_delete(left);
    bzla_hashptr_table_delete(right);
    bzla_hashptr_table_delete(comm);
    bzla_hashint_map_delete(cache);
    *e0_norm = bzla_node_copy(bzla, e0);
    *e1_norm = bzla_node_copy(bzla, e1);
    return;
  }

  if (normalize_all && need_restart && (left->count > 0 || right->count > 0))
  {
  RESTART_NORMALIZE_ALL:
    normalize_all = false;
    bzla_hashptr_table_delete(left);
    bzla_hashptr_table_delete(right);
    bzla_hashptr_table_delete(comm);
    bzla_hashint_map_delete(cache);
    goto RESTART_NORMALIZE;
  }

  if (kind == BZLA_BV_AND_NODE)
    bzla->stats.ands_normalized++;
  else if (kind == BZLA_BV_ADD_NODE)
    bzla->stats.adds_normalized++;
  else
  {
    assert(kind == BZLA_BV_MUL_NODE);
    bzla->stats.muls_normalized++;
  }

  assert(comm->count >= 2u);

  /* normalize common nodes */
  common = mk_norm_node_from_hash_table(bzla, kind, comm);

  if (!(b = bzla_hashptr_table_get(left, common)))
    b = bzla_hashptr_table_add(left, common);
  b->data.as_int += 1;
  *e0_norm = mk_norm_node_from_hash_table(bzla, kind, left);

  if (!(b = bzla_hashptr_table_get(right, common)))
    b = bzla_hashptr_table_add(right, common);
  b->data.as_int += 1;
  *e1_norm = mk_norm_node_from_hash_table(bzla, kind, right);

  /* clean up */
  bzla_node_release(bzla, common);
  bzla_hashptr_table_delete(left);
  bzla_hashptr_table_delete(right);
  bzla_hashptr_table_delete(comm);
  bzla_hashint_map_delete(cache);
}

static BzlaNode *
find_top_op(Bzla *bzla, BzlaNode *e)
{
  BzlaNode *res;
  e = bzla_node_real_addr(e);
  if (bzla_node_is_bv_add(e) || bzla_node_is_bv_mul(e)
      || bzla_node_is_bv_and(e))
    return e;
  if (bzla->rec_rw_calls >= BZLA_REC_RW_BOUND) return 0;

  res = 0;
  BZLA_INC_REC_RW_CALL(bzla);
  if (bzla_node_is_bv_slice(e) || bzla_node_is_bv_sll(e)
      || bzla_node_is_bv_srl(e))
  {
    res = find_top_op(bzla, e->e[0]);
  }
  BZLA_DEC_REC_RW_CALL(bzla);

  // TODO handle more operators ... (here first)

  return res;
}

static BzlaNode *
rebuild_top_op(Bzla *bzla, BzlaNode *e, BzlaNode *c, BzlaNode *r)
{
  assert(!bzla_node_is_inverted(c));

  BzlaNode *res, *tmp;

  if (bzla_node_is_inverted(e))
  {
    tmp = rebuild_top_op(bzla, bzla_node_real_addr(e), c, r);
    res = bzla_node_invert(tmp);
  }
  else if (e == c)
    res = bzla_node_copy(bzla, r);
  else
  {
    // TODO handle more operators ... (then here)
    //
    res = 0;
    tmp = rebuild_top_op(bzla, e->e[0], c, r);
    if (bzla_node_is_bv_slice(e))
    {
      res = rewrite_bv_slice_exp(bzla,
                                 tmp,
                                 bzla_node_bv_slice_get_upper(e),
                                 bzla_node_bv_slice_get_lower(e));
    }
    else if (bzla_node_is_bv_sll(e))
    {
      res = rewrite_bv_sll_exp(bzla, tmp, e->e[1]);
    }
    else if (bzla_node_is_bv_srl(e))
    {
      res = rewrite_bv_srl_exp(bzla, tmp, e->e[1]);
    }
    bzla_node_release(bzla, tmp);
    assert(res);
  }
  return res;
}

static void
normalize_adds_muls_ands(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1, *real_e0, *real_e1, *e0_norm, *e1_norm;

  e0      = *left;
  e1      = *right;
  real_e0 = bzla_node_real_addr(e0);
  real_e1 = bzla_node_real_addr(e1);

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
      && real_e0->kind == real_e1->kind
      && ((bzla_node_is_bv_add(real_e0)
           && bzla_opt_get(bzla, BZLA_OPT_RW_NORMALIZE_ADD))
          || bzla_node_is_bv_mul(real_e0) || bzla_node_is_bv_and(real_e0)))
  {
    normalize_bin_comm_ass_exp(bzla, real_e0, real_e1, &e0_norm, &e1_norm);
    e0_norm = bzla_node_cond_invert(e0, e0_norm);
    e1_norm = bzla_node_cond_invert(e1, e1_norm);
    bzla_node_release(bzla, e0);
    bzla_node_release(bzla, e1);
    *left  = e0_norm;
    *right = e1_norm;
  }
}

static inline void
normalize_eq(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1, *tmp1, *tmp2, *op0, *op1, *c0, *c1, *n0, *n1, *add;

  e0 = *left;
  e1 = *right;

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1))
  {
    e0 = bzla_node_invert(e0);
    e1 = bzla_node_invert(e1);
  }

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 1)
  {
    if (bzla_node_is_inverted(e0) && bzla_node_is_bv_var(e0))
    {
      e0 = bzla_node_invert(e0);
      e1 = bzla_node_invert(e1);
    }
  }

  // TODO(ma): this is probably redundant
  /* normalize adds and muls on demand */
  normalize_adds_muls_ands(bzla, &e0, &e1);

  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2 && (op0 = find_top_op(bzla, e0))
      && (op1 = find_top_op(bzla, e1))
      && bzla_node_real_addr(op0)->kind == bzla_node_real_addr(op1)->kind
      && bzla_node_get_sort_id(op0) == bzla_node_get_sort_id(op1))
  {
    if (!bzla_node_is_bv_and(op0)
        || bzla_opt_get(bzla, BZLA_OPT_RW_NORMALIZE_ADD))
    {
      normalize_bin_comm_ass_exp(bzla, op0, op1, &n0, &n1);
      tmp1 = rebuild_top_op(bzla, e0, op0, n0);
      tmp2 = rebuild_top_op(bzla, e1, op1, n1);
      bzla_node_release(bzla, n0);
      bzla_node_release(bzla, n1);
      bzla_node_release(bzla, e0);
      bzla_node_release(bzla, e1);
      e0 = tmp1;
      e1 = tmp2;
    }
  }

  // TODO (ma): check if this is also applicable to mul nodes and maybe others?
  /*
   * match: c0 = c1 + b
   * result: c0 - c1 = b
   *
   * also handles negated adds:
   *
   * c0 = ~(c1 + b) -> ~c0 = c1 + b
   */
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
      && ((bzla_node_is_bv_add(e0) && bzla_node_is_bv_const(e1))
          || (bzla_node_is_bv_add(e1) && bzla_node_is_bv_const(e0))))
  {
    if (bzla_node_is_bv_const(e0) && bzla_node_is_bv_add(e1))
    {
      c0  = e0;
      add = e1;
    }
    else
    {
      assert(bzla_node_is_bv_add(e0));
      assert(bzla_node_is_bv_const(e1));
      c0  = e1;
      add = e0;
    }

    /* c0 = ~(c1 + b) -> ~c0 = c1 + b */
    c0  = bzla_node_cond_invert(add, c0);
    add = bzla_node_cond_invert(add, add);

    c1 = tmp1 = 0;
    assert(bzla_node_is_regular(add));
    if (bzla_node_is_bv_const(add->e[0]))
    {
      c1   = add->e[0];
      tmp1 = add->e[1];
    }
    else if (bzla_node_is_bv_const(add->e[1]))
    {
      c1   = add->e[1];
      tmp1 = add->e[0];
    }

    if (tmp1)
    {
      assert(c0);
      assert(c1);
      n0 = bzla_node_copy(bzla, tmp1);
      n1 = bzla_exp_bv_sub(bzla, c0, c1);
      bzla_node_release(bzla, e0);
      bzla_node_release(bzla, e1);
      e0 = n0;
      e1 = n1;
    }
  }

  /* ~e0 == ~e1 is the same as e0 == e1 */
  if (bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1))
  {
    e0 = bzla_node_invert(e0);
    e1 = bzla_node_invert(e1);
  }

  *left  = e0;
  *right = e1;
}

static void
normalize_lt(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1, *tmp;

  e0 = *left;
  e1 = *right;

  /* ~a < ~b  is the same as  b < a */
  if (bzla_node_is_inverted(e0) && bzla_node_is_inverted(e1))
  {
    tmp = bzla_node_real_addr(e1);
    e1  = bzla_node_real_addr(e0);
    e0  = tmp;
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_and(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  if (bzla_node_is_bv_mul(e0) || bzla_node_is_bv_add(e1))
    normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_add(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize muls and ands on demand */
  if (bzla_node_is_bv_mul(e0) || bzla_node_is_bv_and(e0))
    normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_mul(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and ands on demand */
  if (bzla_node_is_bv_add(e0) || bzla_node_is_bv_and(e0))
    normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_udiv(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_urem(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1;

  e0 = *left;
  e1 = *right;

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands(bzla, &e0, &e1);

  *left  = e0;
  *right = e1;
}

static void
normalize_concat(Bzla *bzla, BzlaNode **left, BzlaNode **right)
{
  uint32_t i;
  BzlaMemMgr *mm;
  BzlaNode *e0, *e1, *cur, *real_cur, *tmp, *concat;
  BzlaNodePtrStack stack, po_stack;

  mm = bzla->mm;
  e0 = *left;
  e1 = *right;

  /* normalize concats --> left-associative */
  if (bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 2
      && bzla->rec_rw_calls < BZLA_REC_RW_BOUND && bzla_node_is_bv_concat(e1))
  {
    BZLA_INIT_STACK(mm, po_stack);
    BZLA_PUSH_STACK(po_stack, e0);

    BZLA_INIT_STACK(mm, stack);
    BZLA_PUSH_STACK(stack, e1);
    do
    {
      cur      = BZLA_POP_STACK(stack);
      real_cur = bzla_node_real_addr(cur);
      if (bzla_node_is_bv_concat(real_cur))
      {
        BZLA_PUSH_STACK(stack, bzla_node_cond_invert(cur, real_cur->e[1]));
        BZLA_PUSH_STACK(stack, bzla_node_cond_invert(cur, real_cur->e[0]));
      }
      else
        BZLA_PUSH_STACK(po_stack, cur);
    } while (!BZLA_EMPTY_STACK(stack));

    BZLA_INC_REC_RW_CALL(bzla);
    assert(BZLA_COUNT_STACK(po_stack) >= 3);
    cur    = BZLA_PEEK_STACK(po_stack, 0);
    tmp    = BZLA_PEEK_STACK(po_stack, 1);
    concat = rewrite_bv_concat_exp(bzla, cur, tmp);

    for (i = 2; i < BZLA_COUNT_STACK(po_stack) - 1; i++)
    {
      cur = BZLA_PEEK_STACK(po_stack, i);
      assert(!bzla_node_is_bv_concat(cur));
      tmp = rewrite_bv_concat_exp(bzla, concat, cur);
      bzla_node_release(bzla, concat);
      concat = tmp;
    }
    BZLA_DEC_REC_RW_CALL(bzla);

    bzla_node_release(bzla, e0);
    bzla_node_release(bzla, e1);
    e0 = concat;
    e1 = bzla_node_copy(bzla, BZLA_TOP_STACK(po_stack));

    BZLA_RELEASE_STACK(stack);
    BZLA_RELEASE_STACK(po_stack);
  }

  *left  = e0;
  *right = e1;
}

static inline void
normalize_cond(Bzla *bzla, BzlaNode **cond, BzlaNode **left, BzlaNode **right)
{
  BzlaNode *e0, *e1, *e2;

  e0 = *cond;
  e1 = *left;
  e2 = *right;

  /* normalization: ~e0 ? e1 : e2 is the same as e0 ? e2: e1 */
  if (bzla_node_is_inverted(e0))
  {
    e0 = bzla_node_invert(e0);
    BZLA_SWAP(BzlaNode *, e1, e2);
  }

  /* normalize adds and muls on demand */
  normalize_adds_muls_ands(bzla, &e1, &e2);

  *cond  = e0;
  *left  = e1;
  *right = e2;
}

/* -------------------------------------------------------------------------- */
/* term rewriting functions                                                   */
/* -------------------------------------------------------------------------- */

static BzlaNode *
rewrite_bv_slice_exp(Bzla *bzla, BzlaNode *e, uint32_t upper, uint32_t lower)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_SLICE_NODE;

  e = bzla_simplify_exp(bzla, e);
  assert(bzla_dbg_precond_slice_exp(bzla, e, upper, lower));

  result = check_rw_cache(bzla, kind, bzla_node_get_id(e), upper, lower, 0);

  if (!result)
  {
    ADD_RW_RULE(full_slice, e, upper, lower);
    ADD_RW_RULE(const_slice, e, upper, lower);
    ADD_RW_RULE(slice_slice, e, upper, lower);
    ADD_RW_RULE(concat_lower_slice, e, upper, lower);
    ADD_RW_RULE(concat_upper_slice, e, upper, lower);
    ADD_RW_RULE(concat_rec_upper_slice, e, upper, lower);
    ADD_RW_RULE(concat_rec_lower_slice, e, upper, lower);
    ADD_RW_RULE(concat_rec_slice, e, upper, lower);
    ADD_RW_RULE(and_slice, e, upper, lower);
    ADD_RW_RULE(bcond_slice, e, upper, lower);
    ADD_RW_RULE(zero_lower_slice, e, upper, lower);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_slice(bzla, e, upper, lower);
    }
    else
    {
    /* Note: The else branch is only active if we were able to use a rewrite
     * rule. */
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e),
                        upper,
                        lower,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_eq_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool swap_ops    = false;
  BzlaNode *result = 0;
  BzlaNodeKind kind;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_eq_exp(bzla, e0, e1));
  if (bzla_node_is_fun(e0))
  {
    kind = BZLA_FUN_EQ_NODE;
  }
  else if (bzla_node_is_bv(bzla, e0))
  {
    kind = BZLA_BV_EQ_NODE;
  }
  else if (bzla_node_is_rm(bzla, e0))
  {
    kind = BZLA_RM_EQ_NODE;
  }
  else
  {
    assert(bzla_node_is_fp(bzla, e0));
    kind = BZLA_FP_EQ_NODE;
  }

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_eq(bzla, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
      ADD_RW_RULE(const_binary_fp_bool_exp, kind, e0, e1);
      ADD_RW_RULE(const_rm_eq, e0, e1);
      /* We do not rewrite eq in the boolean case, as we cannot extract the
       * resulting XNOR on top level again and would therefore lose
       * substitutions.
       *
       * Additionally, we do not rewrite eq in the boolean case, as we rewrite
       * a != b to a = ~b and substitute.
       */
      ADD_RW_RULE(true_eq, e0, e1);
      ADD_RW_RULE(false_eq, e0, e1);
      ADD_RW_RULE(bcond_eq, e0, e1);
      ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    }
    ADD_RW_RULE(add_left_eq, e0, e1);
    ADD_RW_RULE(add_right_eq, e0, e1);
    ADD_RW_RULE(add_add_1_eq, e0, e1);
    ADD_RW_RULE(add_add_2_eq, e0, e1);
    ADD_RW_RULE(add_add_3_eq, e0, e1);
    ADD_RW_RULE(add_add_4_eq, e0, e1);
    ADD_RW_RULE(sub_eq, e0, e1);
    ADD_RW_RULE(bcond_uneq_if_eq, e0, e1);
    ADD_RW_RULE(bcond_uneq_else_eq, e0, e1);
    ADD_RW_RULE(bcond_if_eq, e0, e1);
    ADD_RW_RULE(bcond_else_eq, e0, e1);
    ADD_RW_RULE(distrib_add_mul_eq, e0, e1);
#if 0
    ADD_RW_RULE(concat_eq, e0, e1);
    ADD_RW_RULE (zero_eq_and_eq, e0, e1);
#endif

    assert(!result);
    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BZLA_SWAP(BzlaNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = bzla_node_create_eq(bzla, e1, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_ult_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_ULT_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_lt(bzla, &e0, &e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(false_lt, e0, e1);
    ADD_RW_RULE(bool_ult, e0, e1);
    ADD_RW_RULE(concat_upper_ult, e0, e1);
    ADD_RW_RULE(concat_lower_ult, e0, e1);
    ADD_RW_RULE(bcond_ult, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_ult(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_slt_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result = 0;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_lt(bzla, &e0, &e1);

  result = check_rw_cache(
      bzla, BZLA_BV_SLT_NODE, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_bv_exp, BZLA_BV_SLT_NODE, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, BZLA_BV_SLT_NODE, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, BZLA_BV_SLT_NODE, e0, e1);
    ADD_RW_RULE(false_lt, e0, e1);
    ADD_RW_RULE(bool_slt, e0, e1);
    ADD_RW_RULE(concat_lower_slt, e0, e1);
    ADD_RW_RULE(bcond_slt, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_slt(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        BZLA_BV_SLT_NODE,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_and_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool swap_ops     = false;
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_AND_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_and(bzla, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(idem1_and, e0, e1);
      ADD_RW_RULE(contr1_and, e0, e1);
      ADD_RW_RULE(contr2_and, e0, e1);
      ADD_RW_RULE(idem2_and, e0, e1);
      ADD_RW_RULE(comm_and, e0, e1);
      ADD_RW_RULE(bool_xnor_and, e0, e1);
      ADD_RW_RULE(resol1_and, e0, e1);
      ADD_RW_RULE(resol2_and, e0, e1);
      ADD_RW_RULE(lt_false_and, e0, e1);
      ADD_RW_RULE(lt_and, e0, e1);
      ADD_RW_RULE(contr_rec_and, e0, e1);
    }
    ADD_RW_RULE(subsum1_and, e0, e1);
    ADD_RW_RULE(subst1_and, e0, e1);
    ADD_RW_RULE(subst2_and, e0, e1);
    ADD_RW_RULE(subsum2_and, e0, e1);
    ADD_RW_RULE(subst3_and, e0, e1);
    ADD_RW_RULE(subst4_and, e0, e1);
    ADD_RW_RULE(contr3_and, e0, e1);
    ADD_RW_RULE(idem3_and, e0, e1);
    ADD_RW_RULE(const1_and, e0, e1);
    ADD_RW_RULE(const2_and, e0, e1);
    ADD_RW_RULE(concat_and, e0, e1);
    // ADD_RW_RULE (push_ite_and, e0, e1);

    assert(!result);

    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BZLA_SWAP(BzlaNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = bzla_node_create_bv_and(bzla, e1, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_add_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool swap_ops     = false;
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_ADD_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_add(bzla, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(bool_add, e0, e1);
      ADD_RW_RULE(mult_add, e0, e1);
      ADD_RW_RULE(not_add, e0, e1);
      ADD_RW_RULE(bcond_add, e0, e1);
      ADD_RW_RULE(urem_add, e0, e1);
    }
    ADD_RW_RULE(neg_add, e0, e1);
    ADD_RW_RULE(zero_add, e0, e1);
    ADD_RW_RULE(const_lhs_add, e0, e1);
    ADD_RW_RULE(const_rhs_add, e0, e1);
    ADD_RW_RULE(const_neg_lhs_add, e0, e1);
    ADD_RW_RULE(const_neg_rhs_add, e0, e1);
    ADD_RW_RULE(push_ite_add, e0, e1);
    ADD_RW_RULE(sll_add, e0, e1);
    ADD_RW_RULE(mul_add, e0, e1)

    assert(!result);

    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BZLA_SWAP(BzlaNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = bzla_node_create_bv_add(bzla, e1, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_mul_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  bool swap_ops     = false;
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_MUL_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_mul(bzla, &e0, &e1);

SWAP_OPERANDS:
  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    if (!swap_ops)
    {
      ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
      ADD_RW_RULE(bool_mul, e0, e1);
#if 0
      // TODO (ma): this increases mul nodes in the general case, needs restriction
      ADD_RW_RULE (bcond_mul, e0, e1);
#endif
    }
    ADD_RW_RULE(const_lhs_mul, e0, e1);
    ADD_RW_RULE(const_rhs_mul, e0, e1);
    ADD_RW_RULE(const_mul, e0, e1);
    ADD_RW_RULE(push_ite_mul, e0, e1);
    ADD_RW_RULE(sll_mul, e0, e1);
    ADD_RW_RULE(neg_mul, e0, e1);
    ADD_RW_RULE(ones_mul, e0, e1);

    assert(!result);

    /* no result so far, swap operands */
    if (!swap_ops)
    {
      BZLA_SWAP(BzlaNode *, e0, e1);
      swap_ops = true;
      goto SWAP_OPERANDS;
    }

    if (!result)
    {
      result = bzla_node_create_bv_mul(bzla, e1, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_udiv_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_UDIV_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_udiv(bzla, &e0, &e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    // TODO what about non powers of 2, like divisor 3, which means that
    // some upper bits are 0 ...

    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(bool_udiv, e0, e1);
    ADD_RW_RULE(power2_udiv, e0, e1);
    ADD_RW_RULE(one_udiv, e0, e1);
    ADD_RW_RULE(bcond_udiv, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_udiv(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_urem_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_UREM_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_regular_binary_bv_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_urem(bzla, &e0, &e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    // TODO do optimize for powers of two even AIGs do it as well !!!

    // TODO what about non powers of 2, like modulo 3, which means that
    // all but the last two bits are zero

    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(bool_urem, e0, e1);
    ADD_RW_RULE(zero_urem, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_urem(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_concat_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_CONCAT_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_concat_exp(bzla, e0, e1));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  normalize_concat(bzla, &e0, &e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(const_concat, e0, e1);
    ADD_RW_RULE(slice_concat, e0, e1);
    ADD_RW_RULE(and_lhs_concat, e0, e1);
    ADD_RW_RULE(and_rhs_concat, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_concat(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_sll_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_SLL_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(const_sll, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_sll(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  assert(result);
  return result;
}

static BzlaNode *
rewrite_bv_srl_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_BV_SRL_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_shift_exp(bzla, e0, e1));

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_bv_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_lhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(special_const_rhs_binary_exp, kind, e0, e1);
    ADD_RW_RULE(const_srl, e0, e1);
    ADD_RW_RULE(same_srl, e0, e1);
    ADD_RW_RULE(not_same_srl, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_bv_srl(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_neg_exp(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_NEG_NODE;

  e0 = bzla_simplify_exp(bzla, e0);

  result = check_rw_cache(bzla, kind, bzla_node_get_id(e0), 0, 0, 0);

  if (!result)
  {
    ADD_RW_RULE(fp_neg, e0);
    ADD_RW_RULE(const_unary_fp_exp, kind, e0);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_neg(bzla, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        0,
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_tester_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);

  BzlaNode *result = 0;

  e0 = bzla_simplify_exp(bzla, e0);

  result = check_rw_cache(bzla, kind, bzla_node_get_id(e0), 0, 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_fp_tester_exp, kind, e0);
    ADD_RW_RULE(fp_tester_sign_ops, kind, e0);

    assert(!result);
    if (!result)
    {
      switch (kind)
      {
        case BZLA_FP_IS_INF_NODE:
          result = bzla_node_create_fp_is_inf(bzla, e0);
          break;
        case BZLA_FP_IS_NAN_NODE:
          result = bzla_node_create_fp_is_nan(bzla, e0);
          break;
        case BZLA_FP_IS_NEG_NODE:
          result = bzla_node_create_fp_is_neg(bzla, e0);
          break;
        case BZLA_FP_IS_POS_NODE:
          result = bzla_node_create_fp_is_pos(bzla, e0);
          break;
        case BZLA_FP_IS_NORM_NODE:
          result = bzla_node_create_fp_is_normal(bzla, e0);
          break;
        case BZLA_FP_IS_SUBNORM_NODE:
          result = bzla_node_create_fp_is_subnormal(bzla, e0);
          break;
        default:
          assert(kind == BZLA_FP_IS_ZERO_NODE);
          result = bzla_node_create_fp_is_zero(bzla, e0);
      }
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        0,
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_to_fp_from_bv_exp(Bzla *bzla, BzlaNode *e0, BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(sort);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_TO_FP_BV_NODE;

  e0 = bzla_simplify_exp(bzla, e0);

  result = check_rw_cache(bzla, kind, bzla_node_get_id(e0), 0, sort, 0);

  if (!result)
  {
    ADD_RW_RULE(const_fp_to_fp_from_bv_exp, e0, sort);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_to_fp_from_bv(bzla, e0, sort);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        0,
                        sort,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_to_fp_from_fp_exp(Bzla *bzla,
                             BzlaNode *e0,
                             BzlaNode *e1,
                             BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(sort);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_TO_FP_FP_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), sort, 0);

  if (!result)
  {
    ADD_RW_RULE(const_fp_to_fp_from_fp_exp, e0, e1, sort);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_to_fp_from_fp(bzla, e0, e1, sort);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        sort,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_to_fp_from_sbv_exp(Bzla *bzla,
                              BzlaNode *e0,
                              BzlaNode *e1,
                              BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(sort);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_TO_FP_SBV_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), sort, 0);

  if (!result)
  {
    ADD_RW_RULE(const_fp_to_fp_from_sbv_exp, kind, e0, e1, sort);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_to_fp_from_sbv(bzla, e0, e1, sort);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        sort,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_to_fp_from_ubv_exp(Bzla *bzla,
                              BzlaNode *e0,
                              BzlaNode *e1,
                              BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(sort);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_TO_FP_UBV_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), sort, 0);

  if (!result)
  {
    ADD_RW_RULE(const_fp_to_fp_from_sbv_exp, kind, e0, e1, sort);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_to_fp_from_ubv(bzla, e0, e1, sort);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        sort,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_min_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_MIN_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(fp_min_max, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_min(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_max_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_MAX_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(fp_min_max, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_max(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_lte_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_LTE_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_fp_bool_exp, kind, e0, e1);
    ADD_RW_RULE(fp_lte, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_lte(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_lt_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_LT_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_fp_bool_exp, kind, e0, e1);
    ADD_RW_RULE(fp_lt, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_lt(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_rem_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_REM_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_fp_exp, kind, e0, e1);
    ADD_RW_RULE(fp_rem_same_divisor, e0, e1);
    ADD_RW_RULE(fp_rem_sign_divisor, e0, e1);
    ADD_RW_RULE(fp_rem_neg, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_rem(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_sqrt_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_SQRT_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_fp_rm_exp, kind, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_sqrt(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_rti_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  assert(bzla);
  assert(e0);
  assert(e1);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_RTI_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_binary_fp_rm_exp, kind, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_rti(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_add_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_ADD_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);

  result = check_rw_cache(bzla,
                          kind,
                          bzla_node_get_id(e0),
                          bzla_node_get_id(e1),
                          bzla_node_get_id(e2),
                          0);

  if (!result)
  {
    ADD_RW_RULE(const_ternary_fp_exp, kind, e0, e1, e2);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_add(bzla, e0, e1, e2);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        bzla_node_get_id(e2),
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_mul_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_MUL_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);

  result = check_rw_cache(bzla,
                          kind,
                          bzla_node_get_id(e0),
                          bzla_node_get_id(e1),
                          bzla_node_get_id(e2),
                          0);

  if (!result)
  {
    ADD_RW_RULE(const_ternary_fp_exp, kind, e0, e1, e2);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_mul(bzla, e0, e1, e2);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        bzla_node_get_id(e2),
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

static BzlaNode *
rewrite_fp_div_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_DIV_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);

  result = check_rw_cache(bzla,
                          kind,
                          bzla_node_get_id(e0),
                          bzla_node_get_id(e1),
                          bzla_node_get_id(e2),
                          0);

  if (!result)
  {
    ADD_RW_RULE(const_ternary_fp_exp, kind, e0, e1, e2);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_div(bzla, e0, e1, e2);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        bzla_node_get_id(e2),
                        0,
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  return result;
}

/* -------------------------------------------------------------------------- */

static BzlaNode *
rewrite_fp_abs_exp(Bzla *bzla, BzlaNode *e0)
{
  assert(bzla);
  assert(e0);

  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FP_ABS_NODE;

  e0 = bzla_simplify_exp(bzla, e0);

  result = check_rw_cache(bzla, kind, bzla_node_get_id(e0), 0, 0, 0);

  if (!result)
  {
    ADD_RW_RULE(fp_abs, e0);
    ADD_RW_RULE(const_unary_fp_exp, kind, e0);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_abs(bzla, e0);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        0,
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  assert(result);
  return result;
}

/* -------------------------------------------------------------------------- */

static BzlaNode *
rewrite_apply_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_APPLY_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  assert(bzla_dbg_precond_apply_exp(bzla, e0, e1));

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_lambda_apply, e0, e1);
    ADD_RW_RULE(param_lambda_apply, e0, e1);
    ADD_RW_RULE(apply_apply, e0, e1);
    ADD_RW_RULE(prop_apply_lambda, e0, e1);
    ADD_RW_RULE(prop_apply_update, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_apply(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  assert(result);
  return result;
}

static BzlaNode *
rewrite_lambda_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result = 0;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  // Note: Rewrite caching not needed since no rules applied

  // FIXME: this rule may yield lambdas with differents sorts (in case of
  // curried
  //        lambdas)
  //  ADD_RW_RULE (lambda_lambda, e0, e1);

  assert(!result);
  result = bzla_node_create_lambda(bzla, e0, e1);
  // DONE:
  assert(result);
  return result;
}

static BzlaNode *
rewrite_forall_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_FORALL_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_quantifier, e0, e1);
    ADD_RW_RULE(eq_forall, e0, e1);
    //  ADD_RW_RULE (param_free_forall, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_forall(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  assert(result);
  return result;
}

static BzlaNode *
rewrite_exists_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_EXISTS_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);

  result = check_rw_cache(
      bzla, kind, bzla_node_get_id(e0), bzla_node_get_id(e1), 0, 0);

  if (!result)
  {
    ADD_RW_RULE(const_quantifier, e0, e1);
    ADD_RW_RULE(eq_exists, e0, e1);
    //  ADD_RW_RULE (param_free_exists, e0, e1);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_exists(bzla, e0, e1);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        0,
                        0,
                        bzla_node_get_id(result));
    }
  }

  assert(result);
  return result;
}

static BzlaNode *
rewrite_cond_exp(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  BzlaNode *result  = 0;
  BzlaNodeKind kind = BZLA_COND_NODE;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  assert(bzla_dbg_precond_cond_exp(bzla, e0, e1, e2));

  e0 = bzla_node_copy(bzla, e0);
  e1 = bzla_node_copy(bzla, e1);
  e2 = bzla_node_copy(bzla, e2);
  normalize_cond(bzla, &e0, &e1, &e2);
  assert(bzla_node_is_regular(e0));

  result = check_rw_cache(bzla,
                          kind,
                          bzla_node_get_id(e0),
                          bzla_node_get_id(e1),
                          bzla_node_get_id(e2),
                          0);

  if (!result)
  {
    ADD_RW_RULE(equal_branches_cond, e0, e1, e2);
    ADD_RW_RULE(const_cond, e0, e1, e2);
    ADD_RW_RULE(cond_if_dom_cond, e0, e1, e2);
    ADD_RW_RULE(cond_if_merge_if_cond, e0, e1, e2);
    ADD_RW_RULE(cond_if_merge_else_cond, e0, e1, e2);
    ADD_RW_RULE(cond_else_dom_cond, e0, e1, e2);
    ADD_RW_RULE(cond_else_merge_if_cond, e0, e1, e2);
    ADD_RW_RULE(cond_else_merge_else_cond, e0, e1, e2);
    // TODO (ma): check if more rules can be applied for ite on bv and funs
    if (!bzla_node_is_fun(e1))
    {
      ADD_RW_RULE(bool_cond, e0, e1, e2);
      ADD_RW_RULE(add_if_cond, e0, e1, e2);
      ADD_RW_RULE(add_else_cond, e0, e1, e2);
      ADD_RW_RULE(concat_cond, e0, e1, e2);
      ADD_RW_RULE(op_lhs_cond, e0, e1, e2);
      ADD_RW_RULE(op_rhs_cond, e0, e1, e2);
      ADD_RW_RULE(comm_op_1_cond, e0, e1, e2);
      ADD_RW_RULE(comm_op_2_cond, e0, e1, e2);
    }

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_cond(bzla, e0, e1, e2);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        kind,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        bzla_node_get_id(e2),
                        0,
                        bzla_node_get_id(result));
    }
  }
  bzla_node_release(bzla, e0);
  bzla_node_release(bzla, e1);
  bzla_node_release(bzla, e2);
  assert(result);
  return result;
}

/* -------------------------------------------------------------------------- */
/* api function */

BzlaNode *
bzla_rewrite_slice_exp(Bzla *bzla,
                       BzlaNode *exp,
                       uint32_t upper,
                       uint32_t lower)
{
  assert(bzla);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;
  BzlaNode *res = rewrite_bv_slice_exp(bzla, exp, upper, lower);
  BZLA_STOP_REWRITE_TIMER;
  return res;
}

BzlaNode *
bzla_rewrite_unary_exp(Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0)
{
  assert(bzla);
  assert(kind);
  assert(e0);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;

  BzlaNode *result;

  switch (kind)
  {
    case BZLA_FP_IS_ZERO_NODE:
    case BZLA_FP_IS_INF_NODE:
    case BZLA_FP_IS_NAN_NODE:
    case BZLA_FP_IS_NEG_NODE:
    case BZLA_FP_IS_POS_NODE:
    case BZLA_FP_IS_NORM_NODE:
    case BZLA_FP_IS_SUBNORM_NODE:
      result = rewrite_fp_tester_exp(bzla, kind, e0);
      break;

    case BZLA_FP_ABS_NODE: result = rewrite_fp_abs_exp(bzla, e0); break;
    default:
      assert(kind == BZLA_FP_NEG_NODE);
      result = rewrite_fp_neg_exp(bzla, e0);
  }
  BZLA_STOP_REWRITE_TIMER;
  return result;
}

BzlaNode *
bzla_rewrite_binary_exp(Bzla *bzla,
                        BzlaNodeKind kind,
                        BzlaNode *e0,
                        BzlaNode *e1)
{
  assert(bzla);
  assert(kind);
  assert(e0);
  assert(e1);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;

  BzlaNode *result;

  switch (kind)
  {
    case BZLA_BV_EQ_NODE:
    case BZLA_FUN_EQ_NODE:
    case BZLA_FP_EQ_NODE:
    case BZLA_RM_EQ_NODE: result = rewrite_eq_exp(bzla, e0, e1); break;

    case BZLA_BV_ULT_NODE: result = rewrite_bv_ult_exp(bzla, e0, e1); break;

    case BZLA_BV_AND_NODE: result = rewrite_bv_and_exp(bzla, e0, e1); break;

    case BZLA_BV_ADD_NODE: result = rewrite_bv_add_exp(bzla, e0, e1); break;

    case BZLA_BV_MUL_NODE: result = rewrite_bv_mul_exp(bzla, e0, e1); break;

    case BZLA_BV_UDIV_NODE: result = rewrite_bv_udiv_exp(bzla, e0, e1); break;

    case BZLA_BV_UREM_NODE: result = rewrite_bv_urem_exp(bzla, e0, e1); break;

    case BZLA_BV_CONCAT_NODE:
      result = rewrite_bv_concat_exp(bzla, e0, e1);
      break;

    case BZLA_BV_SLL_NODE: result = rewrite_bv_sll_exp(bzla, e0, e1); break;

    case BZLA_BV_SLT_NODE: result = rewrite_bv_slt_exp(bzla, e0, e1); break;

    case BZLA_BV_SRL_NODE: result = rewrite_bv_srl_exp(bzla, e0, e1); break;

    case BZLA_FP_MIN_NODE: result = rewrite_fp_min_exp(bzla, e0, e1); break;
    case BZLA_FP_MAX_NODE: result = rewrite_fp_max_exp(bzla, e0, e1); break;
    case BZLA_FP_LTE_NODE: result = rewrite_fp_lte_exp(bzla, e0, e1); break;
    case BZLA_FP_LT_NODE: result = rewrite_fp_lt_exp(bzla, e0, e1); break;
    case BZLA_FP_REM_NODE: result = rewrite_fp_rem_exp(bzla, e0, e1); break;
    case BZLA_FP_SQRT_NODE: result = rewrite_fp_sqrt_exp(bzla, e0, e1); break;
    case BZLA_FP_RTI_NODE: result = rewrite_fp_rti_exp(bzla, e0, e1); break;

    case BZLA_APPLY_NODE: result = rewrite_apply_exp(bzla, e0, e1); break;

    case BZLA_FORALL_NODE: result = rewrite_forall_exp(bzla, e0, e1); break;

    case BZLA_EXISTS_NODE: result = rewrite_exists_exp(bzla, e0, e1); break;

    default:
      assert(kind == BZLA_LAMBDA_NODE);
      result = rewrite_lambda_exp(bzla, e0, e1);
  }

  BZLA_STOP_REWRITE_TIMER;
  return result;
}

BzlaNode *
bzla_rewrite_ternary_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;

  BzlaNode *res;
  switch (kind)
  {
    case BZLA_FP_ADD_NODE: res = rewrite_fp_add_exp(bzla, e0, e1, e2); break;
    case BZLA_FP_MUL_NODE: res = rewrite_fp_mul_exp(bzla, e0, e1, e2); break;
    case BZLA_FP_DIV_NODE: res = rewrite_fp_div_exp(bzla, e0, e1, e2); break;
    default:
      assert(kind == BZLA_COND_NODE);
      res = rewrite_cond_exp(bzla, e0, e1, e2);
  }
  BZLA_STOP_REWRITE_TIMER;
  return res;
}

BzlaNode *
bzla_rewrite_fp_fma_exp(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
  assert(bzla);
  assert(e0);
  assert(e1);
  assert(e2);
  assert(e3);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;

  BzlaNode *result = 0;

  e0 = bzla_simplify_exp(bzla, e0);
  e1 = bzla_simplify_exp(bzla, e1);
  e2 = bzla_simplify_exp(bzla, e2);
  e3 = bzla_simplify_exp(bzla, e3);

  result = check_rw_cache(bzla,
                          BZLA_FP_FMA_NODE,
                          bzla_node_get_id(e0),
                          bzla_node_get_id(e1),
                          bzla_node_get_id(e2),
                          bzla_node_get_id(e3));

  if (!result)
  {
    ADD_RW_RULE(const_fp_fma_exp, e0, e1, e2, e3);

    assert(!result);
    if (!result)
    {
      result = bzla_node_create_fp_fma(bzla, e0, e1, e2, e3);
    }
    else
    {
    DONE:
      bzla_rw_cache_add(bzla->rw_cache,
                        BZLA_FP_FMA_NODE,
                        bzla_node_get_id(e0),
                        bzla_node_get_id(e1),
                        bzla_node_get_id(e2),
                        bzla_node_get_id(e3),
                        bzla_node_get_id(result));
    }
  }
  assert(result);
  BZLA_STOP_REWRITE_TIMER;
  return result;
}

BzlaNode *
bzla_rewrite_unary_to_fp_exp(Bzla *bzla,
                             BzlaNodeKind kind,
                             BzlaNode *e0,
                             BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(sort);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);
  assert(kind == BZLA_FP_TO_FP_BV_NODE);
  (void) kind;

  BZLA_START_REWRITE_TIMER;
  BzlaNode *res = rewrite_fp_to_fp_from_bv_exp(bzla, e0, sort);
  BZLA_STOP_REWRITE_TIMER;
  return res;
}

BzlaNode *
bzla_rewrite_binary_to_fp_exp(
    Bzla *bzla, BzlaNodeKind kind, BzlaNode *e0, BzlaNode *e1, BzlaSortId sort)
{
  assert(bzla);
  assert(e0);
  assert(sort);
  assert(bzla_opt_get(bzla, BZLA_OPT_RW_LEVEL) > 0);

  BZLA_START_REWRITE_TIMER;

  BzlaNode *res;
  switch (kind)
  {
    case BZLA_FP_TO_FP_SBV_NODE:
      res = rewrite_fp_to_fp_from_sbv_exp(bzla, e0, e1, sort);
      break;
    case BZLA_FP_TO_FP_UBV_NODE:
      res = rewrite_fp_to_fp_from_ubv_exp(bzla, e0, e1, sort);
      break;
    default:
      assert(kind == BZLA_FP_TO_FP_FP_NODE);
      res = rewrite_fp_to_fp_from_fp_exp(bzla, e0, e1, sort);
  }
  BZLA_STOP_REWRITE_TIMER;
  return res;
}
