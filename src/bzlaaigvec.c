/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlaaigvec.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#include "bzlacore.h"
#include "bzlaopt.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

static BzlaAIGVec *
new_aigvec(BzlaAIGVecMgr *avmgr, uint32_t width)
{
  assert(avmgr);
  assert(width > 0);

  BzlaAIGVec *result;

  result        = bzla_mem_malloc(avmgr->bzla->mm,
                           sizeof(BzlaAIGVec) + sizeof(BzlaAIG *) * width);
  result->width = width;
  avmgr->cur_num_aigvecs++;
  if (avmgr->max_num_aigvecs < avmgr->cur_num_aigvecs)
    avmgr->max_num_aigvecs = avmgr->cur_num_aigvecs;
  return result;
}

BzlaAIGVec *
bzla_aigvec_const(BzlaAIGVecMgr *avmgr, const BzlaBitVector *bits)
{
  assert(avmgr);
  assert(bits);

  BzlaAIGVec *result;
  uint32_t i, width;
  width = bzla_bv_get_width(bits);
  assert(width > 0);
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] =
        !bzla_bv_get_bit(bits, width - 1 - i) ? BZLA_AIG_FALSE : BZLA_AIG_TRUE;
  return result;
}

BzlaAIGVec *
bzla_aigvec_zero(BzlaAIGVecMgr *avmgr, uint32_t width)
{
  assert(avmgr);
  assert(width);

  BzlaAIGVec *result;
  uint32_t i;
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++) result->aigs[i] = BZLA_AIG_FALSE;
  return result;
}

BzlaAIGVec *
bzla_aigvec_var(BzlaAIGVecMgr *avmgr, uint32_t width)
{
  assert(avmgr);
  assert(width > 0);

  BzlaAIGVec *result;
  uint32_t i;

  result = new_aigvec(avmgr, width);
  for (i = 1; i <= width; i++)
    result->aigs[width - i] = bzla_aig_var(avmgr->amgr);
  return result;
}

void
bzla_aigvec_invert(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av)
{
  uint32_t i, width;
  (void) avmgr;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  width = av->width;
  for (i = 0; i < width; i++) av->aigs[i] = BZLA_INVERT_AIG(av->aigs[i]);
}

BzlaAIGVec *
bzla_aigvec_not(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av)
{
  BzlaAIGVec *result;
  uint32_t i, width;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  width  = av->width;
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = bzla_aig_not(avmgr->amgr, av->aigs[i]);
  return result;
}

BzlaAIGVec *
bzla_aigvec_slice(BzlaAIGVecMgr *avmgr,
                  BzlaAIGVec *av,
                  uint32_t upper,
                  uint32_t lower)
{
  BzlaAIGVec *result;
  uint32_t i, width, diff, counter;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  assert(upper < av->width);
  assert(lower <= upper);
  counter = 0;
  width   = av->width;
  diff    = upper - lower;
  result  = new_aigvec(avmgr, diff + 1);
  for (i = width - upper - 1; i <= width - upper - 1 + diff; i++)
    result->aigs[counter++] = bzla_aig_copy(avmgr->amgr, av->aigs[i]);
  return result;
}

BzlaAIGVec *
bzla_aigvec_and(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGVec *result;
  uint32_t i, width;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);
  width  = av1->width;
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = bzla_aig_and(avmgr->amgr, av1->aigs[i], av2->aigs[i]);
  return result;
}

static BzlaAIG *
ult_aigvec(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGMgr *amgr;
  BzlaAIG *res, *tmp, *term0, *term1;
  uint32_t i, j;

  amgr = avmgr->amgr;
  res  = BZLA_AIG_FALSE;
  for (j = 1, i = av1->width - 1; j <= av1->width; j++, i--)
  {
    term0 = bzla_aig_and(amgr, av1->aigs[i], BZLA_INVERT_AIG(av2->aigs[i]));

    tmp = bzla_aig_and(amgr, BZLA_INVERT_AIG(term0), res);
    bzla_aig_release(amgr, term0);
    bzla_aig_release(amgr, res);
    res = tmp;

    term1 = bzla_aig_and(amgr, BZLA_INVERT_AIG(av1->aigs[i]), av2->aigs[i]);

    tmp = bzla_aig_or(amgr, term1, res);
    bzla_aig_release(amgr, term1);
    bzla_aig_release(amgr, res);
    res = tmp;
  }

  return res;
}

BzlaAIGVec *
bzla_aigvec_ult(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGVec *result;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);
  result          = new_aigvec(avmgr, 1);
  result->aigs[0] = ult_aigvec(avmgr, av1, av2);
  return result;
}

BzlaAIGVec *
bzla_aigvec_slt(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);

  BzlaAIGVec *res;
  BzlaAIGVec *sign1, *sign2, *sign1_inv, *sign2_inv, *r1, *r2, *av2_inv;
  BzlaAIGVec *ult, *by_sign, *by_sign_inv, *eq_sign, *eq_sign_and_ult;
  BzlaAIGVec *r, *r_inv;
  uint32_t width;

  width = av1->width;

  if (width == 1)
  {
    av2_inv = bzla_aigvec_not(avmgr, av2);
    res     = bzla_aigvec_and(avmgr, av1, av2_inv);
    bzla_aigvec_release_delete(avmgr, av2_inv);
  }
  else
  {
    /* sign bits */
    sign1 = bzla_aigvec_slice(avmgr, av1, width - 1, width - 1);
    sign2 = bzla_aigvec_slice(avmgr, av2, width - 1, width - 1);
    /* remainder without sign bits */
    r1 = bzla_aigvec_slice(avmgr, av1, width - 2, 0);
    r2 = bzla_aigvec_slice(avmgr, av2, width - 2, 0);
    /* check if left remainder is unsigned less than right remainder */
    ult = bzla_aigvec_ult(avmgr, r1, r2);

    sign1_inv = bzla_aigvec_not(avmgr, sign1);
    sign2_inv = bzla_aigvec_not(avmgr, sign2);

    /* slt is true if left sign bit is 1 and right sign bit is 0 */
    by_sign     = bzla_aigvec_and(avmgr, sign1, sign2_inv);
    by_sign_inv = bzla_aigvec_not(avmgr, by_sign);
    /* check if sign1 == sign2 */
    r       = bzla_aigvec_and(avmgr, sign1_inv, sign2);
    r_inv   = bzla_aigvec_not(avmgr, r);
    eq_sign = bzla_aigvec_and(avmgr, by_sign_inv, r_inv);

    /* if not determined by sign and sign bits are equal,
     * ult determines result */
    eq_sign_and_ult = bzla_aigvec_and(avmgr, eq_sign, ult);
    /* by_sign \/ eq_sign_and_ult */
    bzla_aigvec_invert(avmgr, eq_sign_and_ult);
    res = bzla_aigvec_and(avmgr, by_sign_inv, eq_sign_and_ult);
    bzla_aigvec_invert(avmgr, res);

    bzla_aigvec_release_delete(avmgr, eq_sign_and_ult);
    bzla_aigvec_release_delete(avmgr, eq_sign);
    bzla_aigvec_release_delete(avmgr, r_inv);
    bzla_aigvec_release_delete(avmgr, r);
    bzla_aigvec_release_delete(avmgr, by_sign);
    bzla_aigvec_release_delete(avmgr, by_sign_inv);
    bzla_aigvec_release_delete(avmgr, ult);
    bzla_aigvec_release_delete(avmgr, r2);
    bzla_aigvec_release_delete(avmgr, r1);
    bzla_aigvec_release_delete(avmgr, sign2_inv);
    bzla_aigvec_release_delete(avmgr, sign2);
    bzla_aigvec_release_delete(avmgr, sign1_inv);
    bzla_aigvec_release_delete(avmgr, sign1);
  }
  return res;
}

BzlaAIGVec *
bzla_aigvec_eq(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  BzlaAIG *result_aig, *temp1, *temp2;
  uint32_t i, width;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);
  amgr       = avmgr->amgr;
  width      = av1->width;
  result     = new_aigvec(avmgr, 1);
  result_aig = bzla_aig_eq(amgr, av1->aigs[0], av2->aigs[0]);
  for (i = 1; i < width; i++)
  {
    temp1 = bzla_aig_eq(amgr, av1->aigs[i], av2->aigs[i]);
    temp2 = bzla_aig_and(amgr, result_aig, temp1);
    bzla_aig_release(amgr, temp1);
    bzla_aig_release(amgr, result_aig);
    result_aig = temp2;
  }
  result->aigs[0] = result_aig;
  return result;
}

static BzlaAIG *
half_adder(BzlaAIGMgr *amgr, BzlaAIG *x, BzlaAIG *y, BzlaAIG **cout)
{
  BzlaAIG *res, *x_and_y, *not_x, *not_y, *not_x_and_not_y, *x_xnor_y;
  x_and_y         = bzla_aig_and(amgr, x, y);
  not_x           = BZLA_INVERT_AIG(x);
  not_y           = BZLA_INVERT_AIG(y);
  not_x_and_not_y = bzla_aig_and(amgr, not_x, not_y);
  x_xnor_y        = bzla_aig_or(amgr, x_and_y, not_x_and_not_y);
  res             = BZLA_INVERT_AIG(x_xnor_y);
  *cout           = x_and_y;
  bzla_aig_release(amgr, not_x_and_not_y);
  return res;
}

static BzlaAIG *
full_adder(
    BzlaAIGMgr *amgr, BzlaAIG *x, BzlaAIG *y, BzlaAIG *cin, BzlaAIG **cout)
{
  BzlaAIG *sum, *c1, *c2, *res;
  sum   = half_adder(amgr, x, y, &c1);
  res   = half_adder(amgr, sum, cin, &c2);
  *cout = bzla_aig_or(amgr, c1, c2);
  bzla_aig_release(amgr, sum);
  bzla_aig_release(amgr, c1);
  bzla_aig_release(amgr, c2);
  return res;
}

static int32_t
compare_aigvec_lsb_first(BzlaAIGVec *a, BzlaAIGVec *b)
{
  uint32_t width, i;
  int32_t res;
  assert(a);
  assert(b);
  width = a->width;
  assert(width == b->width);
  res = 0;
  for (i = 0; !res && i < width; i++)
    res = bzla_aig_compare(a->aigs[i], b->aigs[i]);
  return res;
}

BzlaAIGVec *
bzla_aigvec_add(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);

  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  BzlaAIG *cout, *cin;
  uint32_t i, j;

  if (bzla_opt_get(avmgr->bzla, BZLA_OPT_RW_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first(av1, av2) > 0)
  {
    BZLA_SWAP(BzlaAIGVec *, av1, av2);
  }

  amgr   = avmgr->amgr;
  result = new_aigvec(avmgr, av1->width);
  cout = cin = BZLA_AIG_FALSE; /* for 'cout' to avoid warning */
  for (j = 1, i = av1->width - 1; j <= av1->width; j++, i--)
  {
    result->aigs[i] = full_adder(amgr, av1->aigs[i], av2->aigs[i], cin, &cout);
    bzla_aig_release(amgr, cin);
    cin = cout;
  }
  bzla_aig_release(amgr, cout);
  return result;
}

static BzlaAIGVec *
sll_n_bits_aigvec(BzlaAIGVecMgr *avmgr,
                  BzlaAIGVec *av,
                  uint32_t n,
                  BzlaAIG *shift)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  BzlaAIG *and1, *and2, *not_shift;
  uint32_t i, j, width;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  assert(n < av->width);
  if (n == 0) return bzla_aigvec_copy(avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = bzla_aig_not(amgr, shift);
  result    = new_aigvec(avmgr, width);
  for (i = 0; i < width - n; i++)
  {
    and1            = bzla_aig_and(amgr, av->aigs[i], not_shift);
    and2            = bzla_aig_and(amgr, av->aigs[i + n], shift);
    result->aigs[i] = bzla_aig_or(amgr, and1, and2);
    bzla_aig_release(amgr, and1);
    bzla_aig_release(amgr, and2);
  }
  for (j = width - n; j < width; j++)
    result->aigs[j] = bzla_aig_and(amgr, av->aigs[j], not_shift);
  bzla_aig_release(amgr, not_shift);
  return result;
}

static BzlaAIGVec *
translate_shift(BzlaAIGVecMgr *avmgr,
                BzlaAIGVec *av1,
                BzlaAIGVec *av2,
                BzlaAIGVec *(*fun)(BzlaAIGVecMgr *,
                                   BzlaAIGVec *,
                                   BzlaAIGVec *) )
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width);
  assert(av2->width);

  BzlaAIGVec *res, *av_cond, *av_then, *av_else;
  BzlaAIGVec *tmp, *zero, *upper2, *lower2, *av1_new, *av2_new;
  uint32_t width, pow2, width_shift, delta1, delta2;

  width = av1->width;

  /* When represented as AIG vectors, we require that the vector to be shifted
   * has a power of 2 width, and the shift width is log2 of this width. The
   * given vectors av1 and av2 have the same bit-width, which is not necessarily
   * a power of 2. Hence the requirement for translation.
   *
   * First, we determine the smallest power of 2 that is greater/equal than
   * the bit-width of the given AIG vectors such that width_shift = log2 (pow2).
   */
  for (pow2 = 1, width_shift = 0; pow2 < width; pow2 *= 2) width_shift++;
  assert(pow2 == (1u << width_shift));

  if (width == 1)
  {
    assert(pow2 == 1);
    assert(width_shift == 0);

    tmp = bzla_aigvec_not(avmgr, av2);
    res = bzla_aigvec_and(avmgr, av1, tmp);
    bzla_aigvec_release_delete(avmgr, tmp);
  }
  else
  {
    assert(width > 1);
    assert(width <= pow2);

    /* the delta (in # bits) for 'pow2' and 'width' */
    delta1 = pow2 - width;
    /* the delta (in # bits) for 'width' and 'width_shift' (= log2(pow2)) */
    delta2 = width - width_shift;

    assert(width_shift > 0);

    upper2 = bzla_aigvec_slice(avmgr, av2, width - 1, width - delta2);
    lower2 = bzla_aigvec_slice(avmgr, av2, width_shift - 1, 0);

    assert(upper2->width == delta2);
    assert(lower2->width == width_shift);

    /**
     * if shift width is >= bit-width, result is 0
     * -> we translate given shift to
     *        ite (shift width >= bit-width, 0, shift (av1_new, av2_new))
     * where
     *   - 'shift' is the given shift function (sll, srl) and
     *   - 'av1_new' and 'av2_new' are the given vectors converted to the
     *     required widths 'pow2' and 'width_shift'.
     */

    /* condition for ite */
    if (delta2 > 1)
    {
      /* 0_[upper2->width] */
      zero = bzla_aigvec_zero(avmgr, delta2);
      /* redor: ~(0_[upper2->width] = upper2) */
      tmp     = bzla_aigvec_eq(avmgr, zero, upper2);
      av_cond = bzla_aigvec_not(avmgr, tmp);
      bzla_aigvec_release_delete(avmgr, tmp);
      bzla_aigvec_release_delete(avmgr, zero);
    }
    else
    {
      av_cond = bzla_aigvec_copy(avmgr, upper2);
    }
    bzla_aigvec_release_delete(avmgr, upper2);

    /* then branch for ite */
    av_then = bzla_aigvec_zero(avmgr, width);

    /* else branch for ite */
    if (!delta1)
    {
      av1_new = bzla_aigvec_copy(avmgr, av1);
    }
    else
    {
      tmp     = bzla_aigvec_zero(avmgr, delta1);
      av1_new = bzla_aigvec_concat(avmgr, tmp, av1);
      bzla_aigvec_release_delete(avmgr, tmp);
    }
    assert(av1_new->width == pow2);
    av2_new = lower2;
    av_else = fun(avmgr, av1_new, av2_new);
    bzla_aigvec_release_delete(avmgr, av1_new);
    bzla_aigvec_release_delete(avmgr, av2_new);
    if (delta1 > 0)
    {
      tmp = bzla_aigvec_slice(avmgr, av_else, width - 1, 0);
      bzla_aigvec_release_delete(avmgr, av_else);
      av_else = tmp;
    }

    res = bzla_aigvec_cond(avmgr, av_cond, av_then, av_else);

    bzla_aigvec_release_delete(avmgr, av_cond);
    bzla_aigvec_release_delete(avmgr, av_then);
    bzla_aigvec_release_delete(avmgr, av_else);
  }
  return res;
}

static BzlaAIGVec *
aigvec_sll(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width);
  assert(bzla_util_is_power_of_2(av1->width));
  assert(bzla_util_log_2(av1->width) == av2->width);

  BzlaAIGVec *result, *temp;
  uint32_t i, j, width;

  width  = av2->width;
  result = sll_n_bits_aigvec(avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = sll_n_bits_aigvec(
        avmgr, temp, bzla_util_pow_2(width - i - 1), av2->aigs[i]);
    bzla_aigvec_release_delete(avmgr, temp);
  }
  return result;
}

BzlaAIGVec *
bzla_aigvec_sll(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width);
  assert(av1->width == av2->width);
  return translate_shift(avmgr, av1, av2, aigvec_sll);
}

static BzlaAIGVec *
srl_n_bits_aigvec(BzlaAIGVecMgr *avmgr,
                  BzlaAIGVec *av,
                  uint32_t n,
                  BzlaAIG *shift)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  BzlaAIG *and1, *and2, *not_shift;
  uint32_t i, width;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  assert(n < av->width);
  if (n == 0) return bzla_aigvec_copy(avmgr, av);
  amgr      = avmgr->amgr;
  width     = av->width;
  not_shift = bzla_aig_not(amgr, shift);
  result    = new_aigvec(avmgr, width);
  for (i = 0; i < n; i++)
    result->aigs[i] = bzla_aig_and(amgr, av->aigs[i], not_shift);
  for (i = n; i < width; i++)
  {
    and1            = bzla_aig_and(amgr, av->aigs[i], not_shift);
    and2            = bzla_aig_and(amgr, av->aigs[i - n], shift);
    result->aigs[i] = bzla_aig_or(amgr, and1, and2);
    bzla_aig_release(amgr, and1);
    bzla_aig_release(amgr, and2);
  }
  bzla_aig_release(amgr, not_shift);
  return result;
}

static BzlaAIGVec *
aigvec_srl(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGVec *result, *temp;
  uint32_t i, j, width;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width);
  assert(bzla_util_is_power_of_2(av1->width));
  assert(bzla_util_log_2(av1->width) == av2->width);
  width  = av2->width;
  result = srl_n_bits_aigvec(avmgr, av1, 1, av2->aigs[av2->width - 1]);
  for (j = 2, i = width - 2; j <= width; j++, i--)
  {
    temp   = result;
    result = srl_n_bits_aigvec(
        avmgr, temp, bzla_util_pow_2(width - i - 1), av2->aigs[i]);
    bzla_aigvec_release_delete(avmgr, temp);
  }
  return result;
}

BzlaAIGVec *
bzla_aigvec_srl(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width);
  assert(av1->width == av2->width);
  return translate_shift(avmgr, av1, av2, aigvec_srl);
}

static BzlaAIGVec *
mul_aigvec(BzlaAIGVecMgr *avmgr, BzlaAIGVec *a, BzlaAIGVec *b)
{
  BzlaAIG *cin, *cout, *and, *tmp;
  BzlaAIGMgr *amgr;
  BzlaAIGVec *res;
  uint32_t i, j, k, ik, jk, width;

  width = a->width;
  amgr  = bzla_aigvec_get_aig_mgr(avmgr);

  assert(width > 0);
  assert(width == b->width);

  if (bzla_opt_get(avmgr->bzla, BZLA_OPT_RW_SORT_AIGVEC) > 0
      && compare_aigvec_lsb_first(a, b) > 0)
  {
    BZLA_SWAP(BzlaAIGVec *, a, b);
  }

  res = new_aigvec(avmgr, width);

  for (k = 0; k < width; k++)
    res->aigs[k] = bzla_aig_and(amgr, a->aigs[k], b->aigs[width - 1]);

  for (ik = 2, i = width - 2; ik <= width; ik++, i--)
  {
    cout = BZLA_AIG_FALSE;
    for (jk = 0, j = i; jk <= i; jk++, j--)
    {
      and          = bzla_aig_and(amgr, a->aigs[width - 1 - i + j], b->aigs[i]);
      tmp          = res->aigs[j];
      cin          = cout;
      res->aigs[j] = full_adder(amgr, tmp, and, cin, &cout);
      bzla_aig_release(amgr, and);
      bzla_aig_release(amgr, tmp);
      bzla_aig_release(amgr, cin);
    }
    bzla_aig_release(amgr, cout);
  }

  return res;
}

BzlaAIGVec *
bzla_aigvec_mul(BzlaAIGVecMgr *avmgr, BzlaAIGVec *a, BzlaAIGVec *b)
{
  return mul_aigvec(avmgr, a, b);
}

static void
SC_GATE_CO_aigvec(
    BzlaAIGMgr *amgr, BzlaAIG **CO, BzlaAIG *R, BzlaAIG *D, BzlaAIG *CI)
{
  BzlaAIG *D_or_CI, *D_and_CI, *M;
  D_or_CI  = bzla_aig_or(amgr, D, CI);
  D_and_CI = bzla_aig_and(amgr, D, CI);
  M        = bzla_aig_and(amgr, D_or_CI, R);
  *CO      = bzla_aig_or(amgr, M, D_and_CI);
  bzla_aig_release(amgr, D_or_CI);
  bzla_aig_release(amgr, D_and_CI);
  bzla_aig_release(amgr, M);
}

static void
SC_GATE_S_aigvec(BzlaAIGMgr *amgr,
                 BzlaAIG **S,
                 BzlaAIG *R,
                 BzlaAIG *D,
                 BzlaAIG *CI,
                 BzlaAIG *Q)
{
  BzlaAIG *D_and_CI, *D_or_CI;
  BzlaAIG *T2_or_R, *T2_and_R;
  BzlaAIG *T1, *T2;
  D_or_CI  = bzla_aig_or(amgr, D, CI);
  D_and_CI = bzla_aig_and(amgr, D, CI);
  T1       = bzla_aig_and(amgr, D_or_CI, BZLA_INVERT_AIG(D_and_CI));
  T2       = bzla_aig_and(amgr, T1, Q);
  T2_or_R  = bzla_aig_or(amgr, T2, R);
  T2_and_R = bzla_aig_and(amgr, T2, R);
  *S       = bzla_aig_and(amgr, T2_or_R, BZLA_INVERT_AIG(T2_and_R));
  bzla_aig_release(amgr, T1);
  bzla_aig_release(amgr, T2);
  bzla_aig_release(amgr, D_and_CI);
  bzla_aig_release(amgr, D_or_CI);
  bzla_aig_release(amgr, T2_and_R);
  bzla_aig_release(amgr, T2_or_R);
}

static void
udiv_urem_aigvec(BzlaAIGVecMgr *avmgr,
                 BzlaAIGVec *Ain,
                 BzlaAIGVec *Din,
                 BzlaAIGVec **Qptr,
                 BzlaAIGVec **Rptr)
{
  BzlaAIG **A, **nD, ***S, ***C;
  BzlaAIGVec *Q, *R;
  BzlaAIGMgr *amgr;
  BzlaMemMgr *mem;
  uint32_t size, i, j;

  size = Ain->width;
  assert(size > 0);

  amgr = bzla_aigvec_get_aig_mgr(avmgr);
  mem  = avmgr->bzla->mm;

  BZLA_NEWN(mem, A, size);
  for (i = 0; i < size; i++) A[i] = Ain->aigs[size - 1 - i];

  BZLA_NEWN(mem, nD, size);
  for (i = 0; i < size; i++) nD[i] = BZLA_INVERT_AIG(Din->aigs[size - 1 - i]);

  BZLA_NEWN(mem, S, size + 1);
  for (j = 0; j <= size; j++)
  {
    BZLA_NEWN(mem, S[j], size + 1);
    for (i = 0; i <= size; i++) S[j][i] = BZLA_AIG_FALSE;
  }

  BZLA_NEWN(mem, C, size + 1);
  for (j = 0; j <= size; j++)
  {
    BZLA_NEWN(mem, C[j], size + 1);
    for (i = 0; i <= size; i++) C[j][i] = BZLA_AIG_FALSE;
  }

  R = new_aigvec(avmgr, size);
  Q = new_aigvec(avmgr, size);

  for (j = 0; j <= size - 1; j++)
  {
    S[j][0] = bzla_aig_copy(amgr, A[size - j - 1]);
    C[j][0] = BZLA_AIG_TRUE;

    for (i = 0; i <= size - 1; i++)
      SC_GATE_CO_aigvec(amgr, &C[j][i + 1], S[j][i], nD[i], C[j][i]);

    Q->aigs[j] = bzla_aig_or(amgr, C[j][size], S[j][size]);

    for (i = 0; i <= size - 1; i++)
      SC_GATE_S_aigvec(
          amgr, &S[j + 1][i + 1], S[j][i], nD[i], C[j][i], Q->aigs[j]);
  }

  for (i = size; i >= 1; i--)
    R->aigs[size - i] = bzla_aig_copy(amgr, S[size][i]);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) bzla_aig_release(amgr, C[j][i]);
    BZLA_DELETEN(mem, C[j], size + 1);
  }
  BZLA_DELETEN(mem, C, size + 1);

  for (j = 0; j <= size; j++)
  {
    for (i = 0; i <= size; i++) bzla_aig_release(amgr, S[j][i]);
    BZLA_DELETEN(mem, S[j], size + 1);
  }
  BZLA_DELETEN(mem, S, size + 1);

  BZLA_DELETEN(mem, nD, size);
  BZLA_DELETEN(mem, A, size);

  *Qptr = Q;
  *Rptr = R;
}

BzlaAIGVec *
bzla_aigvec_udiv(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGVec *quotient  = 0;
  BzlaAIGVec *remainder = 0;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);
  udiv_urem_aigvec(avmgr, av1, av2, &quotient, &remainder);
  bzla_aigvec_release_delete(avmgr, remainder);
  return quotient;
}

BzlaAIGVec *
bzla_aigvec_urem(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGVec *quotient, *remainder;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width == av2->width);
  assert(av1->width > 0);
  udiv_urem_aigvec(avmgr, av1, av2, &quotient, &remainder);
  bzla_aigvec_release_delete(avmgr, quotient);
  return remainder;
}

BzlaAIGVec *
bzla_aigvec_concat(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av1, BzlaAIGVec *av2)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  uint32_t i, pos, len_av1, len_av2;
  assert(avmgr);
  assert(av1);
  assert(av2);
  assert(av1->width > 0);
  assert(av2->width > 0);
  assert(INT32_MAX - av1->width >= av2->width);
  pos     = 0;
  amgr    = avmgr->amgr;
  len_av1 = av1->width;
  len_av2 = av2->width;
  result  = new_aigvec(avmgr, len_av1 + len_av2);
  for (i = 0; i < len_av1; i++)
    result->aigs[pos++] = bzla_aig_copy(amgr, av1->aigs[i]);
  for (i = 0; i < len_av2; i++)
    result->aigs[pos++] = bzla_aig_copy(amgr, av2->aigs[i]);
  return result;
}

BzlaAIGVec *
bzla_aigvec_cond(BzlaAIGVecMgr *avmgr,
                 BzlaAIGVec *av_cond,
                 BzlaAIGVec *av_if,
                 BzlaAIGVec *av_else)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  uint32_t i, width;
  assert(avmgr);
  assert(av_cond);
  assert(av_if);
  assert(av_else);
  assert(av_cond->width == 1);
  assert(av_if->width == av_else->width);
  assert(av_if->width > 0);
  amgr   = avmgr->amgr;
  width  = av_if->width;
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] =
        bzla_aig_cond(amgr, av_cond->aigs[0], av_if->aigs[i], av_else->aigs[i]);
  return result;
}

BzlaAIGVec *
bzla_aigvec_copy(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av)
{
  BzlaAIGMgr *amgr;
  BzlaAIGVec *result;
  uint32_t i, width;
  assert(avmgr);
  assert(av);
  amgr   = avmgr->amgr;
  width  = av->width;
  result = new_aigvec(avmgr, width);
  for (i = 0; i < width; i++)
    result->aigs[i] = bzla_aig_copy(amgr, av->aigs[i]);
  return result;
}

BzlaAIGVec *
bzla_aigvec_clone(BzlaAIGVec *av, BzlaAIGVecMgr *avmgr)
{
  assert(av);
  assert(avmgr);

  uint32_t i;
  BzlaAIGVec *res;
  BzlaAIGMgr *amgr;
  BzlaAIG *aig, *caig;

  amgr = avmgr->amgr;
  res  = new_aigvec(avmgr, av->width);
  for (i = 0; i < av->width; i++)
  {
    if (bzla_aig_is_const(av->aigs[i]))
      res->aigs[i] = av->aigs[i];
    else
    {
      aig = av->aigs[i];
      assert(BZLA_REAL_ADDR_AIG(aig)->id >= 0);
      assert((size_t) BZLA_REAL_ADDR_AIG(aig)->id
             < BZLA_COUNT_STACK(amgr->id2aig));
      caig = BZLA_PEEK_STACK(amgr->id2aig, BZLA_REAL_ADDR_AIG(aig)->id);
      assert(caig);
      assert(!bzla_aig_is_const(caig));
      if (BZLA_IS_INVERTED_AIG(aig))
        res->aigs[i] = BZLA_INVERT_AIG(caig);
      else
        res->aigs[i] = caig;
      assert(res->aigs[i]);
    }
  }
  return res;
}

void
bzla_aigvec_to_sat_tseitin(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av)
{
  BzlaAIGMgr *amgr;
  uint32_t i, width;
  assert(avmgr);
  assert(av);
  amgr = bzla_aigvec_get_aig_mgr(avmgr);
  if (!bzla_sat_is_initialized(amgr->smgr)) return;
  width = av->width;
  for (i = 0; i < width; i++) bzla_aig_to_sat_tseitin(amgr, av->aigs[i]);
}

void
bzla_aigvec_release_delete(BzlaAIGVecMgr *avmgr, BzlaAIGVec *av)
{
  BzlaMemMgr *mm;
  BzlaAIGMgr *amgr;
  uint32_t i, width;
  assert(avmgr);
  assert(av);
  assert(av->width > 0);
  mm    = avmgr->bzla->mm;
  amgr  = avmgr->amgr;
  width = av->width;
  for (i = 0; i < width; i++) bzla_aig_release(amgr, av->aigs[i]);
  bzla_mem_free(mm, av, sizeof(BzlaAIGVec) + sizeof(BzlaAIG *) * av->width);
  avmgr->cur_num_aigvecs--;
}

BzlaAIGVecMgr *
bzla_aigvec_mgr_new(Bzla *bzla)
{
  assert(bzla);

  BzlaAIGVecMgr *avmgr;
  BZLA_CNEW(bzla->mm, avmgr);
  avmgr->bzla = bzla;
  avmgr->amgr = bzla_aig_mgr_new(bzla);
  return avmgr;
}

BzlaAIGVecMgr *
bzla_aigvec_mgr_clone(Bzla *bzla, BzlaAIGVecMgr *avmgr)
{
  assert(bzla);
  assert(avmgr);

  BzlaAIGVecMgr *res;
  BZLA_NEW(bzla->mm, res);

  res->bzla            = bzla;
  res->amgr            = bzla_aig_mgr_clone(bzla, avmgr->amgr);
  res->max_num_aigvecs = avmgr->max_num_aigvecs;
  res->cur_num_aigvecs = avmgr->cur_num_aigvecs;
  return res;
}

void
bzla_aigvec_mgr_delete(BzlaAIGVecMgr *avmgr)
{
  assert(avmgr);
  bzla_aig_mgr_delete(avmgr->amgr);
  BZLA_DELETE(avmgr->bzla->mm, avmgr);
}

BzlaAIGMgr *
bzla_aigvec_get_aig_mgr(const BzlaAIGVecMgr *avmgr)
{
  return avmgr ? avmgr->amgr : 0;
}
