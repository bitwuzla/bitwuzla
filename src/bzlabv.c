/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "bzlabv.h"

#include <limits.h>

#include "bzlaaig.h"
#include "bzlaaigvec.h"
#include "bzlabvstruct.h"
#include "bzlacore.h"
#include "utils/bzlautil.h"

/*------------------------------------------------------------------------*/

#ifndef NDEBUG
static bool
check_bits_sll_dbg(const BzlaBitVector *bv,
                   const BzlaBitVector *res,
                   uint32_t shift)
{
  assert(bv);
  assert(res);
  assert(bv->width == res->width);

  uint32_t i;

  if (shift >= bv->width)
  {
    for (i = 0; i < bv->width; i++) assert(bzla_bv_get_bit(bv, i) == 0);
  }
  else
  {
    for (i = 0; shift + i < bv->width; i++)
      assert(bzla_bv_get_bit(bv, i) == bzla_bv_get_bit(res, shift + i));
  }

  return true;
}
#endif

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_new(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw > 0);

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init(res->val);

  return res;
}

BzlaBitVector *
bzla_bv_new_random(BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw)
{
  BzlaBitVector *res;

  res = bzla_bv_new(mm, bw);
  mpz_urandomb(res->val, *((gmp_randstate_t *) rng->gmp_state), bw);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_new_random_range(BzlaMemMgr *mm,
                         BzlaRNG *rng,
                         uint32_t bw,
                         const BzlaBitVector *from,
                         const BzlaBitVector *to)
{
  assert(mm);
  assert(rng);
  assert(bw > 0);
  assert(bw == from->width);
  assert(from->width == to->width);
  assert(bzla_bv_compare(from, to) <= 0);

  BzlaBitVector *res;

  mpz_t n_to;

  res = bzla_bv_new(mm, bw);
  mpz_init_set(n_to, to->val);
  mpz_sub(n_to, n_to, from->val);
  mpz_add_ui(n_to, n_to, 1);

  mpz_urandomm(res->val, *((gmp_randstate_t *) rng->gmp_state), n_to);
  mpz_add(res->val, res->val, from->val);
  mpz_clear(n_to);

  return res;
}

BzlaBitVector *
bzla_bv_new_random_signed_range(BzlaMemMgr *mm,
                                BzlaRNG *rng,
                                uint32_t bw,
                                const BzlaBitVector *from,
                                const BzlaBitVector *to)
{
  assert(mm);
  assert(rng);
  assert(bw > 0);
  assert(bw == from->width);
  assert(from->width == to->width);
  assert(bzla_bv_signed_compare(from, to) <= 0);

  BzlaBitVector *zero, *diff, *tmp, *res;

  /* difference */
  diff = bzla_bv_sub(mm, to, from);
  /* pick from [0, diff] */
  zero = bzla_bv_zero(mm, bw);
  tmp  = bzla_bv_new_random_range(mm, rng, bw, zero, diff);
  /* add picked value to from */
  res = bzla_bv_add(mm, from, tmp);

  bzla_bv_free(mm, tmp);
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, diff);
  return res;
}

BzlaBitVector *
bzla_bv_new_random_bit_range(
    BzlaMemMgr *mm, BzlaRNG *rng, uint32_t bw, uint32_t up, uint32_t lo)
{
  assert(mm);
  assert(rng);
  assert(bw > 0);
  assert(lo <= up);

  uint32_t i;
  BzlaBitVector *res;

  res = bzla_bv_new_random(mm, rng, bw);
  for (i = 0; i < lo; i++) bzla_bv_set_bit(res, i, 0);
  for (i = up + 1; i < res->width; i++) bzla_bv_set_bit(res, i, 0);

  return res;
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_char_to_bv(BzlaMemMgr *mm, const char *assignment)
{
  assert(mm);
  assert(assignment);
  assert(strlen(assignment) > 0);

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = strlen(assignment);
  mpz_init_set_str(res->val, assignment, 2);

  return res;
}

BzlaBitVector *
bzla_bv_uint64_to_bv(BzlaMemMgr *mm, uint64_t value, uint32_t bw)
{
  assert(mm);
  assert(bw > 0);

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_ui(res->val, value);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_int64_to_bv(BzlaMemMgr *mm, int64_t value, uint32_t bw)
{
  assert(mm);
  assert(bw > 0);

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_si(res->val, value);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_const(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_bin_to_bv(mm, str, bw));

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_str(res->val, str, 2);

  return res;
}

BzlaBitVector *
bzla_bv_constd(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_dec_to_bv(mm, str, bw));

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_str(res->val, str, 10);
  /* We assert that given string must fit into bw after conversion. However,
   * However, we still need to normalize negative values. Negative values are
   * represented as "-xxx" (where xxx is the binary representation of the
   * absolute value of 'value') in GMP when created from mpz_init_set_str. */
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_consth(BzlaMemMgr *mm, const char *str, uint32_t bw)
{
  assert(bzla_util_check_hex_to_bv(mm, str, bw));

  BzlaBitVector *res;

  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_str(res->val, str, 16);

  return res;
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_copy(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;

  res = bzla_bv_new(mm, bv->width);
  assert(res->width == bv->width);
  mpz_set(res->val, bv->val);
  assert(bzla_bv_compare(res, (BzlaBitVector *) bv) == 0);

  return res;
}

/*------------------------------------------------------------------------*/

size_t
bzla_bv_size(const BzlaBitVector *bv)
{
  assert(bv);
  (void) bv;
  return sizeof(BzlaBitVector);
}

void
bzla_bv_free(BzlaMemMgr *mm, BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);
  mpz_clear(bv->val);
  bzla_mem_free(mm, bv, sizeof(BzlaBitVector));
}

int32_t
bzla_bv_compare(const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(a);
  assert(b);

  if (a->width != b->width) return -1;
  return mpz_cmp(a->val, b->val);
}

int32_t
bzla_bv_signed_compare(const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(a);
  assert(b);

  uint32_t bw, msb_a, msb_b;
  int32_t res;

  bw    = a->width;
  msb_a = bzla_bv_get_bit(a, bw - 1);
  msb_b = bzla_bv_get_bit(b, bw - 1);

  if (msb_a && !msb_b)
  {
    res = -1;
  }
  else if (!msb_a && msb_b)
  {
    res = 1;
  }
  else
  {
    res = bzla_bv_compare(a, b);
  }
  return res;
}

static uint32_t hash_primes[] = {333444569u, 76891121u, 456790003u};

#define NPRIMES ((uint32_t)(sizeof hash_primes / sizeof *hash_primes))

uint32_t
bzla_bv_hash(const BzlaBitVector *bv)
{
  assert(bv);

  uint32_t i, j = 0, n, res = 0;
  uint32_t x, p0, p1;

  res = bv->width * hash_primes[j++];

  // least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 0, n = mpz_size(bv->val); i < n; ++i)
  {
    p0 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    p1 = hash_primes[j++];
    if (j == NPRIMES) j = 0;
    limb = mpz_getlimbn(bv->val, i);
    if (mp_bits_per_limb == 64)
    {
      uint32_t lo = (uint32_t) limb;
      uint32_t hi = (uint32_t)(limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      p1 = hash_primes[j++];
      if (j == NPRIMES) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert(mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }

  return res;
}

/*------------------------------------------------------------------------*/

void
bzla_bv_print_without_new_line(const BzlaBitVector *bv)
{
  assert(bv);

  int64_t i;
  for (i = bv->width - 1; i >= 0; i--) printf("%d", bzla_bv_get_bit(bv, i));
}

void
bzla_bv_print(const BzlaBitVector *bv)
{
  bzla_bv_print_without_new_line(bv);
  printf("\n");
}

/*------------------------------------------------------------------------*/

char *
bzla_bv_to_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  char *res;
  uint64_t bw = bv->width;

  BZLA_CNEWN(mm, res, bw + 1);
  char *tmp     = mpz_get_str(0, 2, bv->val);
  assert(tmp[0] == '1' || tmp[0] == '0');  // may not be negative
  uint64_t n    = strlen(tmp);
  uint64_t diff = bw - n;
  assert(n <= bw);
  memset(res, '0', diff);
  memcpy(res + diff, tmp, n);
  assert(strlen(res) == bw);
  free(tmp);
  return res;
}

char *
bzla_bv_to_hex_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  char *res;
  uint32_t len;

  len = (bv->width + 3) / 4;
  BZLA_CNEWN(mm, res, len + 1);

  char *tmp     = mpz_get_str(0, 16, bv->val);
  uint32_t n    = strlen(tmp);
  uint32_t diff = len - n;
  assert(n <= len);
  memset(res, '0', diff);
  memcpy(res + diff, tmp, n);
  assert(strlen(res) == len);
  free(tmp);
  return res;
}

static uint32_t
get_first_one_bit_idx(const BzlaBitVector *bv)
{
  assert(bv);
  return mpz_scan1(bv->val, 0);
}

static uint32_t
get_first_zero_bit_idx(const BzlaBitVector *bv)
{
  assert(bv);
  return mpz_scan0(bv->val, 0);
}

char *
bzla_bv_to_dec_char(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  char *res;

  char *tmp = mpz_get_str(0, 10, bv->val);
  res       = bzla_mem_strdup(mm, tmp);
  free(tmp);

  return res;
}

/*------------------------------------------------------------------------*/

uint64_t
bzla_bv_to_uint64(const BzlaBitVector *bv)
{
  assert(bv);
  assert(bv->width <= sizeof(uint64_t) * 8);
  return mpz_get_ui(bv->val);
}

/*------------------------------------------------------------------------*/

uint32_t
bzla_bv_get_width(const BzlaBitVector *bv)
{
  assert(bv);
  return bv->width;
}

uint32_t
bzla_bv_get_len(const BzlaBitVector *bv)
{
  assert(bv);
  (void) bv;
  return 0;
}

uint32_t
bzla_bv_get_bit(const BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);
  assert(pos < bv->width);
  return mpz_tstbit(bv->val, pos);
}

void
bzla_bv_set_bit(BzlaBitVector *bv, uint32_t pos, uint32_t bit)
{
  assert(bv);
  assert(bit == 0 || bit == 1);
  assert(pos < bv->width);

  if (bit)
  {
    mpz_setbit(bv->val, pos);
  }
  else
  {
    mpz_clrbit(bv->val, pos);
  }
}

void
bzla_bv_flip_bit(BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);
  assert(pos < bv->width);
  mpz_combit(bv->val, pos);
}

/*------------------------------------------------------------------------*/

bool
bzla_bv_is_true(const BzlaBitVector *bv)
{
  assert(bv);

  if (bv->width != 1) return 0;
  return bzla_bv_get_bit(bv, 0);
}

bool
bzla_bv_is_false(const BzlaBitVector *bv)
{
  assert(bv);

  if (bv->width != 1) return 0;
  return !bzla_bv_get_bit(bv, 0);
}

bool
bzla_bv_is_zero(const BzlaBitVector *bv)
{
  assert(bv);
  return mpz_cmp_ui(bv->val, 0) == 0;
}

bool
bzla_bv_is_ones(const BzlaBitVector *bv)
{
  assert(bv);

  uint32_t i, n;
  uint64_t m, max;
  mp_limb_t limb;
  if ((n = mpz_size(bv->val)) == 0) return false;  // zero
  m = bv->width / mp_bits_per_limb;
  if (bv->width % mp_bits_per_limb) m += 1;
  if (m != n) return false;  // less limbs used than expected, not ones
  max = mp_bits_per_limb == 64 ? UINT64_MAX : UINT32_MAX;
  for (i = 0; i < n - 1; i++)
  {
    limb = mpz_getlimbn(bv->val, i);
    if (((uint64_t) limb) != max) return false;
  }
  limb = mpz_getlimbn(bv->val, n - 1);
  if (bv->width == (uint32_t) mp_bits_per_limb) return ((uint64_t) limb) == max;
  m = mp_bits_per_limb - bv->width % mp_bits_per_limb;
  return ((uint64_t) limb) == (max >> m);
}

bool
bzla_bv_is_one(const BzlaBitVector *bv)
{
  assert(bv);
  return mpz_cmp_ui(bv->val, 1) == 0;
}

bool
bzla_bv_is_min_signed(const BzlaBitVector *bv)
{
  assert(bv);
  if (get_first_one_bit_idx(bv) != bv->width - 1) return false;
  return true;
}

bool
bzla_bv_is_max_signed(const BzlaBitVector *bv)
{
  assert(bv);
  if (get_first_zero_bit_idx(bv) != bv->width - 1) return false;
  return true;
}

int64_t
bzla_bv_power_of_two(const BzlaBitVector *bv)
{
  assert(bv);

  int64_t i, j;
  uint32_t bit;
  bool iszero;

  for (i = 0, j = 0, iszero = true; i < bv->width; i++)
  {
    bit = bzla_bv_get_bit(bv, i);
    if (!bit) continue;
    if (bit && !iszero) return -1;
    assert(bit && iszero);
    j      = i;
    iszero = false;
  }
  return j;
}

int32_t
bzla_bv_small_positive_int(const BzlaBitVector *bv)
{
  assert(bv);

  int32_t res;
  uint32_t i, n;
  if (!(n = mpz_size(bv->val))) return 0;
  mp_limb_t limb;
  for (i = 0; i < n; i++)
  {
    limb = mpz_getlimbn(bv->val, i);
    if (i == n - 1)
    {
      if (mp_bits_per_limb == 64)
      {
        if (limb >> 32 != 0)
        {
          return -1;
        }
      }
    }
    else
    {
      if (limb != 0)
      {
        return -1;
      }
    }
  }
  res = (int32_t) limb;
  if (res < 0) return -1;
  return res;
}

uint32_t
bzla_bv_get_num_trailing_zeros(const BzlaBitVector *bv)
{
  assert(bv);

  uint32_t res = 0;
  res = mpz_scan1(bv->val, 0);
  if (res > bv->width) res = bv->width;
  return res;
}

/**
 * Get the first limb and return the number of limbs needed to represented
 * given bit-vector if all zero limbs are disregarded.
 */
static uint32_t
get_limb(const BzlaBitVector *bv,
         mp_limb_t *limb,
         uint32_t nbits_rem,
         bool zeros)
{
  /* GMP normalizes the limbs, the left most (most significant) is never 0 */
  uint32_t i, n_limbs, n_limbs_total;
  mp_limb_t res = 0u, mask;

  n_limbs = mpz_size(bv->val);

  /* for leading zeros */
  if (zeros)
  {
    *limb = n_limbs ? mpz_getlimbn(bv->val, n_limbs - 1) : 0;
    return n_limbs;
  }

  /* for leading ones */
  n_limbs_total = bv->width / mp_bits_per_limb + (nbits_rem ? 1 : 0);
  if (n_limbs != n_limbs_total)
  {
    /* no leading ones, simulate */
    *limb = nbits_rem ? ~(~((mp_limb_t) 0) << nbits_rem) : ~((mp_limb_t) 0);
    return n_limbs_total;
  }
  mask = ~((mp_limb_t) 0) << nbits_rem;
  for (i = 0; i < n_limbs; i++)
  {
    res = mpz_getlimbn(bv->val, n_limbs - 1 - i);
    if (nbits_rem && i == 0)
    {
      res = res | mask;
    }
    res = ~res;
    if (res > 0) break;
  }
  *limb = res;
  return n_limbs - i;
}

#if !defined(__GNUC__) && !defined(__clang__)
static uint32_t
clz_limb(uint32_t nbits_per_limb, mp_limb_t limb)
{
  uint32_t w;
  mp_limb_t mask;
  mp_limb_t one = 1u;
  for (w = 0, mask = 0; w < nbits_per_limb; w++)
  {
    mask += (one << w);
    if ((limb & ~mask) == 0) break;
  }
  return nbits_per_limb - 1 - w;
}
#endif

static uint32_t
get_num_leading(const BzlaBitVector *bv, bool zeros)
{
  assert(bv);

  uint32_t res = 0, nbits_pad;
  /* The number of limbs required to represent the actual value.
   * Zero limbs are disregarded. */
  uint32_t n_limbs;
  /* Number of limbs required when representing all bits. */
  uint32_t n_limbs_total;
  /* The number of bits that spill over into the most significant limb,
   * assuming that all bits are represented). Zero if the bit-width is a
   * multiple of n_bits_per_limb. */
  uint32_t nbits_rem;
  uint32_t nbits_per_limb;
  mp_limb_t limb;

  nbits_per_limb = mp_bits_per_limb;
  nbits_rem = bv->width % nbits_per_limb;
  n_limbs = get_limb(bv, &limb, nbits_rem, zeros);
  if (n_limbs == 0) return bv->width;

#if defined(__GNUC__) || defined(__clang__)
  res = nbits_per_limb == 64 ? __builtin_clzll(limb) : __builtin_clz(limb);
#else
  res = clz_limb(nbits_per_limb, limb);
#endif
  n_limbs_total = bv->width / nbits_per_limb + 1;
  nbits_pad     = nbits_per_limb - nbits_rem;
  res += (n_limbs_total - n_limbs) * nbits_per_limb - nbits_pad;
  return res;
}

uint32_t
bzla_bv_get_num_leading_zeros(const BzlaBitVector *bv)
{
  assert(bv);
  return get_num_leading(bv, true);
}

uint32_t
bzla_bv_get_num_leading_ones(const BzlaBitVector *bv)
{
  assert(bv);
  return get_num_leading(bv, false);
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_one(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  BZLA_NEW(mm, res);
  res->width = bw;
  mpz_init_set_ui(res->val, 1);
  return res;
}

BzlaBitVector *
bzla_bv_ones(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  res = bzla_bv_one(mm, bw);
  mpz_mul_2exp(res->val, res->val, bw);
  mpz_sub_ui(res->val, res->val, 1);
  return res;
}

BzlaBitVector *
bzla_bv_min_signed(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  res = bzla_bv_new(mm, bw);
  mpz_setbit(res->val, bw - 1);
  return res;
}

BzlaBitVector *
bzla_bv_max_signed(BzlaMemMgr *mm, uint32_t bw)
{
  assert(mm);
  assert(bw);

  BzlaBitVector *res;
  res = bzla_bv_ones(mm, bw);
  bzla_bv_set_bit(res, bw - 1, 0);
  return res;
}

BzlaBitVector *
bzla_bv_neg(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw = bv->width;
  res = bzla_bv_not(mm, bv);
  mpz_add_ui(res->val, res->val, 1);
  mpz_fdiv_r_2exp(res->val, res->val, bw);
  return res;
}

BzlaBitVector *
bzla_bv_not(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw = bv->width;
  res = bzla_bv_new(mm, bw);
  mpz_com(res->val, bv->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);
  return res;
}

BzlaBitVector *
bzla_bv_inc(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw = bv->width;
  res = bzla_bv_new(mm, bw);
  mpz_add_ui(res->val, bv->val, 1);
  mpz_fdiv_r_2exp(res->val, res->val, bw);
  return res;
}

BzlaBitVector *
bzla_bv_dec(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw = bv->width;
  res = bzla_bv_new(mm, bw);
  mpz_sub_ui(res->val, bv->val, 1);
  mpz_fdiv_r_2exp(res->val, res->val, bw);
  return res;
}

BzlaBitVector *
bzla_bv_redand(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);
  return bzla_bv_is_ones(bv) ? bzla_bv_one(mm, 1) : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_redor(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  mp_limb_t limb;
  size_t i, n;
  for (i = 0, n = mpz_size(bv->val); i < n; i++)
  {
    limb = mpz_getlimbn(bv->val, i);
    if (((uint64_t) limb) != 0) return bzla_bv_one(mm, 1);
  }
  return bzla_bv_zero(mm, 1);
}

/*------------------------------------------------------------------------*/

BzlaBitVector *
bzla_bv_add(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;

  uint32_t bw = a->width;
  res         = bzla_bv_new(mm, bw);
  mpz_add(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_sub(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;

  uint32_t bw = a->width;
  res         = bzla_bv_new(mm, bw);
  mpz_sub(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_and(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_and(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_implies(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);
  assert(a->width == 1);

  return bzla_bv_is_zero(a) || bzla_bv_is_one(b) ? bzla_bv_one(mm, 1)
                                                 : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_or(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_ior(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_nand(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_and(res->val, a->val, b->val);
  mpz_com(res->val, res->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_nor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_ior(res->val, a->val, b->val);
  mpz_com(res->val, res->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_xnor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_xor(res->val, a->val, b->val);
  mpz_com(res->val, res->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_xor(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_xor(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_eq(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) == 0 ? bzla_bv_one(mm, 1)
                                      : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_ne(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) != 0 ? bzla_bv_one(mm, 1)
                                      : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_ult(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) < 0 ? bzla_bv_one(mm, 1) : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_ulte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) <= 0 ? bzla_bv_one(mm, 1)
                                      : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_ugt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) > 0 ? bzla_bv_one(mm, 1) : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_ugte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  return mpz_cmp(a->val, b->val) >= 0 ? bzla_bv_one(mm, 1)
                                      : bzla_bv_zero(mm, 1);
}

BzlaBitVector *
bzla_bv_slt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = bzla_bv_get_bit(a, bw - 1);
  msb_b = bzla_bv_get_bit(b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = bzla_bv_one(mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = bzla_bv_zero(mm, 1);
  }
  else
  {
    res = bzla_bv_ult(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_slte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = bzla_bv_get_bit(a, bw - 1);
  msb_b = bzla_bv_get_bit(b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = bzla_bv_one(mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = bzla_bv_zero(mm, 1);
  }
  else
  {
    res = bzla_bv_ulte(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_sgt(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = bzla_bv_get_bit(a, bw - 1);
  msb_b = bzla_bv_get_bit(b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = bzla_bv_zero(mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = bzla_bv_one(mm, 1);
  }
  else
  {
    res = bzla_bv_ugt(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_sgte(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw, msb_a, msb_b;

  bw    = a->width;
  msb_a = bzla_bv_get_bit(a, bw - 1);
  msb_b = bzla_bv_get_bit(b, bw - 1);
  if (msb_a && !msb_b)
  {
    res = bzla_bv_zero(mm, 1);
  }
  else if (!msb_a && msb_b)
  {
    res = bzla_bv_one(mm, 1);
  }
  else
  {
    res = bzla_bv_ugte(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_sll_uint64(BzlaMemMgr *mm, const BzlaBitVector *a, uint64_t shift)
{
  assert(mm);
  assert(a);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  if (shift >= bw) return res;

  mpz_mul_2exp(res->val, a->val, shift);
  mpz_fdiv_r_2exp(res->val, res->val, bw);
  assert(check_bits_sll_dbg(a, res, shift));

  return res;
}

static bool
shift_is_uint64(BzlaMemMgr *mm, const BzlaBitVector *b, uint64_t *res)
{
  assert(mm);
  assert(b);
  assert(res);

  uint64_t zeroes;
  BzlaBitVector *shift;

  if (b->width <= 64)
  {
    *res = bzla_bv_to_uint64(b);
    return true;
  }

  zeroes = bzla_bv_get_num_leading_zeros(b);
  if (zeroes < b->width - 64) return false;

  shift =
      bzla_bv_slice(mm, b, zeroes < b->width ? b->width - 1 - zeroes : 0, 0);
  assert(shift->width <= 64);
  *res = bzla_bv_to_uint64(shift);
  bzla_bv_free(mm, shift);
  return true;
}

BzlaBitVector *
bzla_bv_sll(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64(mm, b, &ushift))
  {
    return bzla_bv_sll_uint64(mm, a, ushift);
  }
  return bzla_bv_new(mm, a->width);
}

BzlaBitVector *
bzla_bv_sra(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  if (bzla_bv_get_bit(a, a->width - 1))
  {
    BzlaBitVector *not_a       = bzla_bv_not(mm, a);
    BzlaBitVector *not_a_srl_b = bzla_bv_srl(mm, not_a, b);
    res                        = bzla_bv_not(mm, not_a_srl_b);
    bzla_bv_free(mm, not_a);
    bzla_bv_free(mm, not_a_srl_b);
  }
  else
  {
    res = bzla_bv_srl(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_srl_uint64(BzlaMemMgr *mm, const BzlaBitVector *a, uint64_t shift)
{
  assert(mm);
  assert(a);

  BzlaBitVector *res;

  res = bzla_bv_new(mm, a->width);
  if (shift >= a->width) return res;
  mpz_fdiv_q_2exp(res->val, a->val, shift);

  return res;
}

BzlaBitVector *
bzla_bv_srl(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  uint64_t ushift;

  if (shift_is_uint64(mm, b, &ushift))
  {
    return bzla_bv_srl_uint64(mm, a, ushift);
  }
  return bzla_bv_new(mm, a->width);
}

BzlaBitVector *
bzla_bv_mul(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  res = bzla_bv_new(mm, bw);
  mpz_mul(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

void
bzla_bv_udiv_urem(BzlaMemMgr *mm,
                  const BzlaBitVector *a,
                  const BzlaBitVector *b,
                  BzlaBitVector **q,
                  BzlaBitVector **r)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  uint32_t bw = a->width;

  if (bzla_bv_is_zero(b))
  {
    *q = bzla_bv_ones(mm, bw);
    *r = bzla_bv_copy(mm, a);
  }
  else
  {
    *q = bzla_bv_new(mm, bw);
    *r = bzla_bv_new(mm, bw);
    mpz_fdiv_qr((*q)->val, (*r)->val, a->val, b->val);
    mpz_fdiv_r_2exp((*q)->val, (*q)->val, bw);
    mpz_fdiv_r_2exp((*r)->val, (*r)->val, bw);
  }
}

BzlaBitVector *
bzla_bv_udiv(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  if (bzla_bv_is_zero(b)) return bzla_bv_ones(mm, bw);
  res = bzla_bv_new(mm, bw);
  mpz_fdiv_q(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_urem(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  BzlaBitVector *res;
  uint32_t bw = a->width;

  if (bzla_bv_is_zero(b)) return bzla_bv_copy(mm, a);
  res = bzla_bv_new(mm, bw);
  mpz_fdiv_r(res->val, a->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_sdiv(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BzlaBitVector *res, *div, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = bzla_bv_get_bit(a, bw - 1);
  is_signed_b = bzla_bv_get_bit(b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = bzla_bv_neg(mm, a);
    div   = bzla_bv_udiv(mm, neg_a, b);
    res   = bzla_bv_neg(mm, div);
    bzla_bv_free(mm, neg_a);
    bzla_bv_free(mm, div);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = bzla_bv_neg(mm, b);
    div   = bzla_bv_udiv(mm, a, neg_b);
    res   = bzla_bv_neg(mm, div);
    bzla_bv_free(mm, neg_b);
    bzla_bv_free(mm, div);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = bzla_bv_neg(mm, a);
    neg_b = bzla_bv_neg(mm, b);
    res   = bzla_bv_udiv(mm, neg_a, neg_b);
    bzla_bv_free(mm, neg_a);
    bzla_bv_free(mm, neg_b);
  }
  else
  {
    res = bzla_bv_udiv(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_srem(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  bool is_signed_a, is_signed_b;
  uint32_t bw;
  BzlaBitVector *res, *rem, *neg_a, *neg_b;

  bw          = a->width;
  is_signed_a = bzla_bv_get_bit(a, bw - 1);
  is_signed_b = bzla_bv_get_bit(b, bw - 1);

  if (is_signed_a && !is_signed_b)
  {
    neg_a = bzla_bv_neg(mm, a);
    rem   = bzla_bv_urem(mm, neg_a, b);
    res   = bzla_bv_neg(mm, rem);
    bzla_bv_free(mm, neg_a);
    bzla_bv_free(mm, rem);
  }
  else if (!is_signed_a && is_signed_b)
  {
    neg_b = bzla_bv_neg(mm, b);
    res   = bzla_bv_urem(mm, a, neg_b);
    bzla_bv_free(mm, neg_b);
  }
  else if (is_signed_a && is_signed_b)
  {
    neg_a = bzla_bv_neg(mm, a);
    neg_b = bzla_bv_neg(mm, b);
    rem   = bzla_bv_urem(mm, neg_a, neg_b);
    res   = bzla_bv_neg(mm, rem);
    bzla_bv_free(mm, neg_a);
    bzla_bv_free(mm, neg_b);
    bzla_bv_free(mm, rem);
  }
  else
  {
    res = bzla_bv_urem(mm, a, b);
  }
  return res;
}

BzlaBitVector *
bzla_bv_concat(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);

  BzlaBitVector *res;
  uint32_t bw = a->width + b->width;

  res = bzla_bv_new(mm, bw);
  mpz_mul_2exp(res->val, a->val, b->width);
  mpz_add(res->val, res->val, b->val);
  mpz_fdiv_r_2exp(res->val, res->val, bw);

  return res;
}

BzlaBitVector *
bzla_bv_slice(BzlaMemMgr *mm,
              const BzlaBitVector *bv,
              uint32_t upper,
              uint32_t lower)
{
  assert(mm);
  assert(bv);
  assert(bv->width > upper);
  assert(upper >= lower);

  BzlaBitVector *res;
  uint32_t bw = upper - lower + 1;

  res = bzla_bv_new(mm, bw);
  mpz_fdiv_r_2exp(res->val, bv->val, upper + 1);
  mpz_fdiv_q_2exp(res->val, res->val, lower);

  return res;
}

BzlaBitVector *
bzla_bv_sext(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t len)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return bzla_bv_copy(mm, bv);
  }

  bw = bv->width;

  if (bzla_bv_get_bit(bv, bw - 1))
  {
    size_t i, n;
    res = bzla_bv_copy(mm, bv);
    res->width += len;
    for (i = bw, n = bw + len; i < n; i++) mpz_setbit(res->val, i);
  }
  else
  {
    res = bzla_bv_uext(mm, bv, len);
  }

  return res;
}

BzlaBitVector *
bzla_bv_uext(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t len)
{
  assert(mm);
  assert(bv);

  BzlaBitVector *res;
  uint32_t bw;

  if (len == 0)
  {
    return bzla_bv_copy(mm, bv);
  }

  bw  = bv->width + len;
  res = bzla_bv_new(mm, bw);
  mpz_set(res->val, bv->val);

  return res;
}

BzlaBitVector *
bzla_bv_ite(BzlaMemMgr *mm,
            const BzlaBitVector *c,
            const BzlaBitVector *t,
            const BzlaBitVector *e)
{
  assert(c);
  assert(t);
  assert(e);
  assert(t->width == e->width);

  return bzla_bv_is_one(c) ? bzla_bv_copy(mm, t) : bzla_bv_copy(mm, e);
}

BzlaBitVector *
bzla_bv_flipped_bit(BzlaMemMgr *mm, const BzlaBitVector *bv, uint32_t pos)
{
  assert(bv);
  assert(pos < bv->width);

  BzlaBitVector *res;
  res = bzla_bv_copy(mm, bv);
  bzla_bv_flip_bit(res, pos);
  return res;
}

BzlaBitVector *
bzla_bv_flipped_bit_range(BzlaMemMgr *mm,
                          const BzlaBitVector *bv,
                          uint32_t upper,
                          uint32_t lower)
{
  assert(mm);
  assert(lower <= upper);
  assert(upper < bv->width);

  BzlaBitVector *res;
  uint32_t i;

  res = bzla_bv_copy(mm, bv);
  for (i = lower; i <= upper; i++)
    bzla_bv_set_bit(res, i, bzla_bv_get_bit(res, i) ? 0 : 1);
  return res;
}

/*------------------------------------------------------------------------*/

bool
bzla_bv_is_uaddo(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  bool res    = false;
  uint32_t bw = a->width;

  (void) mm;
  mpz_t add;
  mpz_init(add);
  mpz_add(add, a->val, b->val);
  mpz_fdiv_q_2exp(add, add, bw);
  res = mpz_cmp_ui(add, 0) != 0;
  mpz_clear(add);
  return res;
}

bool
bzla_bv_is_umulo(BzlaMemMgr *mm, const BzlaBitVector *a, const BzlaBitVector *b)
{
  assert(mm);
  assert(a);
  assert(b);
  assert(a->width == b->width);

  bool res    = false;
  uint32_t bw = a->width;

  if (a->width > 1)
  {
    (void) mm;
    mpz_t mul;
    mpz_init(mul);
    mpz_mul(mul, a->val, b->val);
    mpz_fdiv_q_2exp(mul, mul, bw);
    res = mpz_cmp_ui(mul, 0) != 0;
    mpz_clear(mul);
  }
  return res;
}

/*------------------------------------------------------------------------*/

#if 0
BzlaBitVector *
bzla_bv_gcd_ext (Bzla * bzla,
		 const BzlaBitVector * bv1,
		 const BzlaBitVector * bv2,
		 BzlaBitVector ** fx,
		 BzlaBitVector ** fy)
{
  assert (bv1);
  assert (bv2);
  assert (bv1->width == bv2->width);
  assert (bzla_bv_compare (bv1, bv2) <= 0);
  assert (fx);
  assert (fy);

  BzlaBitVector *a, *b, *x, *y, *lx, *ly, *gcd = 0;
  BzlaBitVector *zero, *mul, *neg, *tx, *ty, *r, *q = 0;

  zero = bzla_bv_new (bzla->mm, bv1->width);

  a = bzla_bv_copy (bzla->mm, bv1);
  b = bzla_bv_copy (bzla->mm, bv2);

  x = bzla_bv_copy (bzla->mm, zero);            // 0
  y = bzla_bv_flipped_bit (bzla->mm, zero, 0);  // 1

  lx = bzla_bv_flipped_bit (bzla->mm, zero, 0); // 1
  ly = bzla_bv_copy (bzla->mm, zero);           // 0

  r = bzla_bv_copy (bzla->mm, bv1);

  while (bzla_bv_compare (b, zero) > 0)
    {
      if (gcd) bzla_bv_free (bzla->mm, gcd);
      gcd = bzla_bv_copy (bzla->mm, r);

      bzla_bv_free (bzla->mm, r);
      r = bzla_bv_urem (bzla->mm, a, b);    // r = a % b

      if (q) bzla_bv_free (bzla->mm, q);
      q = bzla_bv_udiv (bzla->mm, a, b);    // q = a / b

      bzla_bv_free (bzla->mm, a);
      a = bzla_bv_copy (bzla->mm, b);       // a = b
      bzla_bv_free (bzla->mm, b);
      b = bzla_bv_copy (bzla->mm, r);       // b = r

      tx = bzla_bv_copy (bzla->mm, x);      // tx = x
      mul = bzla_bv_mul (bzla->mm, x, q);
      neg = bzla_bv_neg (bzla->mm, mul);
      bzla_bv_free (bzla->mm, x);
      x = bzla_bv_add (bzla->mm, lx, neg);  // x = lx - x * q
      bzla_bv_free (bzla->mm, neg);
      bzla_bv_free (bzla->mm, mul);
      bzla_bv_free (bzla->mm, lx);
      lx = tx;                              // lx = tx

      ty = bzla_bv_copy (bzla->mm, y);      // ty = y
      mul = bzla_bv_mul (bzla->mm, y, q);
      neg = bzla_bv_neg (bzla->mm, mul);
      bzla_bv_free (bzla->mm, y);
      y = bzla_bv_add (bzla->mm, ly, neg);  // y = ly - y * q
      bzla_bv_free (bzla->mm, neg);
      bzla_bv_free (bzla->mm, mul);
      bzla_bv_free (bzla->mm, ly);
      ly = ty;                              // ly = ty
    }

  *fx = lx;
  *fy = ly;
  bzla_bv_free (bzla->mm, r);
  bzla_bv_free (bzla->mm, q);
  bzla_bv_free (bzla->mm, a);
  bzla_bv_free (bzla->mm, b);
  bzla_bv_free (bzla->mm, x);
  bzla_bv_free (bzla->mm, y);
  bzla_bv_free (bzla->mm, zero);
  return gcd;
}
#endif

/* Calculate modular inverse for bv by means of the Extended Euclidian
 * Algorithm. Note that c must be odd (the greatest
 * common divisor gcd (c, 2^bw) must be and is in this case always 1).  */
BzlaBitVector *
bzla_bv_mod_inverse(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);
  assert(bzla_bv_get_bit(bv, 0)); /* bv must be odd */

  /* a = 2^bw
   * b = bv
   * lx * a + ly * b = gcd (a, b) = 1
   * -> lx * a = lx * 2^bw = 0 (2^bw_[bw] = 0)
   * -> ly * b = bv^-1 * bv = 1
   * -> ly is modular inverse of bv */

  BzlaBitVector *res;
  uint32_t bw;

  bw = bv->width;

  BZLA_NEW(mm, res);
  res->width = bw;
  if (bw == 1)
  {
    mpz_init_set_ui(res->val, 1);
  }
  else
  {
    mpz_t twobw;
    mpz_init(twobw);
    mpz_init(res->val);
    mpz_setbit(twobw, bw);
    mpz_invert(res->val, bv->val, twobw);
    mpz_fdiv_r_2exp(res->val, res->val, bw);
    mpz_clear(twobw);
  }
#ifndef NDEBUG
  mpz_t ty;
  assert(res->width == bv->width);
  mpz_init(ty);
  mpz_mul(ty, bv->val, res->val);
  mpz_fdiv_r_2exp(ty, ty, bw);
  assert(!mpz_cmp_ui(ty, 1));
  mpz_clear(ty);
#endif

  return res;
}

/*------------------------------------------------------------------------*/

BzlaSpecialConstBitVector
bzla_bv_is_special_const(const BzlaBitVector *bv)
{
  assert(bv);

  if (bzla_bv_is_zero(bv)) return BZLA_SPECIAL_CONST_BV_ZERO;
  if (bzla_bv_is_one(bv))
  {
    return bv->width == 1 ? BZLA_SPECIAL_CONST_BV_ONE_ONES
                          : BZLA_SPECIAL_CONST_BV_ONE;
  }
  if (bzla_bv_is_ones(bv))
  {
    assert(bv->width > 1);
    return BZLA_SPECIAL_CONST_BV_ONES;
  }
  if (bzla_bv_is_min_signed(bv))
  {
    return BZLA_SPECIAL_CONST_BV_MIN_SIGNED;
  }
  if (bzla_bv_is_max_signed(bv))
  {
    return BZLA_SPECIAL_CONST_BV_MAX_SIGNED;
  }
  return BZLA_SPECIAL_CONST_BV_NONE;
}

/*------------------------------------------------------------------------*/

BzlaBitVectorTuple *
bzla_bv_new_tuple(BzlaMemMgr *mm, uint32_t arity)
{
  assert(mm);

  BzlaBitVectorTuple *res = 0;

  BZLA_CNEW(mm, res);
  if (arity) BZLA_CNEWN(mm, res->bv, arity);
  res->arity = arity;
  return res;
}

void
bzla_bv_add_to_tuple(BzlaMemMgr *mm,
                     BzlaBitVectorTuple *t,
                     const BzlaBitVector *bv,
                     uint32_t pos)
{
  assert(mm);
  assert(t);
  assert(bv);
  assert(pos < t->arity);
  assert(!t->bv[pos]);
  t->bv[pos] = bzla_bv_copy(mm, bv);
}

void
bzla_bv_free_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t)
{
  assert(mm);
  assert(t);

  uint32_t i;

  if (t->arity)
  {
    for (i = 0; i < t->arity; i++) bzla_bv_free(mm, t->bv[i]);
    bzla_mem_free(mm, t->bv, sizeof(BzlaBitVectorTuple *) * t->arity);
  }
  bzla_mem_free(mm, t, sizeof(BzlaBitVectorTuple));
}

int32_t
bzla_bv_compare_tuple(const BzlaBitVectorTuple *t0,
                      const BzlaBitVectorTuple *t1)
{
  assert(t0);
  assert(t1);

  uint32_t i;
  if (t0->arity != t1->arity) return -1;

  for (i = 0; i < t0->arity; i++)
  {
    assert(t0->bv[i]);
    assert(t1->bv[i]);
    if (t0->bv[i]->width != t1->bv[i]->width
        || bzla_bv_compare(t0->bv[i], t1->bv[i]) != 0)
      return 1;
  }
  return 0;
}

uint32_t
bzla_bv_hash_tuple(const BzlaBitVectorTuple *t)
{
  assert(t);

  uint32_t hash = 0;
  uint32_t i, j = 0;

  for (i = 0; i < t->arity; i++)
  {
    assert(t->bv[i]);
    hash += bzla_bv_hash(t->bv[i]) * hash_primes[j++];
    if (j == NPRIMES) j = 0;
  }
  return hash;
}

BzlaBitVectorTuple *
bzla_bv_copy_tuple(BzlaMemMgr *mm, BzlaBitVectorTuple *t)
{
  assert(mm);
  assert(t);

  BzlaBitVectorTuple *res = 0;
  uint32_t i;

  res = bzla_bv_new_tuple(mm, t->arity);

  for (i = 0; i < t->arity; i++)
  {
    assert(t->bv[i]);
    res->bv[i] = bzla_bv_copy(mm, t->bv[i]);
  }
  return res;
}

size_t
bzla_bv_size_tuple(BzlaBitVectorTuple *t)
{
  assert(t);

  uint32_t i;
  size_t res = 0;

  res = sizeof(BzlaBitVectorTuple) + t->arity * sizeof(BzlaBitVector *);
  for (i = 0; i < t->arity; i++) res += bzla_bv_size(t->bv[i]);
  return res;
}

/*------------------------------------------------------------------------*/
