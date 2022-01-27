/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */
#include "bzlabvdomain.h"

#include <stdio.h>

static BzlaBvDomain *
new_domain(BzlaMemMgr *mm)
{
  BzlaBvDomain *res;
  BZLA_CNEW(mm, res);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_new_init(BzlaMemMgr *mm, uint32_t width)
{
  assert(mm);
  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_zero(mm, width);
  res->hi           = bzla_bv_ones(mm, width);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_new(BzlaMemMgr *mm,
                  const BzlaBitVector *lo,
                  const BzlaBitVector *hi)
{
  assert(mm);
  assert(lo);
  assert(hi);
  assert(bzla_bv_get_width(lo) == bzla_bv_get_width(hi));

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_copy(mm, lo);
  res->hi           = bzla_bv_copy(mm, hi);
  return res;
}

/* Create 2-valued bit-vector from 3-valued bit-vector 'bv' by initializing
 * 'x' values to 'bit'. */
static BzlaBitVector *
char_to_bv(BzlaMemMgr *mm, const char *c, char bit)
{
  size_t len = strlen(c);
  char buf[len + 1];
  buf[len] = '\0';
  for (size_t i = 0; i < len; i++)
  {
    buf[i] = (c[i] == 'x') ? bit : c[i];
  }
  return bzla_bv_char_to_bv(mm, buf);
}

/* Create hi for domain from 3-valued string representation 'val'. */
static BzlaBitVector *
char_to_hi(BzlaMemMgr *mm, const char *val)
{
  return char_to_bv(mm, val, '1');
}

/* Create lo for domain from 3-valued string representation 'val'. */
static BzlaBitVector *
char_to_lo(BzlaMemMgr *mm, const char *val)
{
  return char_to_bv(mm, val, '0');
}

BzlaBvDomain *
bzla_bvdomain_new_from_char(BzlaMemMgr *mm, const char *val)
{
  BzlaBitVector *lo = char_to_lo(mm, val);
  BzlaBitVector *hi = char_to_hi(mm, val);
  BzlaBvDomain *res = bzla_bvdomain_new(mm, lo, hi);
  bzla_bv_free(mm, lo);
  bzla_bv_free(mm, hi);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_new_fixed(BzlaMemMgr *mm, const BzlaBitVector *bv)
{
  assert(mm);
  assert(bv);

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_copy(mm, bv);
  res->hi           = bzla_bv_copy(mm, bv);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_new_fixed_uint64(BzlaMemMgr *mm, uint64_t val, uint32_t width)
{
  assert(mm);
  assert(width);
  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_uint64_to_bv(mm, val, width);
  res->hi           = bzla_bv_copy(mm, res->lo);
  return res;
}

void
bzla_bvdomain_free(BzlaMemMgr *mm, BzlaBvDomain *d)
{
  assert(mm);
  assert(d);

  if (d->lo)
  {
    bzla_bv_free(mm, d->lo);
  }
  if (d->hi)
  {
    bzla_bv_free(mm, d->hi);
  }
  BZLA_DELETE(mm, d);
}

BzlaBvDomain *
bzla_bvdomain_copy(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  return bzla_bvdomain_new(mm, d->lo, d->hi);
}

bool
bzla_bvdomain_is_equal(const BzlaBvDomain *a, const BzlaBvDomain *b)
{
  return bzla_bv_compare(a->hi, b->hi) == 0
         && bzla_bv_compare(a->lo, b->lo) == 0;
}

BzlaBvDomain *
bzla_bvdomain_slice(BzlaMemMgr *mm,
                    const BzlaBvDomain *d,
                    uint32_t hi,
                    uint32_t lo)
{
  assert(mm);
  assert(d);
  assert(hi >= lo);

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_slice(mm, d->lo, hi, lo);
  res->hi           = bzla_bv_slice(mm, d->hi, hi, lo);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_not(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  assert(mm);
  assert(d);

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_not(mm, d->hi);
  res->hi           = bzla_bv_not(mm, d->lo);
  return res;
}

BzlaBvDomain *
bzla_bvdomain_sll(BzlaMemMgr *mm,
                  const BzlaBvDomain *d,
                  const BzlaBitVector *bv)
{
  assert(mm);
  assert(d);
  assert(bv);

  BzlaBvDomain *res = new_domain(mm);
  res->lo           = bzla_bv_sll(mm, d->hi, bv);
  res->hi           = bzla_bv_sll(mm, d->lo, bv);
  return res;
}

/* -------------------------------------------------------------------------- */

uint32_t
bzla_bvdomain_get_width(const BzlaBvDomain *d)
{
  assert(d);
  assert(bzla_bv_get_width(d->lo) == bzla_bv_get_width(d->hi));
  return bzla_bv_get_width(d->lo);
}

/* -------------------------------------------------------------------------- */

bool
bzla_bvdomain_is_valid(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  BzlaBitVector *not_lo       = bzla_bv_not(mm, d->lo);
  BzlaBitVector *not_lo_or_hi = bzla_bv_or(mm, not_lo, d->hi);
  bool res                    = bzla_bv_is_ones(not_lo_or_hi);
  bzla_bv_free(mm, not_lo);
  bzla_bv_free(mm, not_lo_or_hi);
  return res;
}

bool
bzla_bvdomain_is_fixed(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  BzlaBitVector *equal = bzla_bv_eq(mm, d->lo, d->hi);
  bool res             = bzla_bv_is_true(equal);
  bzla_bv_free(mm, equal);
  return res;
}

bool
bzla_bvdomain_has_fixed_bits(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  BzlaBitVector *xnor  = bzla_bv_xnor(mm, d->lo, d->hi);
  BzlaBitVector *redor = bzla_bv_redor(mm, xnor);
  bool res             = bzla_bv_is_true(redor);
  bzla_bv_free(mm, xnor);
  bzla_bv_free(mm, redor);
  return res;
}

void
bzla_bvdomain_fix_bit(const BzlaBvDomain *d, uint32_t pos, bool value)
{
  assert(d);
  assert(pos < bzla_bvdomain_get_width(d));
  bzla_bv_set_bit(d->lo, pos, value);
  bzla_bv_set_bit(d->hi, pos, value);
}

bool
bzla_bvdomain_is_fixed_bit(const BzlaBvDomain *d, uint32_t pos)
{
  assert(d);
  assert(pos < bzla_bvdomain_get_width(d));
  return bzla_bv_get_bit(d->lo, pos) == bzla_bv_get_bit(d->hi, pos);
}

bool
bzla_bvdomain_is_fixed_bit_true(const BzlaBvDomain *d, uint32_t pos)
{
  assert(d);
  assert(pos < bzla_bvdomain_get_width(d));
  return bzla_bv_get_bit(d->lo, pos)
         && bzla_bv_get_bit(d->lo, pos) == bzla_bv_get_bit(d->hi, pos);
}

bool
bzla_bvdomain_is_fixed_bit_false(const BzlaBvDomain *d, uint32_t pos)
{
  assert(d);
  assert(pos < bzla_bvdomain_get_width(d));
  return !bzla_bv_get_bit(d->lo, pos)
         && bzla_bv_get_bit(d->lo, pos) == bzla_bv_get_bit(d->hi, pos);
}

bool
bzla_bvdomain_check_fixed_bits(BzlaMemMgr *mm,
                               const BzlaBvDomain *d,
                               const BzlaBitVector *bv)
{
  bool res;
  BzlaBitVector *and, * or ;
  and = bzla_bv_and(mm, bv, d->hi);
  or  = bzla_bv_or(mm, and, d->lo);
  res = bzla_bv_compare(or, bv) == 0;
  bzla_bv_free(mm, or);
  bzla_bv_free(mm, and);
  return res;
}

/* -------------------------------------------------------------------------- */

char *
bzla_bvdomain_to_char(BzlaMemMgr *mm, const BzlaBvDomain *d)
{
  char *hi, *res;
  size_t len;

  res = bzla_bv_to_char(mm, d->lo);
  hi  = bzla_bv_to_char(mm, d->hi);
  len = strlen(res);

  for (size_t i = 0; i < len; i++)
  {
    if (res[i] != hi[i])
    {
      if (res[i] == '0' && hi[i] == '1')
      {
        res[i] = 'x';
      }
      else
      {
        assert(res[i] == '1' && hi[i] == '0');
        res[i] = '?';
      }
    }
  }
  bzla_mem_freestr(mm, hi);
  return res;
}

void
bzla_bvdomain_print(BzlaMemMgr *mm, const BzlaBvDomain *d, bool print_short)
{
  if (print_short)
  {
    char *s = bzla_bvdomain_to_char(mm, d);
    printf("%s\n", s);
    bzla_mem_freestr(mm, s);
  }
  else
  {
    char *s = bzla_bv_to_char(mm, d->lo);
    printf("lo: %s, ", s);
    bzla_mem_freestr(mm, s);
    s = bzla_bv_to_char(mm, d->hi);
    printf("hi: %s\n", s);
    bzla_mem_freestr(mm, s);
  }
}

#define PRINT_BUFFER_SIZE 1024

const char *
bzla_bvdomain_to_str(const BzlaBvDomain *d)
{
  static char s_buf[PRINT_BUFFER_SIZE];
  static size_t s_buf_pos = 0;
  size_t width            = bzla_bv_get_width(d->lo);
  bool too_long           = width + 1 >= PRINT_BUFFER_SIZE;
  size_t print_width, buf_start;
  uint32_t bit_lo, bit_hi;
  char c;

  assert(s_buf_pos <= PRINT_BUFFER_SIZE);

  /* if bits don't fit into buffer */
  if (width + 1 >= PRINT_BUFFER_SIZE - s_buf_pos)
  {
    s_buf_pos = 0;
  }

  /* Save 3 characters for ... if bv is too long to fit into buffer. */
  print_width = too_long ? width - 3 : width;
  buf_start   = s_buf_pos;
  for (size_t i = 1; i <= print_width; i++)
  {
    bit_lo = bzla_bv_get_bit(d->lo, width - i);
    bit_hi = bzla_bv_get_bit(d->hi, width - i);
    if (bit_lo != bit_hi)
    {
      if (bit_lo == 0 && bit_hi == 1)
      {
        c = 'x';
      }
      else
      {
        assert(bit_lo == 1);
        assert(bit_hi == 0);
        c = '?';
      }
    }
    else
    {
      c = bit_lo == 0 ? '0' : '1';
    }
    s_buf[s_buf_pos++] = c;
    assert(s_buf_pos < PRINT_BUFFER_SIZE - 1);
  }
  if (too_long)
  {
    assert(s_buf_pos < PRINT_BUFFER_SIZE - 4);
    s_buf[s_buf_pos++] = '.';
    s_buf[s_buf_pos++] = '.';
    s_buf[s_buf_pos++] = '.';
  }
  s_buf[s_buf_pos++] = 0;
  return s_buf + buf_start;
}

/*----------------------------------------------------------------------------*/

static BzlaBitVector *
gen_next_bits(BzlaBvDomainGenerator *gen, bool random)
{
  assert(gen->domain);
  assert(random || gen->bits);

  uint32_t bw, bw_bits, i, j;
  BzlaBitVector *res, *next_bits;

  bw  = bzla_bv_get_width(gen->domain->lo);
  res = bzla_bv_copy(gen->mm, gen->domain->lo);

  /* Random always resets gen->bits to a random value between bits_min and
   * bits_max. */
  if (random)
  {
    assert(gen->rng);
    assert(gen->bits_min);
    assert(gen->bits_max);
    if (gen->bits) bzla_bv_free(gen->mm, gen->bits);
    bw_bits   = bzla_bv_get_width(gen->bits_min);
    gen->bits = bzla_bv_new_random_range(
        gen->mm, gen->rng, bw_bits, gen->bits_min, gen->bits_max);
  }

  for (i = 0, j = 0; i < bw; ++i)
  {
    if (!bzla_bvdomain_is_fixed_bit(gen->domain, i))
    {
      bzla_bv_set_bit(res, i, bzla_bv_get_bit(gen->bits, j++));
    }
  }

  /* If bits is ones, we enumerated all values. */
  if (bzla_bv_compare(gen->bits, gen->bits_max) == 0)
  {
    bzla_bv_free(gen->mm, gen->bits);
    /* random never terminates and bits start again at bits_min. */
    gen->bits = random ? bzla_bv_copy(gen->mm, gen->bits_min) : 0;
  }
  else
  {
    next_bits = bzla_bv_inc(gen->mm, gen->bits);
    bzla_bv_free(gen->mm, gen->bits);
    gen->bits = next_bits;
  }

  assert(!gen->bits || bzla_bv_compare(gen->bits, gen->bits_min) >= 0);
  assert(!gen->bits || bzla_bv_compare(gen->bits, gen->bits_max) <= 0);
  assert(bzla_bv_compare(res, gen->min) >= 0);
  assert(bzla_bv_compare(res, gen->max) <= 0);

  if (gen->cur) bzla_bv_free(gen->mm, gen->cur);
  gen->cur = res;

  return res;
}

void
bzla_bvdomain_gen_init(BzlaMemMgr *mm,
                       BzlaRNG *rng,
                       BzlaBvDomainGenerator *gen,
                       const BzlaBvDomain *d)
{
  assert(mm);
  assert(gen);
  assert(d);
  bzla_bvdomain_gen_init_range(mm, rng, gen, d, 0, 0);
}

void
bzla_bvdomain_gen_init_range(BzlaMemMgr *mm,
                             BzlaRNG *rng,
                             BzlaBvDomainGenerator *gen,
                             const BzlaBvDomain *d,
                             const BzlaBitVector *min,
                             const BzlaBitVector *max)
{
  assert(mm);
  assert(gen);
  assert(d);

  uint32_t i, j, k, idx_i, idx_j, j0, bw, cnt, bit;

  bw = bzla_bv_get_width(d->lo);
  for (i = 0, cnt = 0; i < bw; i++)
  {
    if (!bzla_bvdomain_is_fixed_bit(d, i)) cnt += 1;
  }

  if (!min || bzla_bv_compare(d->lo, min) > 0)
  {
    min = d->lo;
  }

  if (!max || bzla_bv_compare(d->hi, max) < 0)
  {
    max = d->hi;
  }

  gen->bits     = 0;
  gen->bits_min = 0;
  gen->bits_max = 0;

  if (cnt && bzla_bv_compare(min, d->hi) <= 0
      && bzla_bv_compare(max, d->lo) >= 0)
  {
    assert(bzla_bv_compare(min, d->lo) >= 0);
    assert(bzla_bv_compare(max, d->hi) <= 0);

    /* set unconstrained bits to the minimum value that corresponds to a
     * generated value >= min */
    gen->bits_min = bzla_bv_new(mm, cnt);
    for (i = 0, j = 0, j0 = 0; i < bw; i++)
    {
      idx_i = bw - 1 - i;
      bit   = bzla_bv_get_bit(min, idx_i);
      if (!bzla_bvdomain_is_fixed_bit(d, idx_i))
      {
        assert(j < cnt);
        idx_j = cnt - 1 - j;
        bzla_bv_set_bit(gen->bits_min, idx_j, bit);
        if (!bit) j0 = j;
        j += 1;
      }
      else if (bzla_bvdomain_is_fixed_bit_true(d, idx_i) && !bit)
      {
        break;
      }
      else if (bzla_bvdomain_is_fixed_bit_false(d, idx_i) && bit)
      {
        assert(j > 0);
        assert(bzla_bv_get_bit(gen->bits_min, cnt - j0 - 1) == 0);
        bzla_bv_set_bit(gen->bits_min, cnt - 1 - j0, 1);
        for (k = j0 + 1; k < cnt; k++)
        {
          bzla_bv_set_bit(gen->bits_min, cnt - 1 - k, 0);
        }
        break;
      }
    }

    /* set unconstrained bits to the maxium value that corresponds to a
     * generated value <= max */
    gen->bits_max = bzla_bv_ones(mm, cnt);
    for (i = 0, j = 0, j0 = 0; i < bw; i++)
    {
      idx_i = bw - 1 - i;
      bit   = bzla_bv_get_bit(max, idx_i);
      if (!bzla_bvdomain_is_fixed_bit(d, idx_i))
      {
        assert(j < cnt);
        idx_j = cnt - 1 - j;
        bzla_bv_set_bit(gen->bits_max, idx_j, bit);
        if (bit) j0 = j;
        j += 1;
      }
      else if (bzla_bvdomain_is_fixed_bit_true(d, idx_i) && !bit)
      {
        assert(j > 0);
        assert(bzla_bv_get_bit(gen->bits_max, cnt - j0 - 1) == 1);
        bzla_bv_set_bit(gen->bits_max, cnt - 1 - j0, 0);
        for (k = j0 + 1; k < cnt; k++)
        {
          bzla_bv_set_bit(gen->bits_max, cnt - 1 - k, 1);
        }
        break;
      }
      else if (bzla_bvdomain_is_fixed_bit_false(d, idx_i) && bit)
      {
        break;
      }
    }

    /* If bits_min > bits_max, we can't generate any value. */
    if (bzla_bv_compare(gen->bits_min, gen->bits_max) <= 0)
    {
      gen->bits = bzla_bv_copy(mm, gen->bits_min);
    }
  }

  gen->mm        = mm;
  gen->domain    = bzla_bvdomain_copy(mm, d);
  gen->cur       = 0;
  gen->rng       = rng;
#ifndef NDEBUG
  gen->min = bzla_bv_copy(mm, min);
  gen->max = bzla_bv_copy(mm, max);
#endif
}

bool
bzla_bvdomain_gen_has_next(const BzlaBvDomainGenerator *gen)
{
  assert(gen);
  assert(!gen->bits || bzla_bv_compare(gen->bits, gen->bits_min) >= 0);
  return gen->bits && bzla_bv_compare(gen->bits, gen->bits_max) <= 0;
}

BzlaBitVector *
bzla_bvdomain_gen_next(BzlaBvDomainGenerator *gen)
{
  assert(gen);
  assert(gen->bits);
  assert(bzla_bvdomain_gen_has_next(gen));
  return gen_next_bits(gen, false);
}

BzlaBitVector *
bzla_bvdomain_gen_random(BzlaBvDomainGenerator *gen)
{
  assert(gen);
  assert(gen->rng);
  assert(bzla_bvdomain_gen_has_next(gen));
  return gen_next_bits(gen, true);
}

void
bzla_bvdomain_gen_delete(const BzlaBvDomainGenerator *gen)
{
  assert(gen);
  if (gen->bits) bzla_bv_free(gen->mm, gen->bits);
  if (gen->bits_min) bzla_bv_free(gen->mm, gen->bits_min);
  if (gen->bits_max) bzla_bv_free(gen->mm, gen->bits_max);
  bzla_bvdomain_free(gen->mm, gen->domain);
  if (gen->cur) bzla_bv_free(gen->mm, gen->cur);
#ifndef NDEBUG
  if (gen->min) bzla_bv_free(gen->mm, gen->min);
  if (gen->max) bzla_bv_free(gen->mm, gen->max);
#endif
}

/*----------------------------------------------------------------------------*/

void
bzla_bvdomain_gen_signed_init(BzlaMemMgr *mm,
                              BzlaRNG *rng,
                              BzlaBvDomainSignedGenerator *gen,
                              const BzlaBvDomain *d)
{
  assert(mm);
  assert(gen);
  assert(d);
  bzla_bvdomain_gen_signed_init_range(mm, rng, gen, d, 0, 0);
}

void
bzla_bvdomain_gen_signed_init_range(BzlaMemMgr *mm,
                                    BzlaRNG *rng,
                                    BzlaBvDomainSignedGenerator *gen,
                                    const BzlaBvDomain *d,
                                    const BzlaBitVector *min,
                                    const BzlaBitVector *max)
{
  assert(mm);
  assert(gen);
  assert(d);

  uint32_t bw;
  int32_t cmp_min, cmp_max;
  BzlaBitVector *zero, *ones, *bvmin, *bvmax;

  bw = bzla_bvdomain_get_width(d);

  bvmin = !min ? bzla_bv_min_signed(mm, bw) : bzla_bv_copy(mm, min);
  bvmax = !max ? bzla_bv_max_signed(mm, bw) : bzla_bv_copy(mm, max);
  assert(bzla_bv_get_width(bvmin) == bw);
  assert(bzla_bv_get_width(bvmax) == bw);

  zero    = bzla_bv_zero(mm, bw);
  ones    = bzla_bv_ones(mm, bw);
  cmp_min = bzla_bv_signed_compare(bvmin, zero);
  cmp_max = bzla_bv_signed_compare(bvmax, zero);

  gen->mm      = mm;
  gen->domain  = bzla_bvdomain_copy(mm, d);
  gen->rng     = rng;
  gen->gen_cur = 0;
  gen->gen_lo  = 0;
  gen->gen_hi  = 0;

  if (cmp_min < 0)
  {
    BZLA_CNEW(mm, gen->gen_lo);
    bzla_bvdomain_gen_init_range(
        mm, rng, gen->gen_lo, d, bvmin, cmp_max < 0 ? bvmax : ones);
    gen->gen_cur = gen->gen_lo;
  }
  if (cmp_max >= 0)
  {
    BZLA_CNEW(mm, gen->gen_hi);
    bzla_bvdomain_gen_init_range(
        mm, rng, gen->gen_hi, d, cmp_min >= 0 ? bvmin : zero, bvmax);
    if (!gen->gen_cur) gen->gen_cur = gen->gen_hi;
  }
  bzla_bv_free(mm, zero);
  bzla_bv_free(mm, ones);
  bzla_bv_free(mm, bvmin);
  bzla_bv_free(mm, bvmax);
}

bool
bzla_bvdomain_gen_signed_has_next(BzlaBvDomainSignedGenerator *gen)
{
  assert(gen);

  if (!gen->gen_cur) return false;
  if (!bzla_bvdomain_gen_has_next(gen->gen_cur))
  {
    if (gen->gen_cur == gen->gen_lo && gen->gen_hi)
    {
      gen->gen_cur = gen->gen_hi;
      return bzla_bvdomain_gen_has_next(gen->gen_cur);
    }
    return false;
  }
  return true;
}

BzlaBitVector *
bzla_bvdomain_gen_signed_next(BzlaBvDomainSignedGenerator *gen)
{
  assert(gen);
  assert(bzla_bvdomain_gen_signed_has_next(gen));
  return bzla_bvdomain_gen_next(gen->gen_cur);
}

BzlaBitVector *
bzla_bvdomain_gen_signed_random(BzlaBvDomainSignedGenerator *gen)
{
  assert(gen);
  assert(gen->rng);
  assert(gen->gen_lo || gen->gen_hi);
  bool has_next_lo = false, has_next_hi = false;

  if (gen->gen_lo) has_next_lo = bzla_bvdomain_gen_has_next(gen->gen_lo);
  if (gen->gen_hi) has_next_hi = bzla_bvdomain_gen_has_next(gen->gen_hi);
  if (has_next_lo && has_next_hi)
  {
    return bzla_bvdomain_gen_random(bzla_rng_flip_coin(gen->rng) ? gen->gen_lo
                                                                 : gen->gen_hi);
  }
  if (has_next_lo)
  {
    return bzla_bvdomain_gen_random(gen->gen_lo);
  }
  assert(has_next_hi);
  return bzla_bvdomain_gen_random(gen->gen_hi);
}

void
bzla_bvdomain_gen_signed_delete(const BzlaBvDomainSignedGenerator *gen)
{
  assert(gen);
  if (gen->gen_lo)
  {
    bzla_bvdomain_gen_delete(gen->gen_lo);
    BZLA_DELETE(gen->mm, gen->gen_lo);
  }
  if (gen->gen_hi)
  {
    bzla_bvdomain_gen_delete(gen->gen_hi);
    BZLA_DELETE(gen->mm, gen->gen_hi);
  }
  bzla_bvdomain_free(gen->mm, gen->domain);
}

/*----------------------------------------------------------------------------*/
struct WheelFactorizer
{
  bool done;
  BzlaMemMgr *mm;
  BzlaBitVector *num;
  BzlaBitVector *fact;

  BzlaBitVector *one;
  BzlaBitVector *two;
  BzlaBitVector *four;
  BzlaBitVector *six;

  size_t pos;
  BzlaBitVector *inc[11];

  uint64_t limit;
};

typedef struct WheelFactorizer WheelFactorizer;

/* Wheel factorization for s % x = t with base {2, 3, 5}. */
static void
wfact_init(WheelFactorizer *wf,
           BzlaMemMgr *mm,
           const BzlaBitVector *n,
           uint64_t limit)
{
  uint32_t bw;

  bw = bzla_bv_get_width(n);

  memset(wf, 0, sizeof(WheelFactorizer));

  wf->mm = mm;

  wf->done  = false;
  wf->limit = limit;
  wf->one   = bzla_bv_one(mm, bw);
  wf->two   = bzla_bv_uint64_to_bv(mm, 2, bw);
  wf->four  = bzla_bv_uint64_to_bv(mm, 4, bw);
  wf->six   = bzla_bv_uint64_to_bv(mm, 6, bw);

  wf->fact    = bzla_bv_copy(mm, wf->two);
  wf->num     = bzla_bv_copy(mm, n);
  wf->pos     = 0;
  wf->inc[0]  = wf->one;
  wf->inc[1]  = wf->two;
  wf->inc[2]  = wf->two;
  wf->inc[3]  = wf->four;
  wf->inc[4]  = wf->two;
  wf->inc[5]  = wf->four;
  wf->inc[6]  = wf->two;
  wf->inc[7]  = wf->four;
  wf->inc[8]  = wf->six;
  wf->inc[9]  = wf->two;
  wf->inc[10] = wf->six;
}

static const BzlaBitVector *
wfact_next(WheelFactorizer *wf)
{
  BzlaMemMgr *mm;
  bool done, found_factor;
  uint64_t limit, num_iterations;
  BzlaBitVector *res, *fact_squared, *quot, *rem, *tmp;

  if (wf->done)
  {
    return 0;
  }

  mm = wf->mm;

  limit          = wf->limit;
  num_iterations = 0;
  res            = 0;
  while (true)
  {
    ++num_iterations;
    if (limit && num_iterations > limit)
    {
      res      = 0;
      wf->done = true;
      break;
    }

    /* sqrt(n) is the maximum factor. */
    if (bzla_bv_is_umulo(mm, wf->fact, wf->fact))
    {
      done = true;
    }
    else
    {
      fact_squared = bzla_bv_mul(mm, wf->fact, wf->fact);
      done         = bzla_bv_compare(fact_squared, wf->num) > 0;
      bzla_bv_free(mm, fact_squared);
    }

    if (done)
    {
      res      = wf->num;
      wf->done = true;
      break;
    }

    bzla_bv_udiv_urem(mm, wf->num, wf->fact, &quot, &rem);
    found_factor = bzla_bv_is_zero(rem);
    bzla_bv_free(mm, rem);

    if (found_factor)
    {
      bzla_bv_free(mm, wf->num);
      wf->num = quot;
      res     = wf->fact;
      break;
    }
    else
    {
      bzla_bv_free(mm, quot);
      tmp  = bzla_bv_add(mm, wf->fact, wf->inc[wf->pos]);
      done = bzla_bv_compare(tmp, wf->fact) <= 0;
      bzla_bv_free(mm, wf->fact);

      wf->fact = tmp;
      wf->pos  = (wf->pos == 10) ? 3 : wf->pos + 1;
      if (done)
      {
        wf->done = true;
        break;
      }
    }
  }

  return res;
}

static void
wfact_delete(WheelFactorizer *wf)
{
  bzla_bv_free(wf->mm, wf->one);
  bzla_bv_free(wf->mm, wf->two);
  bzla_bv_free(wf->mm, wf->four);
  bzla_bv_free(wf->mm, wf->six);
  bzla_bv_free(wf->mm, wf->fact);
  bzla_bv_free(wf->mm, wf->num);
}

BzlaBitVector *
bzla_bvdomain_get_factor(BzlaMemMgr *mm,
                         const BzlaBitVector *num,
                         const BzlaBvDomain *x,
                         const BzlaBitVector *excl_min_val,
                         uint64_t limit,
                         BzlaRNG *rng)
{
  WheelFactorizer wf;
  BzlaBitVector *res, *mul, *tmp, *f;
  const BzlaBitVector *fact;
  BzlaBitVectorPtrStack factors;
  uint32_t i, j, n, cnt;

  wfact_init(&wf, mm, num, limit);

  BZLA_INIT_STACK(mm, factors);
  while (true)
  {
    fact = wfact_next(&wf);

    if (!fact) break;

    BZLA_PUSH_STACK(factors, bzla_bv_copy(mm, fact));
    if (!rng)
    {
      break;
    }
  }

  /* Pick factor from stack. Random (combination) if 'rng' is given. */
  res = 0;
  if (!BZLA_EMPTY_STACK(factors))
  {
    if (rng)
    {
      /* to determine all possible combinations can be very expensive, we'll
       * try for a limited number of times, and if none matches, we return 0 */
      for (cnt = 0; cnt < 1000; cnt++)
      {
        /* number of factors to combine */
        n = bzla_rng_pick_rand(rng, 1, BZLA_COUNT_STACK(factors));
        /* move selected factors to front of the stack and combine
         * this ensures that we don't pick a factor twice, e.g., 2 2 3 can be
         * combined into { 2, 3, 2*2, 2*3, 2*2*3 } */
        for (i = 0, mul = 0; i < n; i++)
        {
          j = bzla_rng_pick_rand(rng, i, BZLA_COUNT_STACK(factors) - 1);
          f = BZLA_PEEK_STACK(factors, j);
          BZLA_POKE_STACK(factors, j, BZLA_PEEK_STACK(factors, i));
          BZLA_POKE_STACK(factors, i, f);
          if (mul)
          {
            tmp = bzla_bv_mul(mm, f, mul);
            if (bzla_bv_compare(tmp, num) > 0)
            {
              bzla_bv_free(mm, tmp);
              continue;
            }
            bzla_bv_free(mm, mul);
            mul = tmp;
          }
          else
          {
            mul = bzla_bv_copy(mm, f);
          }
        }
        if (bzla_bv_compare(mul, excl_min_val) > 0
            && bzla_bvdomain_check_fixed_bits(mm, x, mul))
        {
          res = mul;
          break;
        }
        bzla_bv_free(mm, mul);
      }
    }
    else
    {
      res = BZLA_PEEK_STACK(factors, 0);
    }

    /* Release all except for result. */
    for (i = 0; i < BZLA_COUNT_STACK(factors); ++i)
    {
      bzla_bv_free(mm, BZLA_PEEK_STACK(factors, i));
    }
  }

  BZLA_RELEASE_STACK(factors);
  wfact_delete(&wf);
  return res;
}
