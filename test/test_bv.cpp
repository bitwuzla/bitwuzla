/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <math.h>

#include <bitset>

#include "test.h"

extern "C" {
#include "bzlabv.h"
}

// TODO: remove after non-gmp BV implementation is deleted
#define BZLA_BV_TYPE uint32_t
#define TEST_BV_TYPE_BW (sizeof(BZLA_BV_TYPE) * 8)

#define TEST_BV_IS_UADDO_BITVEC(bw, v0, v1, res)      \
  do                                                  \
  {                                                   \
    bv0 = bzla_bv_uint64_to_bv(d_mm, v0, bw);         \
    bv1 = bzla_bv_uint64_to_bv(d_mm, v1, bw);         \
    ASSERT_EQ(bzla_bv_is_uaddo(d_mm, bv0, bv1), res); \
    bzla_bv_free(d_mm, bv0);                          \
    bzla_bv_free(d_mm, bv1);                          \
  } while (0)

#define TEST_BV_IS_UMULO_BITVEC(bw, v0, v1, res)      \
  do                                                  \
  {                                                   \
    bv0 = bzla_bv_uint64_to_bv(d_mm, v0, bw);         \
    bv1 = bzla_bv_uint64_to_bv(d_mm, v1, bw);         \
    ASSERT_EQ(bzla_bv_is_umulo(d_mm, bv0, bv1), res); \
    bzla_bv_free(d_mm, bv0);                          \
    bzla_bv_free(d_mm, bv1);                          \
  } while (0)

#define TEST_BV_CHECK_CHAR_TO_BV(bv, i)          \
  do                                             \
  {                                              \
    s = bzla_bv_to_char(d_mm, bv);               \
    ASSERT_EQ(strlen(s), bzla_bv_get_width(bv)); \
    for (k = 0; k < i; k++)                      \
    {                                            \
      b = s[i - k - 1] == '0' ? 0 : 1;           \
      ASSERT_EQ(b, bzla_bv_get_bit(bv, k));      \
    }                                            \
    bzla_mem_freestr(d_mm, s);                   \
    bzla_bv_free(d_mm, bv);                      \
  } while (0)

class TestBv : public TestBzla
{
 protected:
  static constexpr uint32_t TEST_BW                   = 32;
  static constexpr uint32_t TEST_BITVEC_NUM_BITS      = 65;
  static constexpr uint32_t TEST_BITVEC_MOD_INV_TESTS = 1000;
  static constexpr uint32_t TEST_BITVEC_TESTS         = 100000;
  static constexpr uint32_t TEST_BITVEC_PERF_TESTS    = 1000000;

  void SetUp() override
  {
    TestBzla::SetUp();
    d_mm  = d_bzla->mm;
    d_rng = d_bzla->rng;
  }

  void bv_to_hex_char_bitvec(FILE *g_logfile, const char *c)
  {
    BzlaBitVector *bv = bzla_bv_char_to_bv(d_mm, c);
    char *h           = bzla_bv_to_hex_char(d_mm, bv);
    fprintf(g_logfile, "2'%s = 16'%s\n", c, h);
    bzla_mem_freestr(d_mm, h);
    bzla_bv_free(d_mm, bv);
  }

  void bv_to_dec_char_bitvec(FILE *g_logfile, const char *c)
  {
    BzlaBitVector *bv = bzla_bv_char_to_bv(d_mm, c);
    char *d           = bzla_bv_to_dec_char(d_mm, bv);
    fprintf(g_logfile, "2'%s = 10'%s\n", c, d);
    bzla_mem_freestr(d_mm, d);
    bzla_bv_free(d_mm, bv);
  }

  static uint64_t _not(uint64_t x, uint32_t bw)
  {
    return ~x % (uint64_t) pow(2, bw);
  }

  static uint64_t neg(uint64_t x, uint32_t bw)
  {
    return -x % (uint64_t) pow(2, bw);
  }

  static uint64_t redand(uint64_t x, uint32_t bw)
  {
    uint64_t a = UINT64_MAX << bw;
    return (x + a) == UINT64_MAX;
  }

  static uint64_t redor(uint64_t x, uint32_t bw)
  {
    (void) bw;
    return x != 0;
  }

  static uint64_t inc(uint64_t x, uint32_t bw)
  {
    return (x + 1) % (uint64_t) pow(2, bw);
  }

  static uint64_t dec(uint64_t x, uint32_t bw)
  {
    return (x - 1) % (uint64_t) pow(2, bw);
  }

  static uint64_t add(uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x + y) % (uint64_t) pow(2, bw);
  }

  static uint64_t sub(uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x - y) % (uint64_t) pow(2, bw);
  }

  static uint64_t _and(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x & y;
  }

  static uint64_t nand(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    uint32_t shift = 64 - bw;
    return (((~(x & y)) << shift) >> shift);
  }

  static uint64_t _or(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x | y;
  }

  static uint64_t nor(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    uint32_t shift = 64 - bw;
    return ((~(x | y)) << shift) >> shift;
  }

  static uint64_t xnor(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    uint32_t shift = 64 - bw;
    return ((~(x ^ y)) << shift) >> shift;
  }

  static uint64_t implies(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw == 1);
    (void) bw;
    return ((~x | y) << 63) >> 63;
  }

  static uint64_t _xor(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x ^ y;
  }

  static uint64_t eq(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x == y;
  }

  static uint64_t ne(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x != y;
  }

  static uint64_t ult(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x < y;
  }

  static uint64_t ulte(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x <= y;
  }

  static uint64_t ugt(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x > y;
  }

  static uint64_t ugte(uint64_t x, uint64_t y, uint32_t bw)
  {
    (void) bw;
    return x >= y;
  }

  static int64_t slt(int64_t x, int64_t y, uint32_t bw)
  {
    (void) bw;
    return x < y;
  }

  static int64_t slte(int64_t x, int64_t y, uint32_t bw)
  {
    (void) bw;
    return x <= y;
  }

  static int64_t sgt(int64_t x, int64_t y, uint32_t bw)
  {
    (void) bw;
    return x > y;
  }

  static int64_t sgte(int64_t x, int64_t y, uint32_t bw)
  {
    (void) bw;
    return x >= y;
  }

  static uint64_t sll(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    if (y >= bw) return 0;
    return (x << y) % (uint64_t) pow(2, bw);
  }

  static uint64_t srl(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    if (y >= bw) return 0;
    return (x >> y) % (uint64_t) pow(2, bw);
  }

  static uint64_t sra(uint64_t x, uint64_t y, uint32_t bw)
  {
    assert(bw <= 64);
    uint64_t max = pow(2, bw);
    if ((x >> (bw - 1)) & 1)
    {
      if (y > bw) return ~0 % max;
      return ~((~x % max) >> y) % max;
    }
    if (y > bw) return 0;
    return (x >> y) % max;
  }

  static uint64_t mul(uint64_t x, uint64_t y, uint32_t bw)
  {
    return (x * y) % (uint64_t) pow(2, bw);
  }

  static uint64_t udiv(uint64_t x, uint64_t y, uint32_t bw)
  {
    if (y == 0) return UINT64_MAX % (uint64_t) pow(2, bw);
    return (x / y) % (uint64_t) pow(2, bw);
  }

  static uint64_t urem(uint64_t x, uint64_t y, uint32_t bw)
  {
    if (y == 0) return x;
    return (x % y) % (uint64_t) pow(2, bw);
  }

  static int64_t sdiv(int64_t x, int64_t y, uint32_t bw)
  {
    if (y == 0)
    {
      return x < 0 ? 1 : UINT64_MAX % (uint64_t) pow(2, bw);
    }
    return (x / y) % (uint64_t) pow(2, bw);
  }

  static int64_t srem(int64_t x, int64_t y, uint32_t bw)
  {
    if (y == 0) return x % (uint64_t) pow(2, bw);
    return (x % y) % (uint64_t) pow(2, bw);
  }

  static uint64_t ite(uint64_t c, uint64_t t, uint64_t e, uint32_t bw)
  {
    (void) bw;
    return c ? t : e;
  }

  void unary_bitvec(uint64_t (*int_func)(uint64_t, uint32_t),
                    BzlaBitVector *(*bitvec_func)(BzlaMemMgr *,
                                                  const BzlaBitVector *),
                    uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bv, *res;
    uint64_t a, ares, bres;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bv   = bzla_bv_new_random(d_mm, d_rng, bit_width);
      res  = bitvec_func(d_mm, bv);
      a    = bzla_bv_to_uint64(bv);
      ares = int_func(a, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv);
    }
  }

  void binary_bitvec(uint64_t (*int_func)(uint64_t, uint64_t, uint32_t),
                     BzlaBitVector *(*bitvec_func)(BzlaMemMgr *,
                                                   const BzlaBitVector *,
                                                   const BzlaBitVector *),
                     uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bv1, *bv2, *zero, *res;
    uint64_t a1, a2, ares, bres;

    zero = bzla_bv_new(d_mm, bit_width);
    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bv1 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      bv2 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      a1  = bzla_bv_to_uint64(bv1);
      a2  = bzla_bv_to_uint64(bv2);
      /* test for x = 0 explicitly */
      res  = bitvec_func(d_mm, zero, bv2);
      ares = int_func(0, a2, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      /* test for y = 0 explicitly */
      res  = bitvec_func(d_mm, bv1, zero);
      ares = int_func(a1, 0, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      /* test x, y random */
      res  = bitvec_func(d_mm, bv1, bv2);
      ares = int_func(a1, a2, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv1);
      bzla_bv_free(d_mm, bv2);
    }
    bzla_bv_free(d_mm, zero);
  }

  void binary_signed_bitvec(
      int64_t (*int_func)(int64_t, int64_t, uint32_t),
      BzlaBitVector *(*bitvec_func)(BzlaMemMgr *,
                                    const BzlaBitVector *,
                                    const BzlaBitVector *),
      uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bv1, *bv2, *zero, *res;
    int64_t a1, a2, ares, bres;

    zero = bzla_bv_new(d_mm, bit_width);
    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bv1 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      bv2 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      a1  = bzla_bv_to_uint64(bv1);
      a2  = bzla_bv_to_uint64(bv2);
      if (bit_width < 64 && bzla_bv_get_bit(bv1, bit_width - 1))
      {
        a1 = (UINT64_MAX << bit_width) | a1;
      }
      if (bit_width < 64 && bzla_bv_get_bit(bv2, bit_width - 1))
      {
        a2 = (UINT64_MAX << bit_width) | a2;
      }
      /* test for x = 0 explicitly */
      res  = bitvec_func(d_mm, zero, bv2);
      ares = int_func(0, a2, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      /* test for y = 0 explicitly */
      res  = bitvec_func(d_mm, bv1, zero);
      ares = int_func(a1, 0, bit_width);
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      /* test x, y random */
      res  = bitvec_func(d_mm, bv1, bv2);
      ares = int_func(a1, a2, bit_width);
      bres = bzla_bv_to_uint64(res);
      assert(ares == bres);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv1);
      bzla_bv_free(d_mm, bv2);
    }
    bzla_bv_free(d_mm, zero);
  }

  void udiv_urem_bitvec(uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bv1, *bv2, *zero, *q, *r;
    uint64_t a1, a2, ares_div, ares_rem, bres_div, bres_rem;

    zero = bzla_bv_new(d_mm, bit_width);
    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bv1 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      bv2 = bzla_bv_new_random(d_mm, d_rng, bit_width);
      a1  = bzla_bv_to_uint64(bv1);
      a2  = bzla_bv_to_uint64(bv2);
      /* test for x = 0 explicitly */
      bzla_bv_udiv_urem(d_mm, zero, bv2, &q, &r);
      ares_div = udiv(0, a2, bit_width);
      ares_rem = urem(0, a2, bit_width);
      bres_div = bzla_bv_to_uint64(q);
      bres_rem = bzla_bv_to_uint64(r);
      ASSERT_EQ(ares_div, bres_div);
      ASSERT_EQ(ares_rem, bres_rem);
      bzla_bv_free(d_mm, q);
      bzla_bv_free(d_mm, r);
      /* test for y = 0 explicitly */
      bzla_bv_udiv_urem(d_mm, bv1, zero, &q, &r);
      ares_div = udiv(a1, 0, bit_width);
      ares_rem = urem(a1, 0, bit_width);
      bres_div = bzla_bv_to_uint64(q);
      bres_rem = bzla_bv_to_uint64(r);
      ASSERT_EQ(ares_div, bres_div);
      ASSERT_EQ(ares_rem, bres_rem);
      bzla_bv_free(d_mm, q);
      bzla_bv_free(d_mm, r);
      /* test x, y random */
      bzla_bv_udiv_urem(d_mm, bv1, bv2, &q, &r);
      ares_div = udiv(a1, a2, bit_width);
      ares_rem = urem(a1, a2, bit_width);
      bres_div = bzla_bv_to_uint64(q);
      bres_rem = bzla_bv_to_uint64(r);
      ASSERT_EQ(ares_div, bres_div);
      ASSERT_EQ(ares_rem, bres_rem);
      bzla_bv_free(d_mm, q);
      bzla_bv_free(d_mm, r);
      bzla_bv_free(d_mm, bv1);
      bzla_bv_free(d_mm, bv2);
    }
    bzla_bv_free(d_mm, zero);
  }

  void shift_bitvec(const char *toshift,
                    const char *shift,
                    const char *expected,
                    BzlaBitVector *(*shift_fun)(BzlaMemMgr *,
                                                const BzlaBitVector *,
                                                const BzlaBitVector *) )
  {
    assert(strlen(toshift) == strlen(shift));
    assert(strlen(toshift) == strlen(expected));

    BzlaBitVector *bv, *bv_shift, *bv_res, *bv_expected;

    bv          = bzla_bv_char_to_bv(d_mm, toshift);
    bv_shift    = bzla_bv_char_to_bv(d_mm, shift);
    bv_res      = shift_fun(d_mm, bv, bv_shift);
    bv_expected = bzla_bv_char_to_bv(d_mm, expected);
    ASSERT_EQ(bzla_bv_compare(bv_res, bv_expected), 0);
    bzla_bv_free(d_mm, bv_expected);
    bzla_bv_free(d_mm, bv_res);
    bzla_bv_free(d_mm, bv_shift);
    bzla_bv_free(d_mm, bv);
  }

  void concat_bitvec(uint32_t bit_width)
  {
    uint32_t i, bw1, bw2;
    BzlaBitVector *bv1, *bv2, *res;
    uint64_t a1, a2, ares, bres;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bw1 = bzla_rng_pick_rand(d_rng, 1, bit_width - 1);
      bw2 = bit_width - bw1;
      bv1 = bzla_bv_new_random(d_mm, d_rng, bw1);
      bv2 = bzla_bv_new_random(d_mm, d_rng, bw2);
      res = bzla_bv_concat(d_mm, bv1, bv2);
      ASSERT_EQ(bzla_bv_get_width(res), bw1 + bw2);
      a1   = bzla_bv_to_uint64(bv1);
      a2   = bzla_bv_to_uint64(bv2);
      ares = (a1 << bw2) | a2;
      bres = bzla_bv_to_uint64(res);
      ASSERT_EQ(ares, bres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv1);
      bzla_bv_free(d_mm, bv2);
    }
  }

  void slice_bitvec(uint32_t bit_width)
  {
    uint32_t i, upper, lower;
    char *sbv, *sres;
    BzlaBitVector *bv, *res;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bv    = bzla_bv_new_random(d_mm, d_rng, bit_width);
      lower = rand() % bit_width;
      upper = rand() % (bit_width - lower) + lower;
      ASSERT_GE(upper, lower);
      ASSERT_LT(upper, bit_width);
      ASSERT_LT(lower, bit_width);

      res = bzla_bv_slice(d_mm, bv, upper, lower);
      ASSERT_EQ(bzla_bv_get_width(res), upper - lower + 1);
      sres = bzla_bv_to_char(d_mm, res);
      sbv  = bzla_bv_to_char(d_mm, bv);

      ASSERT_EQ(strncmp(sbv + bit_width - upper - 1, sres, upper - lower + 1),
                0);

      bzla_mem_freestr(d_mm, sbv);
      bzla_mem_freestr(d_mm, sres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv);
    }
  }

  void ext_bitvec(BzlaBitVector *(*ext_func)(BzlaMemMgr *,
                                             const BzlaBitVector *,
                                             uint32_t),
                  uint32_t bit_width)
  {
    uint32_t i, j, len;
    char *sbv, *sres;
    BzlaBitVector *bv, *res;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      len = bzla_rng_pick_rand(d_rng, 0, bit_width - 1);
      bv  = bzla_bv_new_random(d_mm, d_rng, bit_width - len);

      res = ext_func(d_mm, bv, len);
      ASSERT_EQ(bzla_bv_get_width(bv) + len, bzla_bv_get_width(res));
      sres = bzla_bv_to_char(d_mm, res);
      sbv  = bzla_bv_to_char(d_mm, bv);

      ASSERT_EQ(strncmp(sbv, sres + len, bit_width - len), 0);

      for (j = 0; j < len; j++)
        ASSERT_EQ(sres[j], (ext_func == bzla_bv_uext ? '0' : sbv[0]));

      bzla_mem_freestr(d_mm, sbv);
      bzla_mem_freestr(d_mm, sres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv);
    }
  }

  void ite_bitvec(uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bvc, *bvt, *bve, *res;
    uint64_t ac, at, ae, ares, bres;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      bvc  = bzla_bv_new_random(d_mm, d_rng, 1);
      bvt  = bzla_bv_new_random(d_mm, d_rng, bit_width);
      bve  = bzla_bv_new_random(d_mm, d_rng, bit_width);
      res  = bzla_bv_ite(d_mm, bvc, bvt, bve);
      ac   = bzla_bv_to_uint64(bvc);
      at   = bzla_bv_to_uint64(bvt);
      ae   = bzla_bv_to_uint64(bve);
      ares = ite(ac, at, ae, bit_width);
      bres = bzla_bv_to_uint64(res);
      (void) ares;
      (void) bres;
      assert(ares == bres);
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bvc);
      bzla_bv_free(d_mm, bvt);
      bzla_bv_free(d_mm, bve);
    }
  }

  void mod_inverse_bitvec(uint32_t bit_width)
  {
    uint32_t i;
    BzlaBitVector *bv, *bvinv, *mul;

    for (i = 0; i < TEST_BITVEC_MOD_INV_TESTS; i++)
    {
      bv = bzla_bv_new_random(d_mm, d_rng, bit_width);
      bzla_bv_set_bit(bv, 0, 1);  // must be odd
      bvinv = bzla_bv_mod_inverse(d_mm, bv);
      mul   = bzla_bv_mul(d_mm, bv, bvinv);
      assert(bzla_bv_is_one(mul));
      bzla_bv_free(d_mm, mul);
      bzla_bv_free(d_mm, bv);
      bzla_bv_free(d_mm, bvinv);
    }
  }

  void flipped_bit_bitvec(uint32_t bit_width)
  {
    uint32_t i, j, pos;
    BzlaBitVector *bv, *res;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      pos = bzla_rng_pick_rand(d_rng, 0, bit_width - 1);
      bv  = bzla_bv_new_random(d_mm, d_rng, bit_width);
      res = bzla_bv_flipped_bit(d_mm, bv, pos);
      ASSERT_EQ(bzla_bv_get_bit(bv, pos), !bzla_bv_get_bit(res, pos));
      for (j = 0; j < bit_width; j++)
      {
        if (j == pos) continue;
        ASSERT_EQ(bzla_bv_get_bit(bv, j), bzla_bv_get_bit(res, j));
      }
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv);
    }
  }

  void flipped_bit_range_bitvec(uint32_t bit_width)
  {
    uint32_t i, j, up, lo;
    BzlaBitVector *bv, *res;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      lo = bzla_rng_pick_rand(d_rng, 0, bit_width - 1);
      up = lo == bit_width - 1
               ? bit_width - 1
               : bzla_rng_pick_rand(d_rng, lo + 1, bit_width - 1);
      bv  = bzla_bv_new_random(d_mm, d_rng, bit_width);
      res = bzla_bv_flipped_bit_range(d_mm, bv, up, lo);
      for (j = lo; j <= up; j++)
        ASSERT_EQ(bzla_bv_get_bit(bv, j), !bzla_bv_get_bit(res, j));
      for (j = 0; j < lo; j++)
        ASSERT_EQ(bzla_bv_get_bit(bv, j), bzla_bv_get_bit(res, j));
      for (j = up + 1; j < bit_width; j++)
        ASSERT_EQ(bzla_bv_get_bit(bv, j), bzla_bv_get_bit(res, j));
      bzla_bv_free(d_mm, res);
      bzla_bv_free(d_mm, bv);
    }
  }

  void new_random_bit_range_bitvec(uint32_t bw)
  {
    uint32_t i, j, up, lo;
    BzlaBitVector *bv1, *bv2, *bv3;

    for (i = 0; i < TEST_BITVEC_TESTS; i++)
    {
      lo  = bzla_rng_pick_rand(d_rng, 0, bw - 1);
      up  = lo == bw - 1 ? bw - 1 : bzla_rng_pick_rand(d_rng, lo + 1, bw - 1);
      bv1 = bzla_bv_new_random_bit_range(d_mm, d_rng, bw, up, lo);
      bv2 = bzla_bv_new_random_bit_range(d_mm, d_rng, bw, up, lo);
      bv3 = bzla_bv_new_random_bit_range(d_mm, d_rng, bw, up, lo);
      for (j = lo; j <= up; j++)
      {
        if (bzla_bv_get_bit(bv1, j) != bzla_bv_get_bit(bv2, j)
            || bzla_bv_get_bit(bv1, j) != bzla_bv_get_bit(bv3, j)
            || bzla_bv_get_bit(bv2, j) != bzla_bv_get_bit(bv3, j))
          break;
      }
      for (j = 0; j < lo; j++)
      {
        assert(bzla_bv_get_bit(bv1, j) == 0);
        assert(bzla_bv_get_bit(bv2, j) == 0);
        assert(bzla_bv_get_bit(bv3, j) == 0);
      }
      for (j = up + 1; j < bw; j++)
      {
        assert(bzla_bv_get_bit(bv1, j) == 0);
        assert(bzla_bv_get_bit(bv2, j) == 0);
        assert(bzla_bv_get_bit(bv3, j) == 0);
      }
      bzla_bv_free(d_mm, bv1);
      bzla_bv_free(d_mm, bv2);
      bzla_bv_free(d_mm, bv3);
    }
  }

  void is_uaddo_bitvec(uint32_t bw)
  {
    BzlaBitVector *bv0, *bv1;

    switch (bw)
    {
      case 1:
        TEST_BV_IS_UADDO_BITVEC(bw, 0, 0, false);
        TEST_BV_IS_UADDO_BITVEC(bw, 0, 1, false);
        TEST_BV_IS_UADDO_BITVEC(bw, 1, 1, true);
        break;
      case 7:
        TEST_BV_IS_UADDO_BITVEC(bw, 3, 6, false);
        TEST_BV_IS_UADDO_BITVEC(bw, 126, 2, true);
        break;
      case 31:
        TEST_BV_IS_UADDO_BITVEC(bw, 15, 78, false);
        TEST_BV_IS_UADDO_BITVEC(bw, 2147483647, 2147483650, true);
        break;
      case 33:
        TEST_BV_IS_UADDO_BITVEC(bw, 15, 78, false);
        TEST_BV_IS_UADDO_BITVEC(bw, 4294967295, 4294967530, true);
        break;
    }
  }

  void is_umulo_bitvec(uint32_t bw)
  {
    BzlaBitVector *bv0, *bv1;

    switch (bw)
    {
      case 1:
        TEST_BV_IS_UMULO_BITVEC(bw, 0, 0, false);
        TEST_BV_IS_UMULO_BITVEC(bw, 0, 1, false);
        TEST_BV_IS_UMULO_BITVEC(bw, 1, 1, false);
        break;
      case 7:
        TEST_BV_IS_UMULO_BITVEC(bw, 3, 6, false);
        TEST_BV_IS_UMULO_BITVEC(bw, 124, 2, true);
        break;
      case 31:
        TEST_BV_IS_UMULO_BITVEC(bw, 15, 78, false);
        TEST_BV_IS_UMULO_BITVEC(bw, 1073742058, 2, true);
        break;
      case 33:
        TEST_BV_IS_UMULO_BITVEC(bw, 15, 78, false);
        TEST_BV_IS_UMULO_BITVEC(bw, 4294967530, 4294967530, true);
        break;
    }
  }

  void test_get_num_aux(const std::string &val,
                        uint32_t (*fun)(const BzlaBitVector *),
                        bool from_msb = true,
                        bool zeros    = true)
  {
    BzlaBitVector *bv;
    uint32_t bw  = val.size();
    uint32_t exp = 0;
    char c       = zeros ? '0' : '1';
    if (from_msb)
    {
      for (exp = 0; exp < bw && val[exp] == c; ++exp)
        ;
    }
    else
    {
      for (exp = 0; exp < bw && val[bw - 1 - exp] == c; ++exp)
        ;
    }
    bv = bzla_bv_char_to_bv(d_mm, val.c_str());
    ASSERT_EQ(fun(bv), exp);
    bzla_bv_free(d_mm, bv);
  }

  void test_get_num(uint32_t bw,
                    uint32_t (*fun)(const BzlaBitVector *),
                    bool from_msb = true,
                    bool zeros    = true)
  {
    if (bw == 8)
    {
      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        ss << std::bitset<8>(i).to_string();
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }
    }
    else
    {
      // concat 8-bit value with 0s to create value for bv
      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << v << std::string(bw - 8, '0');
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }

      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << std::string(bw - 8, '0') << v;
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }

      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << v << std::string(bw - 16, '0') << v;
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }

      // concat 8bit-values with 1s to create value for bv
      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << v << std::string(bw - 8, '1');
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }

      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << std::string(bw - 8, '1') << v;
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }

      for (uint64_t i = 0; i < (1u << 8); ++i)
      {
        std::stringstream ss;
        std::string v = std::bitset<8>(i).to_string();
        ss << v << std::string(bw - 16, '1') << v;
        test_get_num_aux(ss.str(), fun, from_msb, zeros);
      }
    }
  }

  BzlaMemMgr *d_mm;
  BzlaRNG *d_rng;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestBv, new)
{
  BzlaBitVector *bv;

  bv = bzla_bv_new(d_mm, TEST_BW);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_new(d_mm, TEST_BW - 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_new(d_mm, TEST_BW + 1);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, new_random)
{
  uint32_t bw;
  BzlaBitVector *bv1, *bv2, *bv3;

  for (bw = 1; bw <= 64; bw++)
  {
    bv1 = bzla_bv_new_random(d_mm, d_rng, bw);
    bv2 = bzla_bv_new_random(d_mm, d_rng, bw);
    bv3 = bzla_bv_new_random(d_mm, d_rng, bw);
    assert(bzla_bv_compare(bv1, bv2) || bzla_bv_compare(bv1, bv3)
           || bzla_bv_compare(bv2, bv3));
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, new_random_range)
{
  uint32_t bw;
  uint64_t val;
  BzlaBitVector *bv, *from, *to, *tmp;

  for (bw = 1; bw <= 64; bw++)
  {
    from = bzla_bv_new_random(d_mm, d_rng, bw);
    // from == to
    bv  = bzla_bv_new_random_range(d_mm, d_rng, bw, from, from);
    val = bzla_bv_to_uint64(bv);
    ASSERT_EQ(val, bzla_bv_to_uint64(from));
    bzla_bv_free(d_mm, bv);
    // from < to
    to = bzla_bv_new_random(d_mm, d_rng, bw);
    while (!bzla_bv_compare(from, to))
    {
      bzla_bv_free(d_mm, to);
      to = bzla_bv_new_random(d_mm, d_rng, bw);
    }
    if (bzla_bv_to_uint64(to) < bzla_bv_to_uint64(from))
    {
      tmp  = to;
      to   = from;
      from = tmp;
    }
    bv  = bzla_bv_new_random_range(d_mm, d_rng, bw, from, to);
    val = bzla_bv_to_uint64(bv);
    ASSERT_GE(val, bzla_bv_to_uint64(from));
    ASSERT_LE(val, bzla_bv_to_uint64(to));
    bzla_bv_free(d_mm, from);
    bzla_bv_free(d_mm, to);
    bzla_bv_free(d_mm, bv);
  }
}

TEST_F(TestBv, new_random_signed_range)
{
  uint32_t bw;
  int64_t val;
  BzlaBitVector *bv, *from, *to, *tmp;

  for (bw = 1; bw <= 64; bw++)
  {
    from = bzla_bv_new_random(d_mm, d_rng, bw);
    // from == to
    bv  = bzla_bv_new_random_signed_range(d_mm, d_rng, bw, from, from);
    val = bzla_bv_to_uint64(bv);
    ASSERT_EQ(val, bzla_bv_to_uint64(from));
    bzla_bv_free(d_mm, bv);
    // from < to
    to = bzla_bv_new_random(d_mm, d_rng, bw);
    while (!bzla_bv_signed_compare(from, to))
    {
      bzla_bv_free(d_mm, to);
      to = bzla_bv_new_random(d_mm, d_rng, bw);
    }
    if (bzla_bv_signed_compare(from, to) >= 0)
    {
      tmp  = to;
      to   = from;
      from = tmp;
    }
    bv = bzla_bv_new_random_signed_range(d_mm, d_rng, bw, from, to);
    ASSERT_LE(bzla_bv_signed_compare(from, bv), 0);
    ASSERT_LE(bzla_bv_signed_compare(bv, to), 0);
    bzla_bv_free(d_mm, from);
    bzla_bv_free(d_mm, to);
    bzla_bv_free(d_mm, bv);
  }
}

TEST_F(TestBv, new_random_bit_range)
{
  new_random_bit_range_bitvec(1);
  new_random_bit_range_bitvec(7);
  new_random_bit_range_bitvec(31);
  new_random_bit_range_bitvec(33);
  new_random_bit_range_bitvec(64);
}

TEST_F(TestBv, copy)
{
  uint32_t bw;
  BzlaBitVector *bv1, *bv2;

  for (bw = 1; bw <= 64; bw++)
  {
    bv1 = bzla_bv_new_random(d_mm, d_rng, bw);
    bv2 = bzla_bv_copy(d_mm, bv1);
    assert(!bzla_bv_compare(bv1, bv2));
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }
}

/* This is not true in corner cases or if the RNG is not random enough.
 * If this fails due to that we might want to consider a larger sample. */
TEST_F(TestBv, hash)
{
  uint32_t bw, hash1, hash2, hash3;
  BzlaBitVector *bv1, *bv2, *bv3;

  for (bw = 32; bw <= 64; bw++)
  {
    bv1   = bzla_bv_new_random(d_mm, d_rng, bw);
    bv2   = bzla_bv_new_random(d_mm, d_rng, bw);
    bv3   = bzla_bv_new_random(d_mm, d_rng, bw);
    hash1 = bzla_bv_hash(bv1);
    hash2 = bzla_bv_hash(bv2);
    hash3 = bzla_bv_hash(bv3);
    (void) hash1;
    (void) hash2;
    (void) hash3;
    assert(!bzla_bv_compare(bv1, bv2) || hash1 != hash2
           || !bzla_bv_compare(bv1, bv3) || hash1 != hash3
           || !bzla_bv_compare(bv2, bv3) || hash2 != hash3);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

/*------------------------------------------------------------------------*/

TEST_F(TestBv, uint64_to_bv)
{
  uint64_t i, j, k, l;
  BzlaBitVector *bv;

  bv = bzla_bv_uint64_to_bv(d_mm, 0, 32);
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_uint64_to_bv(d_mm, UINT32_MAX, 32);
  ASSERT_EQ(bzla_bv_to_uint64(bv), UINT32_MAX);
  bzla_bv_free(d_mm, bv);

  for (i = 0; i < 10; i++)
  {
    for (j = 0; j < 5; j++)
    {
      l  = rand() % 32 + 1;
      bv = bzla_bv_new_random(d_mm, d_rng, l);
      k  = bzla_bv_to_uint64(bv);
      bzla_bv_free(d_mm, bv);
      bv = bzla_bv_uint64_to_bv(d_mm, k, l);
      ASSERT_EQ(bzla_bv_to_uint64(bv), k);
      bzla_bv_free(d_mm, bv);
    }
  }
}

TEST_F(TestBv, uint64_to_bv_to_uint64)
{
  uint64_t i, x, y;
  BzlaBitVector *a;

  for (i = 0; i < 10000000; i++)
  {
    x = ((uint64_t) rand()) << 32;
    x |= (uint64_t) rand();
    a = bzla_bv_uint64_to_bv(d_mm, x, 64);
    y = bzla_bv_to_uint64(a);
    ASSERT_EQ(x, y);
    bzla_bv_free(d_mm, a);
  }
}

TEST_F(TestBv, int64_to_bv)
{
  uint32_t bw;
  uint64_t i;
  BzlaBitVector *a, *ua, *tmp, *b;
  char *str_a;
  int64_t x[] = {
      -1,
      -2,
      -3,
      -123,
      3,
  };
  const char *str_x[] = {
      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111111",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111110",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "1111111111111111111111111111101",

      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111111111111"
      "11111111111111111111111110000101",

      "00000000000000000000000000000000"
      "00000000000000000000000000000000"
      "00000000000000000000000000000011",

      0};

  for (i = 0; str_x[i]; i++)
  {
    assert(str_x[i]);
    bw    = strlen(str_x[i]);
    a     = bzla_bv_int64_to_bv(d_mm, x[i], bw);
    str_a = bzla_bv_to_char(d_mm, a);
    ASSERT_EQ(strcmp(str_a, str_x[i]), 0);
    bzla_mem_freestr(d_mm, str_a);
    if (x[i] < 0)
    {
      tmp = bzla_bv_uint64_to_bv(d_mm, -x[i], bw);
      ua  = bzla_bv_neg(d_mm, tmp);
      bzla_bv_free(d_mm, tmp);
      tmp = bzla_bv_uint64_to_bv(d_mm, x[i], bw);
      b   = bzla_bv_neg(d_mm, tmp);
      bzla_bv_free(d_mm, tmp);
    }
    else
    {
      ua = bzla_bv_uint64_to_bv(d_mm, x[i], bw);
      b  = bzla_bv_uint64_to_bv(d_mm, -x[i], bw);
    }
    ASSERT_EQ(bzla_bv_compare(a, ua), 0);
    ASSERT_NE(bzla_bv_compare(a, b), 0);
    bzla_bv_free(d_mm, a);
    bzla_bv_free(d_mm, b);
    bzla_bv_free(d_mm, ua);
  }
}

/*------------------------------------------------------------------------*/

TEST_F(TestBv, char_to_bv)
{
  BzlaBitVector *bv;

  bv = bzla_bv_char_to_bv(d_mm, "0");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "01");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 3u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "001");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "010");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "011");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 3u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "100");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 4u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "101");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 5u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "110");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 6u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 7u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000000001");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000000010");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000000100");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 4u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000001000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 8u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000010000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 16u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000000100000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 32u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000001000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 64u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000010000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 128u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000000100000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 256u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000001000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 512u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000010000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1024u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000000100000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2048u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000001000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 4096u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000010000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 8192u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000000100000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 16384u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000001000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 32768u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000010000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 65536u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000000100000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 131072u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000001000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 262144u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000010000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 524288u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000000100000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1048576u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000001000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2097152u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000010000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 4194304u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000000100000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 8388608u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000001000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 16777216u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000010000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 33554432u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00000100000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 67108864u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00001000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 134217728u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00010000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 268435456u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00100000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 536870912u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "01000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1073741824u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 2147483648u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11111111111111111111111111111111");
  ASSERT_EQ(bzla_bv_to_uint64(bv), UINT32_MAX);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000000000000000000000000000000001");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111111111111111111111111111111111");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 8589934591u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 0u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000000000000000000000000000000001");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 1u);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1111111111111111111111111111111111");
  ASSERT_EQ(bzla_bv_to_uint64(bv), 17179869183u);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, bv_to_char)
{
  uint32_t i, j, k;
  uint32_t b;
  char *s;
  BzlaBitVector *bv;

  for (i = 1; i < 4; i++)
  {
    for (j = 0; j < (1u << i); j++)
    {
      bv = bzla_bv_uint64_to_bv(d_mm, j, i);
      TEST_BV_CHECK_CHAR_TO_BV(bv, i);
    }
  }

  bv = bzla_bv_uint64_to_bv(d_mm, UINT32_MAX, 32);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 32);

  bv = bzla_bv_uint64_to_bv(d_mm, 0, 32);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 32);

  bv = bzla_bv_uint64_to_bv(d_mm, 1, 32);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 32);

  for (i = 0; i < 20; i++)
  {
    bv = bzla_bv_new_random(d_mm, d_rng, 32);
    TEST_BV_CHECK_CHAR_TO_BV(bv, 32);
  }

  bv = bzla_bv_uint64_to_bv(d_mm, 8589934591, 33);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 33);

  bv = bzla_bv_uint64_to_bv(d_mm, 0, 33);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 33);

  bv = bzla_bv_uint64_to_bv(d_mm, 1, 33);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 33);

  bv = bzla_bv_uint64_to_bv(d_mm, 17179869183, 34);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 34);

  bv = bzla_bv_uint64_to_bv(d_mm, 0, 34);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 34);

  bv = bzla_bv_uint64_to_bv(d_mm, 1, 34);
  TEST_BV_CHECK_CHAR_TO_BV(bv, 34);
}

/*------------------------------------------------------------------------*/

TEST_F(TestBv, bv_to_hex_char)
{
  open_log_file("bv_to_hex_char_bitvec");
  bv_to_hex_char_bitvec(d_log_file, "1");
  bv_to_hex_char_bitvec(d_log_file, "10");
  bv_to_hex_char_bitvec(d_log_file, "11");
  bv_to_hex_char_bitvec(d_log_file, "100");
  bv_to_hex_char_bitvec(d_log_file, "101");
  bv_to_hex_char_bitvec(d_log_file, "110");
  bv_to_hex_char_bitvec(d_log_file, "111");
  bv_to_hex_char_bitvec(d_log_file, "1000");
  bv_to_hex_char_bitvec(d_log_file, "1001");
  bv_to_hex_char_bitvec(d_log_file, "1010");
  bv_to_hex_char_bitvec(d_log_file, "1011");
  bv_to_hex_char_bitvec(d_log_file, "1100");
  bv_to_hex_char_bitvec(d_log_file, "1101");
  bv_to_hex_char_bitvec(d_log_file, "1110");
  bv_to_hex_char_bitvec(d_log_file, "1111");
  bv_to_hex_char_bitvec(d_log_file, "10000");
  bv_to_hex_char_bitvec(d_log_file, "10001");
  bv_to_hex_char_bitvec(d_log_file, "1111111111111111");
  bv_to_hex_char_bitvec(d_log_file, "11111111111111111");
  bv_to_hex_char_bitvec(d_log_file, "00001111111111111111");
  bv_to_hex_char_bitvec(d_log_file, "000011111111111111111");
}

TEST_F(TestBv, bv_to_dec_char)
{
  open_log_file("bv_to_dec_char_bitvec");
  bv_to_dec_char_bitvec(d_log_file, "1");
  bv_to_dec_char_bitvec(d_log_file, "10");
  bv_to_dec_char_bitvec(d_log_file, "11");
  bv_to_dec_char_bitvec(d_log_file, "100");
  bv_to_dec_char_bitvec(d_log_file, "101");
  bv_to_dec_char_bitvec(d_log_file, "110");
  bv_to_dec_char_bitvec(d_log_file, "111");
  bv_to_dec_char_bitvec(d_log_file, "1000");
  bv_to_dec_char_bitvec(d_log_file, "1001");
  bv_to_dec_char_bitvec(d_log_file, "1010");
  bv_to_dec_char_bitvec(d_log_file, "1011");
  bv_to_dec_char_bitvec(d_log_file, "1100");
  bv_to_dec_char_bitvec(d_log_file, "1101");
  bv_to_dec_char_bitvec(d_log_file, "1110");
  bv_to_dec_char_bitvec(d_log_file, "1111");
  bv_to_dec_char_bitvec(d_log_file, "10000");
  bv_to_dec_char_bitvec(d_log_file, "10001");
  bv_to_dec_char_bitvec(d_log_file, "10000000000000000");
  bv_to_dec_char_bitvec(d_log_file,
                        "1"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000");
  bv_to_dec_char_bitvec(d_log_file,
                        "1"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000");
  bv_to_dec_char_bitvec(d_log_file,
                        "1"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000"
                        "00000000");
}

/*------------------------------------------------------------------------*/

TEST_F(TestBv, const)
{
  BzlaBitVector *bv;

  bv = bzla_bv_const(d_mm, "0", 1);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "1", 1);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00", 2);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "01", 2);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "10", 2);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "11", 2);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "000", 3);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "001", 3);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "010", 3);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "011", 3);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "100", 3);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "101", 3);
  assert(bzla_bv_to_uint64(bv) == 5);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "110", 3);
  assert(bzla_bv_to_uint64(bv) == 6);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "111", 3);
  assert(bzla_bv_to_uint64(bv) == 7);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000000001", 32);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000000010", 32);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000000100", 32);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000001000", 32);
  assert(bzla_bv_to_uint64(bv) == 8);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000010000", 32);
  assert(bzla_bv_to_uint64(bv) == 16);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000000100000", 32);
  assert(bzla_bv_to_uint64(bv) == 32);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000001000000", 32);
  assert(bzla_bv_to_uint64(bv) == 64);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000010000000", 32);
  assert(bzla_bv_to_uint64(bv) == 128);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000000100000000", 32);
  assert(bzla_bv_to_uint64(bv) == 256);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000001000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 512);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000010000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 1024);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000000100000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 2048);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000001000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 4096);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000010000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 8192);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000000100000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 16384);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000001000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 32768);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000010000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 65536);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000000100000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 131072);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000001000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 262144);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000010000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 524288);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000000100000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 1048576);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000001000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 2097152);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000010000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 4194304);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000000100000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 8388608);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000001000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 16777216);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000010000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 33554432);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00000100000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 67108864);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00001000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 134217728);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00010000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 268435456);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "00100000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 536870912);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "01000000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 1073741824);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "10000000000000000000000000000000", 32);
  assert(bzla_bv_to_uint64(bv) == 2147483648);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "11111111111111111111111111111111", 32);
  assert(bzla_bv_to_uint64(bv) == UINT32_MAX);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "000000000000000000000000000000000", 33);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "000000000000000000000000000000001", 33);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "111111111111111111111111111111111", 33);
  assert(bzla_bv_to_uint64(bv) == 8589934591);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "0000000000000000000000000000000000", 34);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "0000000000000000000000000000000001", 34);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_const(d_mm, "1111111111111111111111111111111111", 34);
  assert(bzla_bv_to_uint64(bv) == 17179869183);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, constd)
{
  BzlaBitVector *bv;

  bv = bzla_bv_constd(d_mm, "0", 1);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 1);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "0", 2);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 2);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2", 2);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "3", 2);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "0", 3);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 3);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2", 3);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "3", 3);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "4", 3);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "5", 3);
  assert(bzla_bv_to_uint64(bv) == 5);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "6", 3);
  assert(bzla_bv_to_uint64(bv) == 6);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "7", 3);
  assert(bzla_bv_to_uint64(bv) == 7);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "0", 32);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 32);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2", 32);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "4", 32);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "8", 32);
  assert(bzla_bv_to_uint64(bv) == 8);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "16", 32);
  assert(bzla_bv_to_uint64(bv) == 16);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "32", 32);
  assert(bzla_bv_to_uint64(bv) == 32);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "64", 32);
  assert(bzla_bv_to_uint64(bv) == 64);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "128", 32);
  assert(bzla_bv_to_uint64(bv) == 128);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "256", 32);
  assert(bzla_bv_to_uint64(bv) == 256);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "512", 32);
  assert(bzla_bv_to_uint64(bv) == 512);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1024", 32);
  assert(bzla_bv_to_uint64(bv) == 1024);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2048", 32);
  assert(bzla_bv_to_uint64(bv) == 2048);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "4096", 32);
  assert(bzla_bv_to_uint64(bv) == 4096);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "8192", 32);
  assert(bzla_bv_to_uint64(bv) == 8192);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "16384", 32);
  assert(bzla_bv_to_uint64(bv) == 16384);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "32768", 32);
  assert(bzla_bv_to_uint64(bv) == 32768);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "65536", 32);
  assert(bzla_bv_to_uint64(bv) == 65536);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "131072", 32);
  assert(bzla_bv_to_uint64(bv) == 131072);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "262144", 32);
  assert(bzla_bv_to_uint64(bv) == 262144);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "524288", 32);
  assert(bzla_bv_to_uint64(bv) == 524288);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1048576", 32);
  assert(bzla_bv_to_uint64(bv) == 1048576);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2097152", 32);
  assert(bzla_bv_to_uint64(bv) == 2097152);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "4194304", 32);
  assert(bzla_bv_to_uint64(bv) == 4194304);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "8388608", 32);
  assert(bzla_bv_to_uint64(bv) == 8388608);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "16777216", 32);
  assert(bzla_bv_to_uint64(bv) == 16777216);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "33554432", 32);
  assert(bzla_bv_to_uint64(bv) == 33554432);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "67108864", 32);
  assert(bzla_bv_to_uint64(bv) == 67108864);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "134217728", 32);
  assert(bzla_bv_to_uint64(bv) == 134217728);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "268435456", 32);
  assert(bzla_bv_to_uint64(bv) == 268435456);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "536870912", 32);
  assert(bzla_bv_to_uint64(bv) == 536870912);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1073741824", 32);
  assert(bzla_bv_to_uint64(bv) == 1073741824);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "2147483648", 32);
  assert(bzla_bv_to_uint64(bv) == 2147483648);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "4294967295", 32);
  assert(bzla_bv_to_uint64(bv) == UINT32_MAX);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "0", 33);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 33);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "8589934591", 33);
  assert(bzla_bv_to_uint64(bv) == 8589934591);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "0", 34);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "1", 34);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_constd(d_mm, "17179869183", 34);
  assert(bzla_bv_to_uint64(bv) == 17179869183);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, consth)
{
  BzlaBitVector *bv;

  bv = bzla_bv_consth(d_mm, "0", 1);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1", 1);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "0", 2);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1", 2);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "2", 2);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "3", 2);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "0", 3);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1", 3);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "2", 3);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "3", 3);
  assert(bzla_bv_to_uint64(bv) == 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "4", 3);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "5", 3);
  assert(bzla_bv_to_uint64(bv) == 5);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "6", 3);
  assert(bzla_bv_to_uint64(bv) == 6);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "7", 3);
  assert(bzla_bv_to_uint64(bv) == 7);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "0", 32);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1", 32);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "2", 32);
  assert(bzla_bv_to_uint64(bv) == 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "4", 32);
  assert(bzla_bv_to_uint64(bv) == 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "8", 32);
  assert(bzla_bv_to_uint64(bv) == 8);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "10", 32);
  assert(bzla_bv_to_uint64(bv) == 16);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "20", 32);
  assert(bzla_bv_to_uint64(bv) == 32);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "40", 32);
  assert(bzla_bv_to_uint64(bv) == 64);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "80", 32);
  assert(bzla_bv_to_uint64(bv) == 128);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "100", 32);
  assert(bzla_bv_to_uint64(bv) == 256);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "200", 32);
  assert(bzla_bv_to_uint64(bv) == 512);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "400", 32);
  assert(bzla_bv_to_uint64(bv) == 1024);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "800", 32);
  assert(bzla_bv_to_uint64(bv) == 2048);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1000", 32);
  assert(bzla_bv_to_uint64(bv) == 4096);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "2000", 32);
  assert(bzla_bv_to_uint64(bv) == 8192);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "4000", 32);
  assert(bzla_bv_to_uint64(bv) == 16384);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "8000", 32);
  assert(bzla_bv_to_uint64(bv) == 32768);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "10000", 32);
  assert(bzla_bv_to_uint64(bv) == 65536);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "20000", 32);
  assert(bzla_bv_to_uint64(bv) == 131072);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "40000", 32);
  assert(bzla_bv_to_uint64(bv) == 262144);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "80000", 32);
  assert(bzla_bv_to_uint64(bv) == 524288);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "100000", 32);
  assert(bzla_bv_to_uint64(bv) == 1048576);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "200000", 32);
  assert(bzla_bv_to_uint64(bv) == 2097152);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "400000", 32);
  assert(bzla_bv_to_uint64(bv) == 4194304);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "800000", 32);
  assert(bzla_bv_to_uint64(bv) == 8388608);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1000000", 32);
  assert(bzla_bv_to_uint64(bv) == 16777216);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "2000000", 32);
  assert(bzla_bv_to_uint64(bv) == 33554432);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "4000000", 32);
  assert(bzla_bv_to_uint64(bv) == 67108864);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "8000000", 32);
  assert(bzla_bv_to_uint64(bv) == 134217728);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "10000000", 32);
  assert(bzla_bv_to_uint64(bv) == 268435456);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "20000000", 32);
  assert(bzla_bv_to_uint64(bv) == 536870912);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "40000000", 32);
  assert(bzla_bv_to_uint64(bv) == 1073741824);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "80000000", 32);
  assert(bzla_bv_to_uint64(bv) == 2147483648);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "ffffffff", 32);
  assert(bzla_bv_to_uint64(bv) == UINT32_MAX);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "0", 33);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "a", 33);
  assert(bzla_bv_to_uint64(bv) == 10);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1ffffffff", 33);
  assert(bzla_bv_to_uint64(bv) == 8589934591);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "0", 34);
  assert(bzla_bv_to_uint64(bv) == 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "1", 34);
  assert(bzla_bv_to_uint64(bv) == 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_consth(d_mm, "3ffffffff", 34);
  assert(bzla_bv_to_uint64(bv) == 17179869183);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, set_get_flip_bit)
{
  int32_t i;
  uint32_t n, v, vv;
  BzlaBitVector *bv;

  for (i = 1; i < 32; i++)
  {
    bv = bzla_bv_new_random(d_mm, d_rng, i);
    n  = bzla_rng_pick_rand(d_rng, 0, i - 1);
    v  = bzla_bv_get_bit(bv, n);
    vv = bzla_rng_pick_with_prob(d_rng, 500) ? 1 : 0;
    bzla_bv_set_bit(bv, n, vv);
    (void) v;
    assert(bzla_bv_get_bit(bv, n) == vv);
    assert(v == vv || bzla_bv_get_bit(bv, n) == (((~v) << 31) >> 31));
    bzla_bv_flip_bit(bv, n);
    assert(bzla_bv_get_bit(bv, n) == (((~vv) << 31) >> 31));
    bzla_bv_free(d_mm, bv);
  }
}

TEST_F(TestBv, not )
{
  unary_bitvec(_not, bzla_bv_not, 1);
  unary_bitvec(_not, bzla_bv_not, 7);
  unary_bitvec(_not, bzla_bv_not, 31);
  unary_bitvec(_not, bzla_bv_not, 33);
}

TEST_F(TestBv, neg)
{
  unary_bitvec(neg, bzla_bv_neg, 1);
  unary_bitvec(neg, bzla_bv_neg, 7);
  unary_bitvec(neg, bzla_bv_neg, 31);
  unary_bitvec(neg, bzla_bv_neg, 33);
}

TEST_F(TestBv, redand)
{
  unary_bitvec(redand, bzla_bv_redand, 1);
  unary_bitvec(redand, bzla_bv_redand, 7);
  unary_bitvec(redand, bzla_bv_redand, 31);
  unary_bitvec(redand, bzla_bv_redand, 33);
}

TEST_F(TestBv, redor)
{
  unary_bitvec(redor, bzla_bv_redor, 1);
  unary_bitvec(redor, bzla_bv_redor, 7);
  unary_bitvec(redor, bzla_bv_redor, 31);
  unary_bitvec(redor, bzla_bv_redor, 33);
}

TEST_F(TestBv, inc)
{
  unary_bitvec(inc, bzla_bv_inc, 1);
  unary_bitvec(inc, bzla_bv_inc, 7);
  unary_bitvec(inc, bzla_bv_inc, 31);
  unary_bitvec(inc, bzla_bv_inc, 33);
}

TEST_F(TestBv, dec)
{
  unary_bitvec(dec, bzla_bv_dec, 1);
  unary_bitvec(dec, bzla_bv_dec, 7);
  unary_bitvec(dec, bzla_bv_dec, 31);
  unary_bitvec(dec, bzla_bv_dec, 33);
}

TEST_F(TestBv, add)
{
  binary_bitvec(add, bzla_bv_add, 1);
  binary_bitvec(add, bzla_bv_add, 7);
  binary_bitvec(add, bzla_bv_add, 31);
  binary_bitvec(add, bzla_bv_add, 33);
}

TEST_F(TestBv, sub)
{
  binary_bitvec(sub, bzla_bv_sub, 1);
  binary_bitvec(sub, bzla_bv_sub, 7);
  binary_bitvec(sub, bzla_bv_sub, 31);
  binary_bitvec(sub, bzla_bv_sub, 33);
}

TEST_F(TestBv, and)
{
  binary_bitvec(_and, bzla_bv_and, 1);
  binary_bitvec(_and, bzla_bv_and, 7);
  binary_bitvec(_and, bzla_bv_and, 31);
  binary_bitvec(_and, bzla_bv_and, 33);
  binary_bitvec(_and, bzla_bv_and, 64);
}

TEST_F(TestBv, nand)
{
  binary_bitvec(nand, bzla_bv_nand, 1);
  binary_bitvec(nand, bzla_bv_nand, 7);
  binary_bitvec(nand, bzla_bv_nand, 31);
  binary_bitvec(nand, bzla_bv_nand, 33);
  binary_bitvec(nand, bzla_bv_nand, 64);
}

TEST_F(TestBv, or)
{
  binary_bitvec(_or, bzla_bv_or, 1);
  binary_bitvec(_or, bzla_bv_or, 7);
  binary_bitvec(_or, bzla_bv_or, 31);
  binary_bitvec(_or, bzla_bv_or, 33);
  binary_bitvec(_or, bzla_bv_or, 64);
}

TEST_F(TestBv, nor)
{
  binary_bitvec(nor, bzla_bv_nor, 1);
  binary_bitvec(nor, bzla_bv_nor, 7);
  binary_bitvec(nor, bzla_bv_nor, 31);
  binary_bitvec(nor, bzla_bv_nor, 33);
  binary_bitvec(nor, bzla_bv_nor, 64);
}

TEST_F(TestBv, xnor)
{
  binary_bitvec(xnor, bzla_bv_xnor, 1);
  binary_bitvec(xnor, bzla_bv_xnor, 7);
  binary_bitvec(xnor, bzla_bv_xnor, 31);
  binary_bitvec(xnor, bzla_bv_xnor, 33);
  binary_bitvec(xnor, bzla_bv_xnor, 64);
}

TEST_F(TestBv, implies) { binary_bitvec(implies, bzla_bv_implies, 1); }

TEST_F(TestBv, xor)
{
  binary_bitvec(_xor, bzla_bv_xor, 1);
  binary_bitvec(_xor, bzla_bv_xor, 7);
  binary_bitvec(_xor, bzla_bv_xor, 31);
  binary_bitvec(_xor, bzla_bv_xor, 33);
  binary_bitvec(_xor, bzla_bv_xor, 64);
}

TEST_F(TestBv, eq)
{
  binary_bitvec(eq, bzla_bv_eq, 1);
  binary_bitvec(eq, bzla_bv_eq, 7);
  binary_bitvec(eq, bzla_bv_eq, 31);
  binary_bitvec(eq, bzla_bv_eq, 33);
  binary_bitvec(eq, bzla_bv_eq, 64);
}

TEST_F(TestBv, ne)
{
  binary_bitvec(ne, bzla_bv_ne, 1);
  binary_bitvec(ne, bzla_bv_ne, 7);
  binary_bitvec(ne, bzla_bv_ne, 31);
  binary_bitvec(ne, bzla_bv_ne, 33);
  binary_bitvec(ne, bzla_bv_ne, 64);
}

TEST_F(TestBv, ult)
{
  binary_bitvec(ult, bzla_bv_ult, 1);
  binary_bitvec(ult, bzla_bv_ult, 7);
  binary_bitvec(ult, bzla_bv_ult, 31);
  binary_bitvec(ult, bzla_bv_ult, 33);
  binary_bitvec(ult, bzla_bv_ult, 64);
}

TEST_F(TestBv, ulte)
{
  binary_bitvec(ulte, bzla_bv_ulte, 1);
  binary_bitvec(ulte, bzla_bv_ulte, 7);
  binary_bitvec(ulte, bzla_bv_ulte, 31);
  binary_bitvec(ulte, bzla_bv_ulte, 33);
  binary_bitvec(ulte, bzla_bv_ulte, 64);
}

TEST_F(TestBv, ugt)
{
  binary_bitvec(ugt, bzla_bv_ugt, 1);
  binary_bitvec(ugt, bzla_bv_ugt, 7);
  binary_bitvec(ugt, bzla_bv_ugt, 31);
  binary_bitvec(ugt, bzla_bv_ugt, 33);
  binary_bitvec(ugt, bzla_bv_ugt, 64);
}

TEST_F(TestBv, ugte)
{
  binary_bitvec(ugte, bzla_bv_ugte, 1);
  binary_bitvec(ugte, bzla_bv_ugte, 7);
  binary_bitvec(ugte, bzla_bv_ugte, 31);
  binary_bitvec(ugte, bzla_bv_ugte, 33);
  binary_bitvec(ugte, bzla_bv_ugte, 64);
}

TEST_F(TestBv, slt)
{
  binary_signed_bitvec(slt, bzla_bv_slt, 1);
  binary_signed_bitvec(slt, bzla_bv_slt, 7);
  binary_signed_bitvec(slt, bzla_bv_slt, 31);
  binary_signed_bitvec(slt, bzla_bv_slt, 33);
  binary_signed_bitvec(slt, bzla_bv_slt, 64);
}

TEST_F(TestBv, slte)
{
  binary_signed_bitvec(slte, bzla_bv_slte, 1);
  binary_signed_bitvec(slte, bzla_bv_slte, 7);
  binary_signed_bitvec(slte, bzla_bv_slte, 31);
  binary_signed_bitvec(slte, bzla_bv_slte, 33);
  binary_signed_bitvec(slte, bzla_bv_slte, 64);
}

TEST_F(TestBv, sgt)
{
  binary_signed_bitvec(sgt, bzla_bv_sgt, 1);
  binary_signed_bitvec(sgt, bzla_bv_sgt, 7);
  binary_signed_bitvec(sgt, bzla_bv_sgt, 31);
  binary_signed_bitvec(sgt, bzla_bv_sgt, 33);
  binary_signed_bitvec(sgt, bzla_bv_sgt, 64);
}

TEST_F(TestBv, sgte)
{
  binary_signed_bitvec(sgte, bzla_bv_sgte, 1);
  binary_signed_bitvec(sgte, bzla_bv_sgte, 7);
  binary_signed_bitvec(sgte, bzla_bv_sgte, 31);
  binary_signed_bitvec(sgte, bzla_bv_sgte, 33);
  binary_signed_bitvec(sgte, bzla_bv_sgte, 64);
}

TEST_F(TestBv, sll)
{
  binary_bitvec(sll, bzla_bv_sll, 2);
  binary_bitvec(sll, bzla_bv_sll, 8);
  binary_bitvec(sll, bzla_bv_sll, 16);
  binary_bitvec(sll, bzla_bv_sll, 32);

  for (uint32_t i = 0, bw = 2; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::bitset<2>(i).to_string() << std::string(j, '0');
      std::string expected = ss_expected.str();
      expected             = expected.substr(expected.size() - bw, bw);
      shift_bitvec(std::bitset<2>(i).to_string().c_str(),
                   std::bitset<2>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sll);
    }
  }

  for (uint32_t i = 0, bw = 3; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::bitset<3>(i).to_string() << std::string(j, '0');
      std::string expected = ss_expected.str();
      expected             = expected.substr(expected.size() - bw, bw);
      shift_bitvec(std::bitset<3>(i).to_string().c_str(),
                   std::bitset<3>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sll);
    }
  }

  for (uint32_t i = 0, bw = 8; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::bitset<8>(i).to_string() << std::string(j, '0');
      std::string expected = ss_expected.str();
      expected             = expected.substr(expected.size() - bw, bw);
      shift_bitvec(std::bitset<8>(i).to_string().c_str(),
                   std::bitset<8>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sll);
    }
  }

  for (uint32_t i = 0, bw = 65; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::bitset<65>(i).to_string() << std::string(j, '0');
      std::string expected = ss_expected.str();
      expected             = expected.substr(expected.size() - bw, bw);
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sll);
    }
    /* shift value doesn't fit into uint64_t */
    {
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(0u).set(64, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_sll);
    }
  }

  for (uint32_t i = 0, bw = 128; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::bitset<128>(i).to_string() << std::string(j, '0');
      std::string expected = ss_expected.str();
      expected             = expected.substr(expected.size() - bw, bw);
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sll);
    }
    /* shift value doesn't fit into uint64_t */
    for (uint64_t j = 64; j < 128; ++j)
    {
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(0u).set(j, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_sll);
    }
  }
}

TEST_F(TestBv, srl)
{
  binary_bitvec(srl, bzla_bv_srl, 2);
  binary_bitvec(srl, bzla_bv_srl, 8);
  binary_bitvec(srl, bzla_bv_srl, 16);
  binary_bitvec(srl, bzla_bv_srl, 32);

  for (uint32_t i = 0, bw = 2; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::string(j, '0') << std::bitset<2>(i).to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<2>(i).to_string().c_str(),
                   std::bitset<2>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_srl);
    }
  }

  for (uint32_t i = 0, bw = 3; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::string(j, '0') << std::bitset<3>(i).to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<3>(i).to_string().c_str(),
                   std::bitset<3>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_srl);
    }
  }

  for (uint32_t i = 0, bw = 8; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::string(j, '0') << std::bitset<8>(i).to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<8>(i).to_string().c_str(),
                   std::bitset<8>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_srl);
    }
  }

  for (uint32_t i = 0, bw = 65; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::string(j, '0') << std::bitset<65>(i).to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_srl);
    }
    /* shift value doesn't fit into uint64_t */
    {
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(0u).set(64, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_srl);
    }
  }

  for (uint32_t i = 0, bw = 128; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      ss_expected << std::string(j, '0') << std::bitset<128>(i).to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_srl);
    }
    /* shift value doesn't fit into uint64_t */
    {
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(0u).set(120, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_srl);
    }
  }
}

TEST_F(TestBv, sra)
{
  binary_bitvec(sra, bzla_bv_sra, 2);
  binary_bitvec(sra, bzla_bv_sra, 8);
  binary_bitvec(sra, bzla_bv_sra, 9);
  binary_bitvec(sra, bzla_bv_sra, 16);
  binary_bitvec(sra, bzla_bv_sra, 32);

  for (uint32_t i = 0, bw = 2; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      std::bitset<2> bits_i(i);
      ss_expected << std::string(j, bits_i[bw - 1] == 1 ? '1' : '0')
                  << bits_i.to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<2>(i).to_string().c_str(),
                   std::bitset<2>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sra);
    }
  }

  for (uint32_t i = 0, bw = 3; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      std::bitset<3> bits_i(i);
      ss_expected << std::string(j, bits_i[bw - 1] == 1 ? '1' : '0')
                  << bits_i.to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<3>(i).to_string().c_str(),
                   std::bitset<3>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sra);
    }
  }

  for (uint32_t i = 0, bw = 8; i < (1u << bw); ++i)
  {
    for (uint32_t j = 0; j < (1u << bw); ++j)
    {
      std::stringstream ss_expected;
      std::bitset<8> bits_i(i);
      ss_expected << std::string(j, bits_i[bw - 1] == 1 ? '1' : '0')
                  << bits_i.to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<8>(i).to_string().c_str(),
                   std::bitset<8>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sra);
    }
  }

  for (uint32_t i = 0, bw = 65; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      std::bitset<65> bits_i(i);
      ss_expected << std::string(j, bits_i[bw - 1] == 1 ? '1' : '0')
                  << bits_i.to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sra);
    }
    /* shift value doesn't fit into uint64_t */
    {
      shift_bitvec(std::bitset<65>(i).to_string().c_str(),
                   std::bitset<65>(0u).set(64, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_sra);
    }
  }

  for (uint32_t i = 0, bw = 128; i < (1u << bw); ++i)
  {
    /* shift value fits into uint64_t */
    for (uint64_t j = 0; j < 32; ++j)
    {
      std::stringstream ss_expected;
      std::bitset<128> bits_i(i);
      ss_expected << std::string(j, bits_i[bw - 1] == 1 ? '1' : '0')
                  << bits_i.to_string();
      std::string expected = ss_expected.str();
      expected             = expected.substr(0, bw);
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(j).to_string().c_str(),
                   expected.c_str(),
                   bzla_bv_sra);
    }
    /* shift value doesn't fit into uint64_t */
    {
      shift_bitvec(std::bitset<128>(i).to_string().c_str(),
                   std::bitset<128>(0u).set(120, 1).to_string().c_str(),
                   std::string(bw, '0').c_str(),
                   bzla_bv_sra);
    }
  }
}

TEST_F(TestBv, mul)
{
  binary_bitvec(mul, bzla_bv_mul, 1);
  binary_bitvec(mul, bzla_bv_mul, 7);
  binary_bitvec(mul, bzla_bv_mul, 31);
  binary_bitvec(mul, bzla_bv_mul, 33);
}

TEST_F(TestBv, udiv)
{
  binary_bitvec(udiv, bzla_bv_udiv, 1);
  binary_bitvec(udiv, bzla_bv_udiv, 7);
  binary_bitvec(udiv, bzla_bv_udiv, 31);
  binary_bitvec(udiv, bzla_bv_udiv, 33);
}

TEST_F(TestBv, urem)
{
  binary_bitvec(urem, bzla_bv_urem, 1);
  binary_bitvec(urem, bzla_bv_urem, 7);
  binary_bitvec(urem, bzla_bv_urem, 31);
  binary_bitvec(urem, bzla_bv_urem, 33);
}

TEST_F(TestBv, udiv_urem)
{
  udiv_urem_bitvec(1);
  udiv_urem_bitvec(7);
  udiv_urem_bitvec(31);
  udiv_urem_bitvec(33);
}

TEST_F(TestBv, sdiv)
{
  binary_signed_bitvec(sdiv, bzla_bv_sdiv, 1);
  binary_signed_bitvec(sdiv, bzla_bv_sdiv, 7);
  binary_signed_bitvec(sdiv, bzla_bv_sdiv, 31);
  binary_signed_bitvec(sdiv, bzla_bv_sdiv, 33);
}

TEST_F(TestBv, srem)
{
  binary_signed_bitvec(srem, bzla_bv_srem, 1);
  binary_signed_bitvec(srem, bzla_bv_srem, 7);
  binary_signed_bitvec(srem, bzla_bv_srem, 31);
  binary_signed_bitvec(srem, bzla_bv_srem, 33);
}

TEST_F(TestBv, concat)
{
  concat_bitvec(2);
  concat_bitvec(7);
  concat_bitvec(31);
  concat_bitvec(33);
  concat_bitvec(64);
}

TEST_F(TestBv, slice)
{
  slice_bitvec(1);
  slice_bitvec(7);
  slice_bitvec(31);
  slice_bitvec(33);
  slice_bitvec(64);
}

TEST_F(TestBv, uext)
{
  ext_bitvec(bzla_bv_uext, 2);
  ext_bitvec(bzla_bv_uext, 3);
  ext_bitvec(bzla_bv_uext, 4);
  ext_bitvec(bzla_bv_uext, 5);
  ext_bitvec(bzla_bv_uext, 6);
  ext_bitvec(bzla_bv_uext, 7);
  ext_bitvec(bzla_bv_uext, 31);
  ext_bitvec(bzla_bv_uext, 33);
  ext_bitvec(bzla_bv_uext, 64);
}

TEST_F(TestBv, sext)
{
  ext_bitvec(bzla_bv_sext, 2);
  ext_bitvec(bzla_bv_sext, 3);
  ext_bitvec(bzla_bv_sext, 4);
  ext_bitvec(bzla_bv_sext, 5);
  ext_bitvec(bzla_bv_sext, 6);
  ext_bitvec(bzla_bv_sext, 7);
  ext_bitvec(bzla_bv_sext, 31);
  ext_bitvec(bzla_bv_sext, 33);
  ext_bitvec(bzla_bv_sext, 64);
}

TEST_F(TestBv, ite)
{
  ite_bitvec(1);
  ite_bitvec(7);
  ite_bitvec(31);
  ite_bitvec(33);
  ite_bitvec(64);
}

TEST_F(TestBv, mod_inverse)
{
  mod_inverse_bitvec(1);
  mod_inverse_bitvec(7);
  mod_inverse_bitvec(31);
  mod_inverse_bitvec(33);
  mod_inverse_bitvec(64);
}

TEST_F(TestBv, flipped_bit)
{
  flipped_bit_bitvec(1);
  flipped_bit_bitvec(7);
  flipped_bit_bitvec(31);
  flipped_bit_bitvec(33);
  flipped_bit_bitvec(64);
}

TEST_F(TestBv, flipped_bit_range)
{
  flipped_bit_range_bitvec(1);
  flipped_bit_range_bitvec(7);
  flipped_bit_range_bitvec(31);
  flipped_bit_range_bitvec(33);
  flipped_bit_range_bitvec(64);
}

TEST_F(TestBv, is_uaddo)
{
  is_uaddo_bitvec(1);
  is_uaddo_bitvec(7);
  is_uaddo_bitvec(31);
  is_uaddo_bitvec(33);
}

TEST_F(TestBv, is_umulo)
{
  is_umulo_bitvec(1);
  is_umulo_bitvec(7);
  is_umulo_bitvec(31);
  is_umulo_bitvec(33);
}

TEST_F(TestBv, compare)
{
  int32_t i, j, k;
  BzlaBitVector *bv1, *bv2;

  for (i = 0; i < 15; i++)
  {
    bv1 = bzla_bv_uint64_to_bv(d_mm, i, 4);
    bv2 = bzla_bv_uint64_to_bv(d_mm, i, 4);
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }

  for (i = 0; i < 15 - 1; i++)
  {
    bv1 = bzla_bv_uint64_to_bv(d_mm, i, 4);
    bv2 = bzla_bv_uint64_to_bv(d_mm, i + 1, 4);
    ASSERT_LT(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_GT(bzla_bv_compare(bv2, bv1), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }

  for (i = 0, j = 0, k = 0; i < 15; i++)
  {
    k = rand() % 16;
    do
    {
      j = rand() % 16;
    } while (j == k);
    bv1 = bzla_bv_uint64_to_bv(d_mm, j, 4);
    bv2 = bzla_bv_uint64_to_bv(d_mm, k, 4);
    if (j > k)
    {
      ASSERT_GT(bzla_bv_compare(bv1, bv2), 0);
      ASSERT_LT(bzla_bv_compare(bv2, bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bzla_bv_compare(bv1, bv2), 0);
      ASSERT_GT(bzla_bv_compare(bv2, bv1), 0);
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }
}

TEST_F(TestBv, signed_compare)
{
  int32_t i, j, k;
  BzlaBitVector *bv1, *bv2;

  for (i = -8; i < 7; i++)
  {
    bv1 = bzla_bv_int64_to_bv(d_mm, i, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, i, 4);
    ASSERT_EQ(bzla_bv_signed_compare(bv1, bv2), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }

  for (i = -8; i < 7 - 1; i++)
  {
    bv1 = bzla_bv_int64_to_bv(d_mm, i, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, i + 1, 4);
    ASSERT_LT(bzla_bv_signed_compare(bv1, bv2), 0);
    ASSERT_GT(bzla_bv_signed_compare(bv2, bv1), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }

  for (i = 0, j = 0, k = 0; i < 15; i++)
  {
    /* j <= 0, k <= 0 */
    k = rand() % 9;
    do
    {
      j = rand() % 9;
    } while (j == k);
    j   = -j;
    k   = -k;
    bv1 = bzla_bv_int64_to_bv(d_mm, j, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, k, 4);
    if (j > k)
    {
      ASSERT_GT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_LT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_GT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);

    /* j <= 0, k >= 0 */
    k = rand() % 8;
    do
    {
      j = rand() % 9;
    } while (j == k);
    j   = -j;
    bv1 = bzla_bv_int64_to_bv(d_mm, j, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, k, 4);
    if (j > k)
    {
      ASSERT_GT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_LT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_GT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);

    /* j >= 0, k <= 0 */
    k = rand() % 9;
    do
    {
      j = rand() % 8;
    } while (j == k);
    k   = -k;
    bv1 = bzla_bv_int64_to_bv(d_mm, j, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, k, 4);
    if (j > k)
    {
      ASSERT_GT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_LT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_GT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);

    /* j >= 0, k >= 0 */
    k = rand() % 8;
    do
    {
      j = rand() % 8;
    } while (j == k);
    bv1 = bzla_bv_int64_to_bv(d_mm, -j, 4);
    bv2 = bzla_bv_int64_to_bv(d_mm, -k, 4);
    if (-j > -k)
    {
      ASSERT_GT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_LT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    if (-j < -k)
    {
      ASSERT_LT(bzla_bv_signed_compare(bv1, bv2), 0);
      ASSERT_GT(bzla_bv_signed_compare(bv2, bv1), 0);
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }
}

TEST_F(TestBv, is_true)
{
  int32_t i;
  BzlaBitVector *bv1, *bv2;

  for (i = 1; i < 32; i++)
  {
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_uint64_to_bv(
        d_mm, bzla_rng_pick_rand(d_rng, 1, (1 << i) - 1), i);
    if (i > 1)
    {
      assert(!bzla_bv_is_true(bv1));
      assert(!bzla_bv_is_true(bv2));
    }
    else
    {
      assert(bzla_bv_is_true(bv1));
      assert(bzla_bv_is_true(bv2));
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }
}

TEST_F(TestBv, is_false)
{
  int32_t i;
  BzlaBitVector *bv1, *bv2;

  for (i = 1; i < 32; i++)
  {
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_uint64_to_bv(
        d_mm, bzla_rng_pick_rand(d_rng, 1, (1 << i) - 1), i);
    if (i > 1)
    {
      assert(!bzla_bv_is_false(bv1));
      assert(!bzla_bv_is_false(bv2));
    }
    else
    {
      assert(bzla_bv_is_false(bv1));
      assert(!bzla_bv_is_false(bv2));
    }
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
  }
}

TEST_F(TestBv, is_one)
{
  BzlaBitVector *bv1, *bv2, *bv3;

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 1, i - 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_TRUE(bzla_bv_is_one(bv1));
    ASSERT_TRUE(bzla_bv_is_one(bv2));
    ASSERT_TRUE(bzla_bv_is_one(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 0, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_one(bv1));
    ASSERT_FALSE(bzla_bv_is_one(bv2));
    ASSERT_FALSE(bzla_bv_is_one(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '1');
    bv1 = bzla_bv_ones(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_one(bv1));
    ASSERT_FALSE(bzla_bv_is_one(bv2));
    ASSERT_FALSE(bzla_bv_is_one(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    bv1 = bzla_bv_min_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1), i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l =
          bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1 - 64), i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_one(bv1));
    ASSERT_FALSE(bzla_bv_is_one(bv2));
    ASSERT_FALSE(bzla_bv_is_one(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 3; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    bv1 = bzla_bv_max_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, (((uint64_t) 1) << (i - 1)) - 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(
          d_mm, (((uint64_t) 1) << (i - 1 - 64)) - 1, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_one(bv1));
    ASSERT_FALSE(bzla_bv_is_one(bv2));
    ASSERT_FALSE(bzla_bv_is_one(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, is_ones)
{
  BzlaBitVector *bv1, *bv2, *bv3;

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    bv1 = bzla_bv_ones(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_TRUE(bzla_bv_is_ones(bv1));
    ASSERT_TRUE(bzla_bv_is_ones(bv2));
    ASSERT_TRUE(bzla_bv_is_ones(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 0, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_ones(bv1));
    ASSERT_FALSE(bzla_bv_is_ones(bv2));
    ASSERT_FALSE(bzla_bv_is_ones(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    bv1 = bzla_bv_min_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1), i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l =
          bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1 - 64), i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_ones(bv1));
    ASSERT_FALSE(bzla_bv_is_ones(bv2));
    ASSERT_FALSE(bzla_bv_is_ones(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    bv1 = bzla_bv_max_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, (((uint64_t) 1) << (i - 1)) - 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(
          d_mm, (((uint64_t) 1) << (i - 1 - 64)) - 1, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_ones(bv1));
    ASSERT_FALSE(bzla_bv_is_ones(bv2));
    ASSERT_FALSE(bzla_bv_is_ones(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 1, i - 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_ones(bv1));
    ASSERT_FALSE(bzla_bv_is_ones(bv2));
    ASSERT_FALSE(bzla_bv_is_ones(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, is_zero)
{
  BzlaBitVector *bv1, *bv2, *bv3;

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 0, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_TRUE(bzla_bv_is_zero(bv1));
    ASSERT_TRUE(bzla_bv_is_zero(bv2));
    ASSERT_TRUE(bzla_bv_is_zero(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 1, i - 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_zero(bv1));
    ASSERT_FALSE(bzla_bv_is_zero(bv2));
    ASSERT_FALSE(bzla_bv_is_zero(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    bv1 = bzla_bv_ones(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_zero(bv1));
    ASSERT_FALSE(bzla_bv_is_zero(bv2));
    ASSERT_FALSE(bzla_bv_is_zero(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    bv1 = bzla_bv_min_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1), i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l =
          bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1 - 64), i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_zero(bv1));
    ASSERT_FALSE(bzla_bv_is_zero(bv2));
    ASSERT_FALSE(bzla_bv_is_zero(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    bv1 = bzla_bv_max_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, (((uint64_t) 1) << (i - 1)) - 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(
          d_mm, (((uint64_t) 1) << (i - 1 - 64)) - 1, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_zero(bv1));
    ASSERT_FALSE(bzla_bv_is_zero(bv2));
    ASSERT_FALSE(bzla_bv_is_zero(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, is_max_signed)
{
  BzlaBitVector *bv1, *bv2, *bv3;

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    bv1 = bzla_bv_max_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, (((uint64_t) 1) << (i - 1)) - 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(
          d_mm, (((uint64_t) 1) << (i - 1 - 64)) - 1, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_TRUE(bzla_bv_is_max_signed(bv1));
    ASSERT_TRUE(bzla_bv_is_max_signed(bv2));
    ASSERT_TRUE(bzla_bv_is_max_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '0');
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 0, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_max_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 3; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 1, i - 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_max_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '1');
    bv1 = bzla_bv_ones(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_max_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    bv1 = bzla_bv_min_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1), i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l =
          bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1 - 64), i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_max_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_max_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, is_min_signed)
{
  BzlaBitVector *bv1, *bv2, *bv3;

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "1" << std::string(i - 1, '0');
    bv1 = bzla_bv_min_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1), i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l =
          bzla_bv_uint64_to_bv(d_mm, ((uint64_t) 1) << (i - 1 - 64), i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_TRUE(bzla_bv_is_min_signed(bv1));
    ASSERT_TRUE(bzla_bv_is_min_signed(bv2));
    ASSERT_TRUE(bzla_bv_is_min_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::string s(i, '0');
    bv1 = bzla_bv_zero(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 0, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 0, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_min_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::stringstream ss;
    ss << std::string(i - 1, '0') << "1";
    bv1 = bzla_bv_one(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, 1, i - 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, 0, 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_min_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 2; i <= 128; i++)
  {
    std::string s(i, '1');
    bv1 = bzla_bv_ones(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, s.c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_min_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }

  for (uint32_t i = 1; i <= 128; i++)
  {
    std::stringstream ss;
    ss << "0" << std::string(i - 1, '1');
    bv1 = bzla_bv_max_signed(d_mm, i);
    bv2 = bzla_bv_char_to_bv(d_mm, ss.str().c_str());
    if (i <= 64)
    {
      bv3 = bzla_bv_uint64_to_bv(d_mm, (((uint64_t) 1) << (i - 1)) - 1, i);
    }
    else
    {
      BzlaBitVector *r = bzla_bv_uint64_to_bv(d_mm, UINT64_MAX, 64);
      BzlaBitVector *l = bzla_bv_uint64_to_bv(
          d_mm, (((uint64_t) 1) << (i - 1 - 64)) - 1, i - 64);

      bv3 = bzla_bv_concat(d_mm, l, r);
      bzla_bv_free(d_mm, l);
      bzla_bv_free(d_mm, r);
    }
    ASSERT_FALSE(bzla_bv_is_min_signed(bv1));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv2));
    ASSERT_FALSE(bzla_bv_is_min_signed(bv3));
    ASSERT_EQ(bzla_bv_compare(bv1, bv2), 0);
    ASSERT_EQ(bzla_bv_compare(bv1, bv3), 0);
    bzla_bv_free(d_mm, bv1);
    bzla_bv_free(d_mm, bv2);
    bzla_bv_free(d_mm, bv3);
  }
}

TEST_F(TestBv, is_special_const)
{
  int32_t i;
  BzlaBitVector *bv;

  bv = bzla_bv_char_to_bv(d_mm, "0");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ZERO);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONE_ONES);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ZERO);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "01");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONE);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_MIN_SIGNED);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONES);
  bzla_bv_free(d_mm, bv);

  for (i = 0; i <= 7; i++)
  {
    bv = bzla_bv_uint64_to_bv(d_mm, i, 3);
    if (i == 0)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ZERO);
    }
    else if (i == 1)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONE);
    }
    else if (i == 4)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_MIN_SIGNED);
    }
    else if (i == 3)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_MAX_SIGNED);
    }
    else if (i == 7)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONES);
    }
    else
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_NONE);
    }
    bzla_bv_free(d_mm, bv);
  }

  for (i = 0; i <= 15; i++)
  {
    bv = bzla_bv_uint64_to_bv(d_mm, i, 4);
    if (i == 0)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ZERO);
    }
    else if (i == 1)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONE);
    }
    else if (i == 8)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_MIN_SIGNED);
    }
    else if (i == 7)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_MAX_SIGNED);
    }
    else if (i == 15)
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONES);
    }
    else
    {
      ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_NONE);
    }
    bzla_bv_free(d_mm, bv);
  }

  bv = bzla_bv_char_to_bv(d_mm, "1111");
  ASSERT_EQ(bzla_bv_is_special_const(bv), BZLA_SPECIAL_CONST_BV_ONES);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, power_of_two)
{
  BzlaBitVector *bv;

  bv = bzla_bv_char_to_bv(
      d_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "001");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00100");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "001000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 5);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 6);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00010000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 7);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 8);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 9);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000010000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 10);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 28);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "100000000000000000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 29);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 30);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "01000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), 30);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "1110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "11110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "1111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "1111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "11111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "111111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "1111111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);

  bzla_bv_free(d_mm, bv);
  bv = bzla_bv_char_to_bv(d_mm, "1111111111111110");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "011");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0011");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00101");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "101101");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010001");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100111");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1001000001");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11010000001");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000011");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000111");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000010000001111");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000010");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "100000000000000000000001000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1000000000000100000000000000000");
  ASSERT_EQ(bzla_bv_power_of_two(bv), -1);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, small_positive_int)
{
  BzlaBitVector *bv;

  bv = bzla_bv_char_to_bv(
      d_mm, "0000000000000000000000000000000000000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "001");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 2);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00100");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 4);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "001000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 8);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 16);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 32);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 64);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00010000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 128);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 256);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 512);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000010000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1024);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), (1 << 28));
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "100000000000000000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), (1 << 29));
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), (1 << 30));
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "01000000000000000000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), (1 << 30));
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 6);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 14);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 30);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 62);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 126);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 510);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1022);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 2046);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 4094);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1111111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 8190);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1111111111111110");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 65534);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "011");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "111");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 7);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0011");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 3);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00101");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 5);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "101101");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 45);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "00100001");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 33);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100111");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 39);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1001000001");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 577);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "11010000001");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1665);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "000100000011");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 259);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0001000000111");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 519);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0000010000001111");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1039);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000010");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 268435458);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "100000000000000000000001000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 536870976);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "1000000000000100000000000000000");
  ASSERT_EQ(bzla_bv_small_positive_int(bv), 1073872896);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000000000000000000000000000000");
  ASSERT_LT(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "10000100000000000000000011100000");
  ASSERT_LT(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010000000000000000000000000000000");
  ASSERT_LT(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);

  bv = bzla_bv_char_to_bv(d_mm, "0010000000000100000000000011110000");
  ASSERT_LT(bzla_bv_small_positive_int(bv), 0);
  bzla_bv_free(d_mm, bv);
}

TEST_F(TestBv, get_num_trailing_zeros)
{
  test_get_num(8, bzla_bv_get_num_trailing_zeros, false);
  test_get_num(64, bzla_bv_get_num_trailing_zeros, false);
  test_get_num(76, bzla_bv_get_num_trailing_zeros, false);
  test_get_num(128, bzla_bv_get_num_trailing_zeros, false);
  test_get_num(176, bzla_bv_get_num_trailing_zeros, false);
}

TEST_F(TestBv, get_num_leading_zeros)
{
  test_get_num(8, bzla_bv_get_num_leading_zeros);
  test_get_num(64, bzla_bv_get_num_leading_zeros);
  test_get_num(76, bzla_bv_get_num_leading_zeros);
  test_get_num(128, bzla_bv_get_num_leading_zeros);
  test_get_num(176, bzla_bv_get_num_leading_zeros);
}

TEST_F(TestBv, test_get_num_leading_ones)
{
  test_get_num(8, bzla_bv_get_num_leading_ones, true, false);
  test_get_num(64, bzla_bv_get_num_leading_ones, true, false);
  test_get_num(76, bzla_bv_get_num_leading_ones, true, false);
  test_get_num(128, bzla_bv_get_num_leading_ones, true, false);
  test_get_num(176, bzla_bv_get_num_leading_ones, true, false);
}

// TODO bzla_bv_get_assignment
