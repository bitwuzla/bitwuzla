/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlautil.h"
}

class TestArith : public TestBitwuzla
{
 protected:
  static constexpr uint32_t BZLA_TEST_ARITHMETIC_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_ARITHMETIC_HIGH = 4;

  void u_arithmetic_test(int32_t (*func)(int32_t, int32_t),
                         BitwuzlaKind kind,
                         int32_t low,
                         int32_t high,
                         uint32_t rwl)
  {
    assert(func != NULL);
    assert(low > 0);
    assert(low <= high);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t result   = 0;
    int32_t max      = 0;
    int32_t num_bits = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          result = func(i, j);

          if (result < max)
          {
            if (d_bzla) bitwuzla_delete(d_bzla);
            d_bzla = bitwuzla_new();
            bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

            const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);

            const BitwuzlaTerm *const1, *const2, *const3, *bfun, *eq;
            const1 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
            const2 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, j);
            bfun   = bitwuzla_mk_term2(d_bzla, kind, const1, const2);
            const3 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, result);
            eq = bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, bfun, const3);

            bitwuzla_assert(d_bzla, eq);

            ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
            bitwuzla_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }

  void s_arithmetic_test(int32_t (*func)(int32_t, int32_t),
                         BitwuzlaKind kind,
                         int32_t low,
                         int32_t high,
                         uint32_t rwl)
  {
    assert(func != NULL);
    assert(low > 0);
    assert(low <= high);

    int32_t i        = 0;
    int32_t j        = 0;
    int32_t result   = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits - 1);
      for (i = -max; i < max; i++)
      {
        for (j = -max; j < max; j++)
        {
          result = func(i, j);

          if (result >= -max && result < max)
          {
            if (d_bzla) bitwuzla_delete(d_bzla);
            d_bzla = bitwuzla_new();
            bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

            const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
            const BitwuzlaTerm *const1, *const2, *const3, *bfun, *eq;

            const1 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) i);
            const2 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) j);

            bfun = bitwuzla_mk_term2(d_bzla, kind, const1, const2);
            const3 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) result);
            eq = bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, bfun, const3);
            bitwuzla_assert(d_bzla, eq);

            ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
            bitwuzla_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }

  static int32_t add(int32_t x, int32_t y) { return x + y; }

  static int32_t sub(int32_t x, int32_t y) { return x - y; }

  static int32_t mul(int32_t x, int32_t y) { return x * y; }

  static int32_t divide(int32_t x, int32_t y)
  {
    if (y == 0)
    {
      if (x < 0) return 1;
      return -1;
    }
    return x / y;
  }

  static int32_t rem(int32_t x, int32_t y)
  {
    if (y == 0) return x;

    return x % y;
  }
};

TEST_F(TestArith, add_u)
{
  u_arithmetic_test(add,
                    BITWUZLA_KIND_BV_ADD,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(add,
                    BITWUZLA_KIND_BV_ADD,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sub_u)
{
  u_arithmetic_test(sub,
                    BITWUZLA_KIND_BV_SUB,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(sub,
                    BITWUZLA_KIND_BV_SUB,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, mul_u)
{
  u_arithmetic_test(mul,
                    BITWUZLA_KIND_BV_MUL,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(mul,
                    BITWUZLA_KIND_BV_MUL,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, udiv_u)
{
  u_arithmetic_test(divide,
                    BITWUZLA_KIND_BV_UDIV,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(divide,
                    BITWUZLA_KIND_BV_UDIV,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, urem_u)
{
  u_arithmetic_test(rem,
                    BITWUZLA_KIND_BV_UREM,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(rem,
                    BITWUZLA_KIND_BV_UREM,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, add_s)
{
  s_arithmetic_test(add,
                    BITWUZLA_KIND_BV_ADD,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(add,
                    BITWUZLA_KIND_BV_ADD,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sub_s)
{
  s_arithmetic_test(sub,
                    BITWUZLA_KIND_BV_SUB,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(sub,
                    BITWUZLA_KIND_BV_SUB,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, mul_s)
{
  s_arithmetic_test(mul,
                    BITWUZLA_KIND_BV_MUL,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(mul,
                    BITWUZLA_KIND_BV_MUL,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sdiv_s)
{
  s_arithmetic_test(divide,
                    BITWUZLA_KIND_BV_SDIV,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(divide,
                    BITWUZLA_KIND_BV_SDIV,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, srem_s)
{
  s_arithmetic_test(rem,
                    BITWUZLA_KIND_BV_SREM,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(rem,
                    BITWUZLA_KIND_BV_SREM,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}
