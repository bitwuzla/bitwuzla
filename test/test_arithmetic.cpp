/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "utils/bzlautil.h"
}

class TestArith : public TestBoolector
{
 protected:
  static constexpr uint32_t BZLA_TEST_ARITHMETIC_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_ARITHMETIC_HIGH = 4;

  void u_arithmetic_test(int32_t (*func)(int32_t, int32_t),
                         BoolectorNode* (*btorfun)(Bzla*,
                                                   BoolectorNode*,
                                                   BoolectorNode*),
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
            if (d_bzla) boolector_delete(d_bzla);
            d_bzla = boolector_new();
            boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

            BoolectorSort sort = boolector_bv_sort(d_bzla, num_bits);
            BoolectorNode *const1, *const2, *const3, *bfun, *eq;

            const1 = boolector_unsigned_int(d_bzla, i, sort);
            const2 = boolector_unsigned_int(d_bzla, j, sort);
            bfun   = btorfun(d_bzla, const1, const2);
            const3 = boolector_unsigned_int(d_bzla, result, sort);
            eq     = boolector_eq(d_bzla, bfun, const3);
            boolector_assert(d_bzla, eq);

            ASSERT_EQ(boolector_sat(d_bzla), BOOLECTOR_SAT);
            boolector_release_sort(d_bzla, sort);
            boolector_release(d_bzla, const1);
            boolector_release(d_bzla, const2);
            boolector_release(d_bzla, const3);
            boolector_release(d_bzla, bfun);
            boolector_release(d_bzla, eq);
            boolector_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }

  void s_arithmetic_test(int32_t (*func)(int32_t, int32_t),
                         BoolectorNode* (*btorfun)(Bzla*,
                                                   BoolectorNode*,
                                                   BoolectorNode*),
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
            if (d_bzla) boolector_delete(d_bzla);
            d_bzla = boolector_new();
            boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

            BoolectorSort sort = boolector_bv_sort(d_bzla, num_bits);
            BoolectorNode *const1, *const2, *const3, *bfun, *eq;

            const1 = boolector_int(d_bzla, i, sort);
            const2 = boolector_int(d_bzla, j, sort);
            bfun   = btorfun(d_bzla, const1, const2);
            const3 = boolector_int(d_bzla, result, sort);
            eq     = boolector_eq(d_bzla, bfun, const3);
            boolector_assert(d_bzla, eq);

            ASSERT_EQ(boolector_sat(d_bzla), BOOLECTOR_SAT);
            boolector_release_sort(d_bzla, sort);
            boolector_release(d_bzla, const1);
            boolector_release(d_bzla, const2);
            boolector_release(d_bzla, const3);
            boolector_release(d_bzla, bfun);
            boolector_release(d_bzla, eq);
            boolector_delete(d_bzla);
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
                    boolector_bv_add,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(add,
                    boolector_bv_add,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sub_u)
{
  u_arithmetic_test(sub,
                    boolector_bv_sub,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(sub,
                    boolector_bv_sub,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, mul_u)
{
  u_arithmetic_test(mul,
                    boolector_bv_mul,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(mul,
                    boolector_bv_mul,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, udiv_u)
{
  u_arithmetic_test(divide,
                    boolector_bv_udiv,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(divide,
                    boolector_bv_udiv,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, urem_u)
{
  u_arithmetic_test(rem,
                    boolector_urem,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  u_arithmetic_test(rem,
                    boolector_urem,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, add_s)
{
  s_arithmetic_test(add,
                    boolector_bv_add,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(add,
                    boolector_bv_add,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sub_s)
{
  s_arithmetic_test(sub,
                    boolector_bv_sub,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(sub,
                    boolector_bv_sub,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, mul_s)
{
  s_arithmetic_test(mul,
                    boolector_bv_mul,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(mul,
                    boolector_bv_mul,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, sdiv_s)
{
  s_arithmetic_test(divide,
                    boolector_bv_sdiv,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(divide,
                    boolector_bv_sdiv,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}

TEST_F(TestArith, srem_s)
{
  s_arithmetic_test(rem,
                    boolector_srem,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    1);
  s_arithmetic_test(rem,
                    boolector_srem,
                    BZLA_TEST_ARITHMETIC_LOW,
                    BZLA_TEST_ARITHMETIC_HIGH,
                    0);
}
