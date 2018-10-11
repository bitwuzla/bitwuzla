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

#define BZLA_TEST_RED_LOGIC_XOR(a, b) (((a) || (b)) && !((a) && (b)))

class TestLogic : public TestBoolector
{
 protected:
  static constexpr uint32_t BZLA_TEST_LOGIC_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_LOGIC_HIGH = 4;

  static constexpr uint32_t BZLA_TEST_RED_LOGIC_LOW  = 2;
  static constexpr uint32_t BZLA_TEST_RED_LOGIC_HIGH = 4;

  void not_logic_test(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    uint32_t i       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        BoolectorSort sort;
        BoolectorNode *const1, *const2, *eq, *inv;

        if (d_bzla) boolector_delete(d_bzla);
        d_bzla = boolector_new();

        boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

        result = ~i & (max - 1);

        sort   = boolector_bv_sort(d_bzla, num_bits);
        const1 = boolector_unsigned_int(d_bzla, i, sort);
        const2 = boolector_unsigned_int(d_bzla, result, sort);
        inv    = boolector_bv_not(d_bzla, const1);
        eq     = boolector_eq(d_bzla, inv, const2);
        boolector_assert(d_bzla, eq);

        ASSERT_EQ(boolector_sat(d_bzla), BOOLECTOR_SAT);
        boolector_release(d_bzla, inv);
        boolector_release(d_bzla, eq);
        boolector_release(d_bzla, const1);
        boolector_release(d_bzla, const2);
        boolector_release_sort(d_bzla, sort);
        boolector_delete(d_bzla);
        d_bzla = nullptr;
      }
    }
  }

  void binary_logic_test(uint32_t (*func)(uint32_t, uint32_t),
                         BoolectorNode *(*bzla_fun)(Bzla *,
                                                    BoolectorNode *,
                                                    BoolectorNode *),
                         int32_t low,
                         int32_t high,
                         uint32_t rwl)
  {
    assert(func != NULL);
    assert(low > 0);
    assert(low <= high);

    uint32_t i       = 0;
    uint32_t j       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        for (j = 0; j < (uint32_t) max; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *const3, *eq, *bfun;

          if (d_bzla) boolector_delete(d_bzla);
          d_bzla = boolector_new();
          boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          result = func(i, j);

          sort   = boolector_bv_sort(d_bzla, num_bits);
          const1 = boolector_unsigned_int(d_bzla, i, sort);
          const2 = boolector_unsigned_int(d_bzla, j, sort);
          bfun   = bzla_fun(d_bzla, const1, const2);
          const3 = boolector_unsigned_int(d_bzla, result, sort);
          eq     = boolector_eq(d_bzla, bfun, const3);
          boolector_assert(d_bzla, eq);

          ASSERT_EQ(boolector_sat(d_bzla), BOOLECTOR_SAT);
          boolector_release(d_bzla, eq);
          boolector_release(d_bzla, const1);
          boolector_release(d_bzla, const2);
          boolector_release(d_bzla, const3);
          boolector_release(d_bzla, bfun);
          boolector_release_sort(d_bzla, sort);
          boolector_delete(d_bzla);
          d_bzla = nullptr;
        }
      }
    }
  }

  void xnor_logic_test(int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    uint32_t i       = 0;
    uint32_t j       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        for (j = 0; j < (uint32_t) max; j++)
        {
          for (j = 0; j < (uint32_t) max; j++)
          {
            BoolectorSort sort;
            BoolectorNode *const1, *const2, *const3, *eq, *xnor;

            if (d_bzla) boolector_delete(d_bzla);
            d_bzla = boolector_new();
            boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

            result = ~(i ^ j) & (max - 1);

            sort   = boolector_bv_sort(d_bzla, num_bits);
            const1 = boolector_unsigned_int(d_bzla, i, sort);
            const2 = boolector_unsigned_int(d_bzla, j, sort);
            xnor   = boolector_xnor(d_bzla, const1, const2);
            const3 = boolector_unsigned_int(d_bzla, result, sort);
            eq     = boolector_eq(d_bzla, xnor, const3);
            boolector_assert(d_bzla, eq);

            ASSERT_EQ(boolector_sat(d_bzla), BOOLECTOR_SAT);
            boolector_release(d_bzla, eq);
            boolector_release(d_bzla, const1);
            boolector_release(d_bzla, const2);
            boolector_release(d_bzla, const3);
            boolector_release(d_bzla, xnor);
            boolector_release_sort(d_bzla, sort);
            boolector_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }

  void red_logic_test(uint32_t (*func)(uint32_t, uint32_t),
                      BoolectorNode *(*bzla_fun)(Bzla *, BoolectorNode *),
                      int32_t low,
                      int32_t high,
                      uint32_t rwl)
  {
    assert(func != NULL);
    assert(low > 0);
    assert(low <= high);

    int32_t sat_res;
    uint32_t i       = 0;
    uint32_t result  = 0;
    int32_t num_bits = 0;
    int32_t max      = 0;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < (uint32_t) max; i++)
      {
        BoolectorSort sort;
        BoolectorNode *const1, *bfun;

        if (d_bzla) boolector_delete(d_bzla);
        d_bzla = boolector_new();
        boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

        result = func(i, (uint32_t) num_bits);

        sort   = boolector_bv_sort(d_bzla, num_bits);
        const1 = boolector_unsigned_int(d_bzla, i, sort);
        bfun   = bzla_fun(d_bzla, const1);
        boolector_assert(d_bzla, bfun);

        sat_res = boolector_sat(d_bzla);
        ASSERT_TRUE((result && sat_res == BOOLECTOR_SAT)
                    || (!result && sat_res == BOOLECTOR_UNSAT));
        boolector_release(d_bzla, const1);
        boolector_release(d_bzla, bfun);
        boolector_release_sort(d_bzla, sort);
        boolector_delete(d_bzla);
        d_bzla = nullptr;
      }
    }
  }

  static uint32_t _and(uint32_t x, uint32_t y) { return x & y; }

  static uint32_t _or(uint32_t x, uint32_t y) { return x | y; }

  static uint32_t _xor(uint32_t x, uint32_t y) { return x ^ y; }

  static uint32_t redand(uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 1;
    uint32_t i      = 0;
    assert(num_bits > 1);
    assert(num_bits <= 32);
    for (i = 0; result && i < num_bits; i++) result = result && (x & (1 << i));
    return result;
  }

  static uint32_t redor(uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 0;
    uint32_t i      = 0;
    assert(num_bits > 1);
    assert(num_bits <= 32);
    for (i = 0; !result && i < num_bits; i++) result = result || (x & (1 << i));
    return result;
  }

  static uint32_t redxor(uint32_t x, uint32_t num_bits)
  {
    uint32_t result = 0;
    uint32_t i      = 0;
    assert(num_bits > 1);
    assert(num_bits <= 32);
    result = BZLA_TEST_RED_LOGIC_XOR(x & 1, x & 2);
    for (i = 2; i < num_bits; i++)
      result = BZLA_TEST_RED_LOGIC_XOR(result, x & (1 << i));
    return result;
  }
};

TEST_F(TestLogic, not )
{
  not_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  not_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, and)
{
  binary_logic_test(
      _and, boolector_and, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _and, boolector_and, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, or)
{
  binary_logic_test(
      _or, boolector_or, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _or, boolector_or, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, xor)
{
  binary_logic_test(
      _xor, boolector_xor, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _xor, boolector_xor, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, xnor)
{
  xnor_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  xnor_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, redand)
{
  red_logic_test(redand,
                 boolector_redand,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redand,
                 boolector_redand,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}

TEST_F(TestLogic, redor)
{
  red_logic_test(redor,
                 boolector_bv_redor,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redor,
                 boolector_bv_redor,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}

TEST_F(TestLogic, redxor)
{
  red_logic_test(redxor,
                 boolector_bv_redxor,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redxor,
                 boolector_bv_redxor,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}
