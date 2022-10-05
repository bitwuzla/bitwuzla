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

#define BZLA_TEST_RED_LOGIC_XOR(a, b) (((a) || (b)) && !((a) && (b)))

class TestLogic : public TestBitwuzla
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
        if (d_bzla) bitwuzla_delete(d_bzla);
        d_bzla = bitwuzla_new();

        bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

        result = ~i & (max - 1);

        const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
        const BitwuzlaTerm *const1 =
            bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
        const BitwuzlaTerm *const2 =
            bitwuzla_mk_bv_value_uint64(d_bzla, sort, result);
        const BitwuzlaTerm *inv =
            bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, const1);
        const BitwuzlaTerm *eq =
            bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, inv, const2);
        bitwuzla_assert(d_bzla, eq);

        ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
        bitwuzla_delete(d_bzla);
        d_bzla = nullptr;
      }
    }
  }

  void binary_logic_test(uint32_t (*func)(uint32_t, uint32_t),
                         BitwuzlaKind kind,
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
          if (d_bzla) bitwuzla_delete(d_bzla);
          d_bzla = bitwuzla_new();
          bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

          result = func(i, j);

          const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
          const BitwuzlaTerm *const1 =
              bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
          const BitwuzlaTerm *const2 =
              bitwuzla_mk_bv_value_uint64(d_bzla, sort, j);
          const BitwuzlaTerm *bfun =
              bitwuzla_mk_term2(d_bzla, kind, const1, const2);
          const BitwuzlaTerm *const3 =
              bitwuzla_mk_bv_value_uint64(d_bzla, sort, result);
          const BitwuzlaTerm *eq =
              bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, bfun, const3);
          bitwuzla_assert(d_bzla, eq);

          ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
          bitwuzla_delete(d_bzla);
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
            if (d_bzla) bitwuzla_delete(d_bzla);
            d_bzla = bitwuzla_new();
            bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

            result = ~(i ^ j) & (max - 1);

            const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
            const BitwuzlaTerm *const1 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
            const BitwuzlaTerm *const2 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, j);
            const BitwuzlaTerm *xnor = bitwuzla_mk_term2(
                d_bzla, BITWUZLA_KIND_BV_XNOR, const1, const2);
            const BitwuzlaTerm *const3 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, result);
            const BitwuzlaTerm *eq =
                bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, xnor, const3);
            bitwuzla_assert(d_bzla, eq);

            ASSERT_EQ(bitwuzla_check_sat(d_bzla), BITWUZLA_SAT);
            bitwuzla_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }

  void red_logic_test(uint32_t (*func)(uint32_t, uint32_t),
                      BitwuzlaKind kind,
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
        if (d_bzla) bitwuzla_delete(d_bzla);
        d_bzla = bitwuzla_new();
        bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

        result = func(i, (uint32_t) num_bits);

        const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
        const BitwuzlaTerm *const1 =
            bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
        const BitwuzlaTerm *bfun = bitwuzla_mk_term1(d_bzla, kind, const1);
        bitwuzla_assert(d_bzla, bfun);

        sat_res = bitwuzla_check_sat(d_bzla);
        ASSERT_TRUE((result && sat_res == BITWUZLA_SAT)
                    || (!result && sat_res == BITWUZLA_UNSAT));
        bitwuzla_delete(d_bzla);
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
      _and, BITWUZLA_KIND_BV_AND, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _and, BITWUZLA_KIND_BV_AND, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, or)
{
  binary_logic_test(
      _or, BITWUZLA_KIND_BV_OR, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _or, BITWUZLA_KIND_BV_OR, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, xor)
{
  binary_logic_test(
      _xor, BITWUZLA_KIND_BV_XOR, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  binary_logic_test(
      _xor, BITWUZLA_KIND_BV_XOR, BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, xnor)
{
  xnor_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 1);
  xnor_logic_test(BZLA_TEST_LOGIC_LOW, BZLA_TEST_LOGIC_HIGH, 0);
}

TEST_F(TestLogic, redand)
{
  red_logic_test(redand,
                 BITWUZLA_KIND_BV_REDAND,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redand,
                 BITWUZLA_KIND_BV_REDAND,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}

TEST_F(TestLogic, redor)
{
  red_logic_test(redor,
                 BITWUZLA_KIND_BV_REDOR,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redor,
                 BITWUZLA_KIND_BV_REDOR,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}

TEST_F(TestLogic, redxor)
{
  red_logic_test(redxor,
                 BITWUZLA_KIND_BV_REDXOR,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 1);
  red_logic_test(redxor,
                 BITWUZLA_KIND_BV_REDXOR,
                 BZLA_TEST_RED_LOGIC_LOW,
                 BZLA_TEST_RED_LOGIC_HIGH,
                 0);
}
