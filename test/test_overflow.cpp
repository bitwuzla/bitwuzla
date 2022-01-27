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
#include "bzlaaig.h"
#include "dumper/bzladumpaig.h"
#include "utils/bzlautil.h"
}

class TestOverflow : public TestBitwuzla
{
 protected:
  static constexpr uint32_t BZLA_TEST_OVERFLOW_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_OVERFLOW_HIGH = 4;

  int32_t add(int32_t x, int32_t y) { return x + y; }

  int32_t sub(int32_t x, int32_t y) { return x - y; }

  int32_t mul(int32_t x, int32_t y) { return x * y; }

  int32_t div(int32_t x, int32_t y)
  {
    assert(y != 0);
    return x / y;
  }

  void u_overflow_test(BitwuzlaKind kind,
                       int32_t low,
                       int32_t high,
                       uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    int32_t i, j, num_bits, max, result;
    bool overflow_test, overflow_bzla;
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          if (d_bzla) bitwuzla_delete(d_bzla);
          d_bzla = bitwuzla_new();

          bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

          overflow_test = false;
          overflow_bzla = false;

          switch (kind)
          {
            case BITWUZLA_KIND_BV_UADD_OVERFLOW:
            case BITWUZLA_KIND_BV_SADD_OVERFLOW: result = add(i, j); break;
            case BITWUZLA_KIND_BV_USUB_OVERFLOW:
            case BITWUZLA_KIND_BV_SSUB_OVERFLOW: result = sub(i, j); break;
            case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
            case BITWUZLA_KIND_BV_SMUL_OVERFLOW: result = mul(i, j); break;
            default:
              assert(kind == BITWUZLA_KIND_BV_SDIV_OVERFLOW);
              result = div(i, j);
          }

          if (result < 0 || result >= max) overflow_test = true;

          const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
          const BitwuzlaTerm *const1 =
              bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
          const BitwuzlaTerm *const2 =
              bitwuzla_mk_bv_value_uint64(d_bzla, sort, j);
          const BitwuzlaTerm *bfun =
              bitwuzla_mk_term2(d_bzla, kind, const1, const2);
          bitwuzla_assert(d_bzla, bfun);

          sat_res = bitwuzla_check_sat(d_bzla);
          ASSERT_TRUE(sat_res == BITWUZLA_SAT || sat_res == BITWUZLA_UNSAT);
          if (sat_res == BITWUZLA_SAT)
          {
            overflow_bzla = true;
          }
          if (overflow_bzla)
          {
            ASSERT_TRUE(overflow_test);
          }
          if (overflow_test)
          {
            ASSERT_TRUE(overflow_bzla);
          }

          bitwuzla_delete(d_bzla);
          d_bzla = nullptr;
        }
      }
    }
  }

  void s_overflow_test(BitwuzlaKind kind,
                       bool exclude_second_zero,
                       int32_t low,
                       int32_t high,
                       uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    int32_t i, j;
    bool overflow_test, overflow_bzla;
    int32_t result, num_bits, max;
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits - 1);
      for (i = -max; i < max; i++)
      {
        for (j = -max; j < max; j++)
        {
          if (!exclude_second_zero || j != 0)
          {
            if (d_bzla) bitwuzla_delete(d_bzla);
            d_bzla = bitwuzla_new();

            bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

            overflow_test = false;
            overflow_bzla = false;

            switch (kind)
            {
              case BITWUZLA_KIND_BV_UADD_OVERFLOW:
              case BITWUZLA_KIND_BV_SADD_OVERFLOW: result = add(i, j); break;
              case BITWUZLA_KIND_BV_USUB_OVERFLOW:
              case BITWUZLA_KIND_BV_SSUB_OVERFLOW: result = sub(i, j); break;
              case BITWUZLA_KIND_BV_UMUL_OVERFLOW:
              case BITWUZLA_KIND_BV_SMUL_OVERFLOW: result = mul(i, j); break;
              default:
                assert(kind == BITWUZLA_KIND_BV_SDIV_OVERFLOW);
                result = div(i, j);
            }

            if (!(result >= -max && result < max)) overflow_test = true;

            const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
            const BitwuzlaTerm *const1 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) i);
            const BitwuzlaTerm *const2 =
                bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) j);
            const BitwuzlaTerm *bfun =
                bitwuzla_mk_term2(d_bzla, kind, const1, const2);
            bitwuzla_assert(d_bzla, bfun);

            sat_res = bitwuzla_check_sat(d_bzla);
            ASSERT_TRUE(sat_res == BITWUZLA_SAT || sat_res == BITWUZLA_UNSAT);
            if (sat_res == BITWUZLA_SAT)
            {
              overflow_bzla = true;
            }
            if (overflow_bzla)
            {
              ASSERT_TRUE(overflow_test);
            }
            if (overflow_test)
            {
              ASSERT_TRUE(overflow_bzla);
            }

            bitwuzla_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }
};

TEST_F(TestOverflow, uaddo)
{
  u_overflow_test(BITWUZLA_KIND_BV_UADD_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  u_overflow_test(BITWUZLA_KIND_BV_UADD_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, usubo)
{
  u_overflow_test(BITWUZLA_KIND_BV_USUB_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  u_overflow_test(BITWUZLA_KIND_BV_USUB_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, umulo)
{
  u_overflow_test(BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  u_overflow_test(BITWUZLA_KIND_BV_UMUL_OVERFLOW,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, saddo)
{
  s_overflow_test(BITWUZLA_KIND_BV_SADD_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  s_overflow_test(BITWUZLA_KIND_BV_SADD_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, ssubo)
{
  s_overflow_test(BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  s_overflow_test(BITWUZLA_KIND_BV_SSUB_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, smulo)
{
  s_overflow_test(BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  s_overflow_test(BITWUZLA_KIND_BV_SMUL_OVERFLOW,
                  false,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}

TEST_F(TestOverflow, sdivo)
{
  s_overflow_test(BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                  true,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  1);
  s_overflow_test(BITWUZLA_KIND_BV_SDIV_OVERFLOW,
                  true,
                  BZLA_TEST_OVERFLOW_LOW,
                  BZLA_TEST_OVERFLOW_HIGH,
                  0);
}
