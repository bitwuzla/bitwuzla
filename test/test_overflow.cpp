/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlaaig.h"
#include "dumper/bzladumpaig.h"
#include "utils/bzlautil.h"
}

class TestOverflow : public TestBzla
{
 protected:
  static constexpr uint32_t BZLA_TEST_OVERFLOW_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_OVERFLOW_HIGH = 4;

  enum Op
  {
    UADD,
    SADD,
    USUB,
    SSUB,
    UMUL,
    SMUL,
    SDIV
  };

  int32_t add(int32_t x, int32_t y) { return x + y; }

  int32_t sub(int32_t x, int32_t y) { return x - y; }

  int32_t mul(int32_t x, int32_t y) { return x * y; }

  int32_t div(int32_t x, int32_t y)
  {
    assert(y != 0);
    return x / y;
  }

  void u_overflow_test(Op op, int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    BoolectorNode *(*bzla_fun)(Bzla *, BoolectorNode *, BoolectorNode *);

    int32_t i, j, num_bits, max, result;
    bool overflow_test, overflow_boolector;
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          BoolectorSort sort;
          BoolectorNode *const1, *const2, *bfun;

          if (d_bzla) boolector_delete(d_bzla);
          d_bzla = boolector_new();

          boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

          overflow_test      = false;
          overflow_boolector = false;

          switch (op)
          {
            case UADD:
              bzla_fun = boolector_bv_uaddo;
              result   = add(i, j);
              break;
            case SADD:
              bzla_fun = boolector_bv_saddo;
              result   = add(i, j);
              break;
            case USUB:
              bzla_fun = boolector_bv_usubo;
              result   = sub(i, j);
              break;
            case SSUB:
              bzla_fun = boolector_bv_ssubo;
              result   = sub(i, j);
              break;
            case UMUL:
              bzla_fun = boolector_bv_umulo;
              result   = mul(i, j);
              break;
            case SMUL:
              bzla_fun = boolector_bv_smulo;
              result   = mul(i, j);
              break;
            default:
              assert(op == SDIV);
              bzla_fun = boolector_bv_sdivo;
              result   = div(i, j);
          }

          if (result < 0 || result >= max) overflow_test = true;

          sort   = boolector_bv_sort(d_bzla, num_bits);
          const1 = boolector_unsigned_int(d_bzla, i, sort);
          const2 = boolector_unsigned_int(d_bzla, j, sort);
          bfun   = bzla_fun(d_bzla, const1, const2);
          boolector_assert(d_bzla, bfun);

          sat_res = boolector_sat(d_bzla);
          ASSERT_TRUE(sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
          if (sat_res == BOOLECTOR_SAT)
          {
            overflow_boolector = true;
          }
          if (overflow_boolector)
          {
            ASSERT_TRUE(overflow_test);
          }
          if (overflow_test)
          {
            ASSERT_TRUE(overflow_boolector);
          }

          boolector_release_sort(d_bzla, sort);
          boolector_release(d_bzla, const1);
          boolector_release(d_bzla, const2);
          boolector_release(d_bzla, bfun);
          boolector_delete(d_bzla);
          d_bzla = nullptr;
        }
      }
    }
  }

  void s_overflow_test(
      Op op, bool exclude_second_zero, int32_t low, int32_t high, uint32_t rwl)
  {
    assert(low > 0);
    assert(low <= high);

    BoolectorNode *(*bzla_fun)(Bzla *, BoolectorNode *, BoolectorNode *);

    int32_t i, j;
    bool overflow_test, overflow_boolector;
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
            BoolectorSort sort;
            BoolectorNode *const1, *const2, *bfun;

            if (d_bzla) boolector_delete(d_bzla);
            d_bzla = boolector_new();

            boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, rwl);

            overflow_test      = false;
            overflow_boolector = false;

            switch (op)
            {
              case UADD:
                bzla_fun = boolector_bv_uaddo;
                result   = add(i, j);
                break;
              case SADD:
                bzla_fun = boolector_bv_saddo;
                result   = add(i, j);
                break;
              case USUB:
                bzla_fun = boolector_bv_usubo;
                result   = sub(i, j);
                break;
              case SSUB:
                bzla_fun = boolector_bv_ssubo;
                result   = sub(i, j);
                break;
              case UMUL:
                bzla_fun = boolector_bv_umulo;
                result   = mul(i, j);
                break;
              case SMUL:
                bzla_fun = boolector_bv_smulo;
                result   = mul(i, j);
                break;
              default:
                assert(op == SDIV);
                bzla_fun = boolector_bv_sdivo;
                result   = div(i, j);
            }

            if (!(result >= -max && result < max)) overflow_test = true;

            sort   = boolector_bv_sort(d_bzla, num_bits);
            const1 = boolector_int(d_bzla, i, sort);
            const2 = boolector_int(d_bzla, j, sort);
            bfun   = bzla_fun(d_bzla, const1, const2);
            boolector_assert(d_bzla, bfun);

            sat_res = boolector_sat(d_bzla);
            ASSERT_TRUE(sat_res == BOOLECTOR_SAT || sat_res == BOOLECTOR_UNSAT);
            if (sat_res == BOOLECTOR_SAT)
            {
              overflow_boolector = true;
            }
            if (overflow_boolector)
            {
              ASSERT_TRUE(overflow_test);
            }
            if (overflow_test)
            {
              ASSERT_TRUE(overflow_boolector);
            }

            boolector_release_sort(d_bzla, sort);
            boolector_release(d_bzla, const1);
            boolector_release(d_bzla, const2);
            boolector_release(d_bzla, bfun);
            boolector_delete(d_bzla);
            d_bzla = nullptr;
          }
        }
      }
    }
  }
};

TEST_F(TestOverflow, uaddo)
{
  u_overflow_test(UADD, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test(UADD, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, usubo)
{
  u_overflow_test(USUB, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test(USUB, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, umulo)
{
  u_overflow_test(UMUL, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  u_overflow_test(UMUL, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, saddo)
{
  s_overflow_test(
      SADD, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test(
      SADD, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, ssubo)
{
  s_overflow_test(
      SSUB, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test(
      SSUB, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, smulo)
{
  s_overflow_test(
      SMUL, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test(
      SMUL, false, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}

TEST_F(TestOverflow, sdivo)
{
  s_overflow_test(
      SDIV, true, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 1);
  s_overflow_test(
      SDIV, true, BZLA_TEST_OVERFLOW_LOW, BZLA_TEST_OVERFLOW_HIGH, 0);
}
