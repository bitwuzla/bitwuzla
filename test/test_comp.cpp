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

class TestComp : public TestBitwuzla
{
 protected:
  static constexpr uint32_t BZLA_TEST_COMP_LOW  = 1;
  static constexpr uint32_t BZLA_TEST_COMP_HIGH = 4;

  void u_comp_test(int32_t (*func)(int32_t, int32_t),
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
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits);
      for (i = 0; i < max; i++)
      {
        for (j = 0; j < max; j++)
        {
          result = func(i, j);

          if (d_bzla) bitwuzla_delete(d_bzla);
          d_bzla = bitwuzla_new();
          bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

          const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
          const BitwuzlaTerm *const1, *const2, *bfun;

          const1 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, i);
          const2 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, j);

          bfun = bitwuzla_mk_term2(d_bzla, kind, const1, const2);
          bitwuzla_assert(d_bzla, bfun);

          sat_res = bitwuzla_check_sat(d_bzla);
          ASSERT_TRUE((result && sat_res == BITWUZLA_SAT)
                      || (!result && sat_res == BITWUZLA_UNSAT));
          bitwuzla_delete(d_bzla);
          d_bzla = nullptr;
        }
      }
    }
  }

  void s_comp_test(int32_t (*func)(int32_t, int32_t),
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
    int32_t sat_res;

    for (num_bits = low; num_bits <= high; num_bits++)
    {
      max = bzla_util_pow_2(num_bits - 1);
      for (i = -max; i < max; i++)
      {
        for (j = -max; j < max; j++)
        {
          result = func(i, j);

          if (d_bzla) bitwuzla_delete(d_bzla);
          d_bzla = bitwuzla_new();
          bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, rwl);

          const BitwuzlaSort *sort = bitwuzla_mk_bv_sort(d_bzla, num_bits);
          const BitwuzlaTerm *const1, *const2, *bfun;

          const1 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) i);
          const2 = bitwuzla_mk_bv_value_uint64(d_bzla, sort, (uint64_t) j);

          bfun = bitwuzla_mk_term2(d_bzla, kind, const1, const2);
          bitwuzla_assert(d_bzla, bfun);

          sat_res = bitwuzla_check_sat(d_bzla);
          ASSERT_TRUE(sat_res == BITWUZLA_SAT || sat_res == BITWUZLA_UNSAT);
          if (sat_res == BITWUZLA_SAT)
          {
            ASSERT_TRUE(result > 0);
          }
          else
          {
            ASSERT_EQ(sat_res, BITWUZLA_UNSAT);
            ASSERT_TRUE(result == 0);
          }
          bitwuzla_delete(d_bzla);
          d_bzla = nullptr;
        }
      }
    }
  }

  static int32_t eq(int32_t x, int32_t y) { return x == y; }

  static int32_t ne(int32_t x, int32_t y) { return x != y; }

  static int32_t lt(int32_t x, int32_t y) { return x < y; }

  static int32_t lte(int32_t x, int32_t y) { return x <= y; }

  static int32_t gt(int32_t x, int32_t y) { return x > y; }

  static int32_t gte(int32_t x, int32_t y) { return x >= y; }
};

TEST_F(TestComp, test_eq_1)
{
  u_comp_test(
      eq, BITWUZLA_KIND_EQUAL, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      eq, BITWUZLA_KIND_EQUAL, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ne_1)
{
  u_comp_test(
      ne, BITWUZLA_KIND_DISTINCT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      ne, BITWUZLA_KIND_DISTINCT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ult)
{
  u_comp_test(
      lt, BITWUZLA_KIND_BV_ULT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      lt, BITWUZLA_KIND_BV_ULT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ulte)
{
  u_comp_test(
      lte, BITWUZLA_KIND_BV_ULE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      lte, BITWUZLA_KIND_BV_ULE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ugt)
{
  u_comp_test(
      gt, BITWUZLA_KIND_BV_UGT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      gt, BITWUZLA_KIND_BV_UGT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ugte)
{
  u_comp_test(
      gte, BITWUZLA_KIND_BV_UGE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  u_comp_test(
      gte, BITWUZLA_KIND_BV_UGE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_eq_2)
{
  s_comp_test(
      eq, BITWUZLA_KIND_EQUAL, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      eq, BITWUZLA_KIND_EQUAL, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_ne_2)
{
  s_comp_test(
      ne, BITWUZLA_KIND_DISTINCT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      ne, BITWUZLA_KIND_DISTINCT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_slt)
{
  s_comp_test(
      lt, BITWUZLA_KIND_BV_SLT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      lt, BITWUZLA_KIND_BV_SLT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_slte)
{
  s_comp_test(
      lte, BITWUZLA_KIND_BV_SLE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      lte, BITWUZLA_KIND_BV_SLE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_sgt)
{
  s_comp_test(
      gt, BITWUZLA_KIND_BV_SGT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      gt, BITWUZLA_KIND_BV_SGT, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}

TEST_F(TestComp, test_sgte)
{
  s_comp_test(
      gte, BITWUZLA_KIND_BV_SGE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 1);
  s_comp_test(
      gte, BITWUZLA_KIND_BV_SGE, BZLA_TEST_COMP_LOW, BZLA_TEST_COMP_HIGH, 0);
}
