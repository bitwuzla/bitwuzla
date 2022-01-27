/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * This file is part of Bitwuzla.
 *
 * Copyright (C) 2007-2022 by the authors listed in the AUTHORS file.
 *
 * See COPYING for more information on using this software.
 */

#include <sstream>

#include "test.h"

extern "C" {
#include "bzlaopt.h"
}

class TestInc : public TestBitwuzla
{
 protected:
  void test_inc_counter(uint32_t w, bool nondet)
  {
    assert(w > 0);

    std::stringstream name;
    uint32_t i;
    int32_t res;

    bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

    const BitwuzlaSort *s       = bitwuzla_mk_bv_sort(d_bzla, w);
    const BitwuzlaTerm *one     = bitwuzla_mk_bv_one(d_bzla, s);
    const BitwuzlaTerm *current = bitwuzla_mk_bv_zero(d_bzla, s);

    i = 0;
    for (;;)
    {
      const BitwuzlaTerm *inc =
          bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_ADD, current, one);
      const BitwuzlaTerm *next, *oracle;

      if (nondet)
      {
        name << oracle << i;
        if (i)
        {
          s      = bitwuzla_mk_bool_sort(d_bzla);
          oracle = bitwuzla_mk_const(d_bzla, s, name.str().c_str());
        }

        else
        {
          oracle = bitwuzla_mk_true(d_bzla);
        }
        next =
            bitwuzla_mk_term3(d_bzla, BITWUZLA_KIND_ITE, oracle, inc, current);
      }
      else
      {
        next = inc;
      }

      current = next;

      const BitwuzlaTerm *nonzero =
          bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_REDOR, current);
      const BitwuzlaTerm *allzero =
          bitwuzla_mk_term1(d_bzla, BITWUZLA_KIND_BV_NOT, nonzero);

      i++;

      bitwuzla_assume(d_bzla, allzero);

      res = bitwuzla_check_sat(d_bzla);
      if (res == BITWUZLA_SAT)
      {
        break;
      }
      ASSERT_EQ(res, BITWUZLA_UNSAT);
      ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, allzero));
      ASSERT_LT(i, (uint32_t)(1 << w));
    }

    ASSERT_EQ(i, (uint32_t)(1 << w));
  }

  void test_inc_lt(uint32_t w)
  {
    assert(w > 0);

    const BitwuzlaTerm *prev, *next, *lt;
    const BitwuzlaSort *s;
    std::stringstream name;
    uint32_t i;
    int32_t res;

    bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);

    i    = 0;
    prev = 0;
    for (;;)
    {
      i++;
      name << i;
      s    = bitwuzla_mk_bv_sort(d_bzla, w);
      next = bitwuzla_mk_const(d_bzla, s, name.str().c_str());

      if (prev)
      {
        lt = bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_BV_ULT, prev, next);
        bitwuzla_assert(d_bzla, lt);
      }

      prev = next;

      res = bitwuzla_check_sat(d_bzla);
      if (res == BITWUZLA_UNSAT) break;

      ASSERT_EQ(res, BITWUZLA_SAT);
      ASSERT_LE(i, (uint32_t)(1 << w));
    }

    ASSERT_EQ(i, (uint32_t)(1 << w) + 1);
  }
};

TEST_F(TestInc, true_false)
{
  const BitwuzlaTerm *ff = bitwuzla_mk_false(d_bzla);
  const BitwuzlaTerm *tt = bitwuzla_mk_true(d_bzla);
  int32_t res;

  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  bitwuzla_assume(d_bzla, tt);
  res = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(res, BITWUZLA_SAT);

  bitwuzla_assume(d_bzla, ff);
  res = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(res, BITWUZLA_UNSAT);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, ff));
}

TEST_F(TestInc, count1) { test_inc_counter(1, false); }

TEST_F(TestInc, count2) { test_inc_counter(2, false); }

TEST_F(TestInc, count3) { test_inc_counter(3, false); }

TEST_F(TestInc, count4) { test_inc_counter(4, false); }

TEST_F(TestInc, count8) { test_inc_counter(8, false); }

TEST_F(TestInc, count1nondet) { test_inc_counter(1, true); }

TEST_F(TestInc, count2nondet) { test_inc_counter(2, true); }

TEST_F(TestInc, count3nondet) { test_inc_counter(3, true); }

TEST_F(TestInc, count4nondet) { test_inc_counter(4, true); }

TEST_F(TestInc, count8nondet) { test_inc_counter(8, true); }

TEST_F(TestInc, lt1) { test_inc_lt(1); }

TEST_F(TestInc, lt2) { test_inc_lt(2); }

TEST_F(TestInc, lt3) { test_inc_lt(3); }

TEST_F(TestInc, lt4) { test_inc_lt(4); }

TEST_F(TestInc, lt8) { test_inc_lt(8); }

TEST_F(TestInc, assume_assert1)
{
  int32_t sat_result;
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, 0);
  const BitwuzlaSort *s      = bitwuzla_mk_bool_sort(d_bzla);
  const BitwuzlaSort *as     = bitwuzla_mk_array_sort(d_bzla, s, s);
  const BitwuzlaTerm *array  = bitwuzla_mk_const(d_bzla, as, "array1");
  const BitwuzlaTerm *index1 = bitwuzla_mk_const(d_bzla, s, "index1");
  const BitwuzlaTerm *index2 = bitwuzla_mk_const(d_bzla, s, "index2");
  const BitwuzlaTerm *read1 =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_ARRAY_SELECT, array, index1);
  const BitwuzlaTerm *read2 =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_ARRAY_SELECT, array, index2);
  const BitwuzlaTerm *eq_index =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, index1, index2);
  const BitwuzlaTerm *ne_read =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_DISTINCT, read1, read2);
  bitwuzla_assert(d_bzla, ne_read);
  sat_result = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(sat_result, BITWUZLA_SAT);
  bitwuzla_assume(d_bzla, eq_index);
  sat_result = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(sat_result, BITWUZLA_UNSAT);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, eq_index));
  sat_result = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(sat_result, BITWUZLA_SAT);
}

TEST_F(TestInc, lemmas_on_demand1)
{
  int32_t sat_result;

  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_INCREMENTAL, 1);
  bitwuzla_set_option(d_bzla, BITWUZLA_OPT_RW_LEVEL, 0);
  const BitwuzlaSort *s      = bitwuzla_mk_bool_sort(d_bzla);
  const BitwuzlaSort *as     = bitwuzla_mk_array_sort(d_bzla, s, s);
  const BitwuzlaTerm *array  = bitwuzla_mk_const(d_bzla, as, "array1");
  const BitwuzlaTerm *index1 = bitwuzla_mk_const(d_bzla, s, "index1");
  const BitwuzlaTerm *index2 = bitwuzla_mk_const(d_bzla, s, "index2");
  const BitwuzlaTerm *read1 =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_ARRAY_SELECT, array, index1);
  const BitwuzlaTerm *read2 =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_ARRAY_SELECT, array, index2);
  const BitwuzlaTerm *eq =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_EQUAL, index1, index2);
  const BitwuzlaTerm *ne =
      bitwuzla_mk_term2(d_bzla, BITWUZLA_KIND_DISTINCT, read1, read2);
  bitwuzla_assert(d_bzla, eq);
  bitwuzla_assume(d_bzla, ne);
  sat_result = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(sat_result, BITWUZLA_UNSAT);
  ASSERT_TRUE(bitwuzla_is_unsat_assumption(d_bzla, ne));
  sat_result = bitwuzla_check_sat(d_bzla);
  ASSERT_EQ(sat_result, BITWUZLA_SAT);
}
