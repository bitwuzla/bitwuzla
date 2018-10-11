/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2007-2010 Robert Daniel Brummayer.
 *  Copyright (C) 2007-2012 Armin Biere.
 *  Copyright (C) 2012-2019 Aina Niemetz
 *  Copyright (C) 2016 Mathias Preiner
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlaopt.h"
}

class TestInc : public TestBoolector
{
 protected:
  void test_inc_counter(uint32_t w, bool nondet)
  {
    assert(w > 0);

    BoolectorNode *nonzero, *allzero, *one, *oracle;
    BoolectorNode *current, *next, *inc;
    BoolectorSort s;
    char name[100];
    uint32_t i;
    int32_t res;

    boolector_set_opt(d_bzla, BZLA_OPT_INCREMENTAL, 1);
    s       = boolector_bv_sort(d_bzla, w);
    one     = boolector_one(d_bzla, s);
    current = boolector_zero(d_bzla, s);
    boolector_release_sort(d_bzla, s);

    i = 0;

    for (;;)
    {
      inc = boolector_add(d_bzla, current, one);

      if (nondet)
      {
        sprintf(name, "oracle%d", i);
        if (i)
        {
          s      = boolector_bool_sort(d_bzla);
          oracle = boolector_var(d_bzla, s, name);
          boolector_release_sort(d_bzla, s);
        }

        else
          oracle = boolector_true(d_bzla);
        next = boolector_cond(d_bzla, oracle, inc, current);
        boolector_release(d_bzla, oracle);
      }
      else
        next = boolector_copy(d_bzla, inc);

      boolector_release(d_bzla, inc);
      boolector_release(d_bzla, current);
      current = next;

      nonzero = boolector_bv_redor(d_bzla, current);
      allzero = boolector_bv_not(d_bzla, nonzero);
      boolector_release(d_bzla, nonzero);

      i++;

      boolector_assume(d_bzla, allzero);

      res = boolector_sat(d_bzla);
      if (res == BOOLECTOR_SAT)
      {
        boolector_release(d_bzla, allzero);
        break;
      }
      ASSERT_EQ(res, BOOLECTOR_UNSAT);
      ASSERT_TRUE(boolector_failed(d_bzla, allzero));
      ASSERT_LT(i, (uint32_t)(1 << w));
      boolector_release(d_bzla, allzero);
    }

    ASSERT_EQ(i, (uint32_t)(1 << w));

    boolector_release(d_bzla, one);
    boolector_release(d_bzla, current);
  }

  void test_inc_lt(uint32_t w)
  {
    assert(w > 0);

    BoolectorNode *prev, *next, *lt;
    BoolectorSort s;
    char name[100];
    uint32_t i;
    int32_t res;

    boolector_set_opt(d_bzla, BZLA_OPT_INCREMENTAL, 1);

    i    = 0;
    prev = 0;
    for (;;)
    {
      i++;

      sprintf(name, "%d", i);
      s    = boolector_bv_sort(d_bzla, w);
      next = boolector_var(d_bzla, s, name);
      boolector_release_sort(d_bzla, s);

      if (prev)
      {
        lt = boolector_ult(d_bzla, prev, next);
        boolector_assert(d_bzla, lt);
        boolector_release(d_bzla, lt);
        boolector_release(d_bzla, prev);
      }

      prev = next;

      res = boolector_sat(d_bzla);
      if (res == BOOLECTOR_UNSAT) break;

      ASSERT_EQ(res, BOOLECTOR_SAT);
      ASSERT_LE(i, (uint32_t)(1 << w));
    }

    ASSERT_EQ(i, (uint32_t)(1 << w) + 1);

    boolector_release(d_bzla, prev);
  }
};

TEST_F(TestInc, true_false)
{
  BoolectorNode *ff;
  BoolectorNode *tt;
  int32_t res;

  ff = boolector_false(d_bzla);
  tt = boolector_true(d_bzla);
  boolector_set_opt(d_bzla, BZLA_OPT_INCREMENTAL, 1);
  boolector_assume(d_bzla, tt);
  res = boolector_sat(d_bzla);
  ASSERT_EQ(res, BOOLECTOR_SAT);

  boolector_assume(d_bzla, ff);
  res = boolector_sat(d_bzla);
  ASSERT_EQ(res, BOOLECTOR_UNSAT);
  ASSERT_TRUE(boolector_failed(d_bzla, ff));

  boolector_release(d_bzla, ff);
  boolector_release(d_bzla, tt);
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
  BoolectorNode *array, *index1, *index2, *read1, *read2, *eq_index, *ne_read;
  BoolectorSort s, as;

  boolector_set_opt(d_bzla, BZLA_OPT_INCREMENTAL, 1);
  boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, 0);
  s        = boolector_bool_sort(d_bzla);
  as       = boolector_array_sort(d_bzla, s, s);
  array    = boolector_array(d_bzla, as, "array1");
  index1   = boolector_var(d_bzla, s, "index1");
  index2   = boolector_var(d_bzla, s, "index2");
  read1    = boolector_read(d_bzla, array, index1);
  read2    = boolector_read(d_bzla, array, index2);
  eq_index = boolector_eq(d_bzla, index1, index2);
  ne_read  = boolector_ne(d_bzla, read1, read2);
  boolector_assert(d_bzla, ne_read);
  sat_result = boolector_sat(d_bzla);
  ASSERT_EQ(sat_result, BOOLECTOR_SAT);
  boolector_assume(d_bzla, eq_index);
  sat_result = boolector_sat(d_bzla);
  ASSERT_EQ(sat_result, BOOLECTOR_UNSAT);
  ASSERT_TRUE(boolector_failed(d_bzla, eq_index));
  sat_result = boolector_sat(d_bzla);
  ASSERT_EQ(sat_result, BOOLECTOR_SAT);
  boolector_release(d_bzla, array);
  boolector_release(d_bzla, index1);
  boolector_release(d_bzla, index2);
  boolector_release(d_bzla, read1);
  boolector_release(d_bzla, read2);
  boolector_release(d_bzla, eq_index);
  boolector_release(d_bzla, ne_read);
  boolector_release_sort(d_bzla, s);
  boolector_release_sort(d_bzla, as);
}

TEST_F(TestInc, lemmas_on_demand1)
{
  int32_t sat_result;
  BoolectorNode *array, *index1, *index2, *read1, *read2, *eq, *ne;
  BoolectorSort s, as;

  boolector_set_opt(d_bzla, BZLA_OPT_INCREMENTAL, 1);
  boolector_set_opt(d_bzla, BZLA_OPT_REWRITE_LEVEL, 0);
  s      = boolector_bool_sort(d_bzla);
  as     = boolector_array_sort(d_bzla, s, s);
  array  = boolector_array(d_bzla, as, "array1");
  index1 = boolector_var(d_bzla, s, "index1");
  index2 = boolector_var(d_bzla, s, "index2");
  read1  = boolector_read(d_bzla, array, index1);
  read2  = boolector_read(d_bzla, array, index2);
  eq     = boolector_eq(d_bzla, index1, index2);
  ne     = boolector_ne(d_bzla, read1, read2);
  boolector_assert(d_bzla, eq);
  boolector_assume(d_bzla, ne);
  sat_result = boolector_sat(d_bzla);
  ASSERT_EQ(sat_result, BOOLECTOR_UNSAT);
  ASSERT_TRUE(boolector_failed(d_bzla, ne));
  sat_result = boolector_sat(d_bzla);
  ASSERT_EQ(sat_result, BOOLECTOR_SAT);
  boolector_release(d_bzla, array);
  boolector_release(d_bzla, index1);
  boolector_release(d_bzla, index2);
  boolector_release(d_bzla, read1);
  boolector_release(d_bzla, read2);
  boolector_release(d_bzla, eq);
  boolector_release(d_bzla, ne);
  boolector_release_sort(d_bzla, s);
  boolector_release_sort(d_bzla, as);
}
