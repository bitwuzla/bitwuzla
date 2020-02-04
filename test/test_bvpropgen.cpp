/*  Boolector: Satisfiability Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2020 Aina Niemetz.
 *  Copyright (C) 2020 Mathias Preiner.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include "test.h"

extern "C" {
#include "bzlabvprop.h"
#include "utils/bzlarng.h"
}

#include <stdlib.h>

#include <unordered_set>

class TestBvPropGen : public TestBvDomain
{
 protected:
  void SetUp() override
  {
    TestBvDomain::SetUp();
    bzla_rng_init(&d_rng, 0);
  }

  void test_next(const char *str_d,
                 const char *min,
                 const char *max,
                 std::vector<std::string> expected,
                 bool rand = false)
  {
    BzlaBvDomainGenerator gen;
    BzlaBvDomain *d       = bzla_bvprop_new_from_char(d_mm, str_d);
    BzlaBitVector *bv_min = 0;
    BzlaBitVector *bv_max = 0;
    if (min || max)
    {
      bv_min = min ? bzla_bv_char_to_bv(d_mm, min) : 0;
      bv_max = max ? bzla_bv_char_to_bv(d_mm, max) : 0;
      bzla_bvprop_gen_init_range(
          d_mm, rand ? &d_rng : nullptr, &gen, d, bv_min, bv_max);
    }
    else
    {
      bzla_bvprop_gen_init(d_mm, rand ? &d_rng : nullptr, &gen, d);
    }
    if (bv_min) bzla_bv_free(d_mm, bv_min);
    if (bv_max) bzla_bv_free(d_mm, bv_max);
    if (rand)
    {
      ASSERT_TRUE(expected.size() || !bzla_bvprop_gen_has_next(&gen));
      std::unordered_set<std::string> results;
      while (results.size() < expected.size())
      {
        BzlaBitVector *res = bzla_bvprop_gen_random(&gen);
        char *as_str       = bzla_bv_to_char(d_mm, res);
        ASSERT_NE(std::find(expected.begin(), expected.end(), as_str),
                  expected.end());
        results.insert(as_str);
        bzla_mem_freestr(d_mm, as_str);
        /* test that call to has_next in between */
        if (bzla_bvprop_gen_has_next(&gen)
            && bzla_rng_pick_with_prob(&d_rng, 500))
        {
          res    = bzla_bvprop_gen_next(&gen);
          as_str = bzla_bv_to_char(d_mm, res);
          ASSERT_NE(std::find(expected.begin(), expected.end(), as_str),
                    expected.end());
          results.insert(as_str);
          bzla_mem_freestr(d_mm, as_str);
        }
      }
    }
    else
    {
      uint32_t i = 0;
      while (bzla_bvprop_gen_has_next(&gen))
      {
        ASSERT_LT(i, expected.size());
        BzlaBitVector *res = bzla_bvprop_gen_next(&gen);
        BzlaBitVector *exp = bzla_bv_char_to_bv(d_mm, expected[i++].c_str());
        ASSERT_EQ(bzla_bv_compare(res, exp), 0);
        bzla_bv_free(d_mm, exp);
      }
      ASSERT_EQ(i, expected.size());
    }
    bzla_bvprop_free(d_mm, d);
    bzla_bvprop_gen_delete(&gen);
  }

  BzlaRNG d_rng;
};

TEST_F(TestBvPropGen, newdelete)
{
  BzlaBvDomainGenerator gen;
  for (uint32_t bw = 1; bw <= 16; ++bw)
  {
    BzlaBvDomain *d = bzla_bvprop_new_init(d_mm, bw);
    bzla_bvprop_gen_init(d_mm, 0, &gen, d);
    bzla_bvprop_gen_delete(&gen);
    bzla_bvprop_free(d_mm, d);
  }
}

TEST_F(TestBvPropGen, has_next)
{
  uint32_t bw, i, num_consts;
  BzlaBvDomainGenerator gen;
  char **consts;
  BzlaBvDomain *d;

  for (bw = 1; bw <= 8; bw++)
  {
    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d = bzla_bvprop_new_from_char(d_mm, consts[i]);
      bzla_bvprop_gen_init(d_mm, 0, &gen, d);
      ASSERT_TRUE(bzla_bvprop_is_fixed(d_mm, d)
                  || bzla_bvprop_gen_has_next(&gen));
      while (bzla_bvprop_gen_has_next(&gen))
      {
        bzla_bvprop_gen_next(&gen);
      }
      bzla_bvprop_free(d_mm, d);
      bzla_bvprop_gen_delete(&gen);
    }

    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvPropGen, next_00x) { test_next("00x", 0, 0, {"000", "001"}); }
TEST_F(TestBvPropGen, next_01x) { test_next("01x", 0, 0, {"010", "011"}); }
TEST_F(TestBvPropGen, next_10x) { test_next("10x", 0, 0, {"100", "101"}); }
TEST_F(TestBvPropGen, next_11x) { test_next("11x", 0, 0, {"110", "111"}); }

TEST_F(TestBvPropGen, next_0x0) { test_next("0x0", 0, 0, {"000", "010"}); }
TEST_F(TestBvPropGen, next_0x1) { test_next("0x1", 0, 0, {"001", "011"}); }
TEST_F(TestBvPropGen, next_1x0) { test_next("1x0", 0, 0, {"100", "110"}); }
TEST_F(TestBvPropGen, next_1x1) { test_next("1x1", 0, 0, {"101", "111"}); }

TEST_F(TestBvPropGen, next_x00) { test_next("x00", 0, 0, {"000", "100"}); }
TEST_F(TestBvPropGen, next_x01) { test_next("x01", 0, 0, {"001", "101"}); }
TEST_F(TestBvPropGen, next_x10) { test_next("x10", 0, 0, {"010", "110"}); }
TEST_F(TestBvPropGen, next_x11) { test_next("x11", 0, 0, {"011", "111"}); }

TEST_F(TestBvPropGen, next_0xx)
{
  test_next("0xx", 0, 0, {"000", "001", "010", "011"});
}

TEST_F(TestBvPropGen, next_1xx)
{
  test_next("1xx", 0, 0, {"100", "101", "110", "111"});
}

TEST_F(TestBvPropGen, next_xx0)
{
  test_next("xx0", 0, 0, {"000", "010", "100", "110"});
}

TEST_F(TestBvPropGen, next_xx1)
{
  test_next("xx1", 0, 0, {"001", "011", "101", "111"});
}

TEST_F(TestBvPropGen, next_xxx)
{
  test_next(
      "xxx", 0, 0, {"000", "001", "010", "011", "100", "101", "110", "111"});
}

TEST_F(TestBvPropGen, next_range_00x_11)
{
  test_next("00x", 0, "000", {"000"});
}
TEST_F(TestBvPropGen, next_range_00x_21)
{
  test_next("00x", 0, "001", {"000", "001"});
}
TEST_F(TestBvPropGen, next_range_00x_31)
{
  test_next("00x", 0, "010", {"000", "001"});
}
TEST_F(TestBvPropGen, next_range_00x_12)
{
  test_next("00x", "000", "000", {"000"});
}
TEST_F(TestBvPropGen, next_range_00x_22)
{
  test_next("00x", "000", "001", {"000", "001"});
}
TEST_F(TestBvPropGen, next_range_00x_32)
{
  test_next("00x", "001", "010", {"001"});
}
TEST_F(TestBvPropGen, next_range_00x_13)
{
  test_next("00x", "000", 0, {"000", "001"});
}
TEST_F(TestBvPropGen, next_range_00x_23)
{
  test_next("00x", "001", 0, {"001"});
}
TEST_F(TestBvPropGen, next_range_00x_33) { test_next("00x", "010", 0, {}); }

TEST_F(TestBvPropGen, next_range_01x_11)
{
  test_next("01x", 0, "011", {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_12)
{
  test_next("01x", 0, "010", {"010"});
}
TEST_F(TestBvPropGen, next_range_01x_13) { test_next("01x", 0, "000", {}); }
TEST_F(TestBvPropGen, next_range_01x_21)
{
  test_next("01x", "000", 0, {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_22)
{
  test_next("01x", "010", 0, {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_23) { test_next("01x", "100", 0, {}); }
TEST_F(TestBvPropGen, next_range_01x_31)
{
  test_next("01x", "000", "011", {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_32)
{
  test_next("01x", "010", "100", {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_33)
{
  test_next("01x", "010", "010", {"010"});
}
TEST_F(TestBvPropGen, next_range_01x_34) { test_next("01x", "100", "111", {}); }
TEST_F(TestBvPropGen, next_range_x10_35) { test_next("x10", "011", "101", {}); }

TEST_F(TestBvPropGen, next_range_01x_regr1)
{
  test_next("01x", "001", "110", {"010", "011"});
}
TEST_F(TestBvPropGen, next_range_01x_regr2)
{
  test_next("x1x", "001", 0, {"010", "011", "110", "111"});
}

TEST_F(TestBvPropGen, has_next_rand)
{
  uint32_t bw, i, num_consts, n_tests;
  BzlaBvDomainGenerator gen;
  char **consts;
  BzlaBvDomain *d;

  for (bw = 1; bw <= 4; bw++)
  {
    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d = bzla_bvprop_new_from_char(d_mm, consts[i]);
      bzla_bvprop_gen_init(d_mm, &d_rng, &gen, d);
      ASSERT_TRUE(bzla_bvprop_is_fixed(d_mm, d)
                  || bzla_bvprop_gen_has_next(&gen));
      if (bzla_bvprop_gen_has_next(&gen))
      {
        for (n_tests = 2 * num_consts; n_tests != 0; --n_tests)
        {
          ASSERT_TRUE(bzla_bvprop_gen_has_next(&gen));
          bzla_bvprop_gen_random(&gen);
        }
      }
      bzla_bvprop_free(d_mm, d);
      bzla_bvprop_gen_delete(&gen);
    }
    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvPropGen, next_00x_rand)
{
  test_next("00x", 0, 0, {"000", "001"}, true);
}
TEST_F(TestBvPropGen, next_01x_rand)
{
  test_next("01x", 0, 0, {"010", "011"}, true);
}
TEST_F(TestBvPropGen, next_10x_rand)
{
  test_next("10x", 0, 0, {"100", "101"}, true);
}
TEST_F(TestBvPropGen, next_11x_rand)
{
  test_next("11x", 0, 0, {"110", "111"}, true);
}

TEST_F(TestBvPropGen, next_0x0_rand)
{
  test_next("0x0", 0, 0, {"000", "010"}, true);
}
TEST_F(TestBvPropGen, next_0x1_rand)
{
  test_next("0x1", 0, 0, {"001", "011"}, true);
}
TEST_F(TestBvPropGen, next_1x0_rand)
{
  test_next("1x0", 0, 0, {"100", "110"}, true);
}
TEST_F(TestBvPropGen, next_1x1_rand)
{
  test_next("1x1", 0, 0, {"101", "111"}, true);
}

TEST_F(TestBvPropGen, next_x00_rand)
{
  test_next("x00", 0, 0, {"000", "100"}, true);
}
TEST_F(TestBvPropGen, next_x01_rand)
{
  test_next("x01", 0, 0, {"001", "101"}, true);
}
TEST_F(TestBvPropGen, next_x10_rand)
{
  test_next("x10", 0, 0, {"010", "110"}, true);
}
TEST_F(TestBvPropGen, next_x11_rand)
{
  test_next("x11", 0, 0, {"011", "111"}, true);
}

TEST_F(TestBvPropGen, next_0xx_rand)
{
  test_next("0xx", 0, 0, {"000", "001", "010", "011"}, true);
}

TEST_F(TestBvPropGen, next_1xx_rand)
{
  test_next("1xx", 0, 0, {"100", "101", "110", "111"}, true);
}

TEST_F(TestBvPropGen, next_xx0_rand)
{
  test_next("xx0", 0, 0, {"000", "010", "100", "110"}, true);
}

TEST_F(TestBvPropGen, next_xx1_rand)
{
  test_next("xx1", 0, 0, {"001", "011", "101", "111"}, true);
}

TEST_F(TestBvPropGen, next_xxx_1_rand)
{
  test_next("xxx",
            "000",
            "111",
            {"000", "001", "010", "011", "100", "101", "110", "111"},
            true);
}

TEST_F(TestBvPropGen, next_xxx_2_rand)
{
  test_next("xxx",
            0,
            0,
            {"000", "001", "010", "011", "100", "101", "110", "111"},
            true);
}

TEST_F(TestBvPropGen, next_range_00x_11_rand)
{
  test_next("00x", 0, "000", {"000"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_21_rand)
{
  test_next("00x", 0, "001", {"000", "001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_31_rand)
{
  test_next("00x", 0, "010", {"000", "001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_12_rand)
{
  test_next("00x", "000", "000", {"000"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_22_rand)
{
  test_next("00x", "000", "001", {"000", "001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_32_rand)
{
  test_next("00x", "001", "010", {"001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_13_rand)
{
  test_next("00x", "000", 0, {"000", "001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_23_rand)
{
  test_next("00x", "001", 0, {"001"}, true);
}

TEST_F(TestBvPropGen, next_range_00x_33_rand)
{
  test_next("00x", "010", 0, {}, true);
}

TEST_F(TestBvPropGen, next_range_01x_11_rand)
{
  test_next("01x", 0, "011", {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_12_rand)
{
  test_next("01x", 0, "010", {"010"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_13_rand)
{
  test_next("01x", 0, "000", {}, true);
}

TEST_F(TestBvPropGen, next_range_01x_21_rand)
{
  test_next("01x", "000", 0, {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_22_rand)
{
  test_next("01x", "010", 0, {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_23_rand)
{
  test_next("01x", "100", 0, {}, true);
}

TEST_F(TestBvPropGen, next_range_01x_31_rand)
{
  test_next("01x", "000", "011", {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_32_rand)
{
  test_next("01x", "010", "100", {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_33_rand)
{
  test_next("01x", "010", "010", {"010"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_34_rand)
{
  test_next("01x", "100", "111", {}, true);
}

TEST_F(TestBvPropGen, next_range_x10_35_rand_rand)
{
  test_next("x10", "011", "101", {}, true);
}

TEST_F(TestBvPropGen, next_range_01x_regr1_rand)
{
  test_next("01x", "001", "110", {"010", "011"}, true);
}

TEST_F(TestBvPropGen, next_range_01x_regr2_rand)
{
  test_next("x1x", "001", 0, {"010", "011", "110", "111"}, true);
}
