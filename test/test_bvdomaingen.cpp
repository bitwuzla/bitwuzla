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

#include <bitset>
#include <unordered_set>

#define TEST_BVDOMAINGEN_BW 4

class TestBvDomainGen : public TestBvDomainCommon
{
 protected:
  void SetUp() override
  {
    TestBvDomainCommon::SetUp();
    bzla_rng_init(&d_rng, 0);
    d_num_consts = generate_consts(TEST_BVDOMAINGEN_BW, &d_xvalues);
    for (uint32_t i = 0; i < (1u << TEST_BVDOMAINGEN_BW); ++i)
    {
      std::string v = std::bitset<TEST_BVDOMAINGEN_BW>(i).to_string();
      d_values.push_back(v);
    }
  }

  void TearDown() override
  {
    free_consts(TEST_BVDOMAINGEN_BW, d_num_consts, d_xvalues);
    TestBvDomainCommon::TearDown();
  }

  void test_next_aux(const char *str_d,
                     const char *min,
                     const char *max,
                     std::vector<std::string> expected,
                     bool rand = false)
  {
    BzlaBvDomainGenerator gen;
    BzlaBvDomain *d       = bzla_bvdomain_new_from_char(d_mm, str_d);
    BzlaBitVector *bv_min = 0;
    BzlaBitVector *bv_max = 0;
    if (min || max)
    {
      bv_min = min ? bzla_bv_char_to_bv(d_mm, min) : 0;
      bv_max = max ? bzla_bv_char_to_bv(d_mm, max) : 0;
      bzla_bvdomain_gen_init_range(
          d_mm, rand ? &d_rng : nullptr, &gen, d, bv_min, bv_max);
    }
    else
    {
      bzla_bvdomain_gen_init(d_mm, rand ? &d_rng : nullptr, &gen, d);
    }
    if (bv_min) bzla_bv_free(d_mm, bv_min);
    if (bv_max) bzla_bv_free(d_mm, bv_max);
    if (rand)
    {
      ASSERT_TRUE(expected.size() || !bzla_bvdomain_gen_has_next(&gen));
      std::unordered_set<std::string> results;
      while (results.size() < expected.size())
      {
        BzlaBitVector *res = bzla_bvdomain_gen_random(&gen);
        char *as_str       = bzla_bv_to_char(d_mm, res);
        ASSERT_NE(std::find(expected.begin(), expected.end(), as_str),
                  expected.end());
        results.insert(as_str);
        bzla_mem_freestr(d_mm, as_str);
        /* test that call to has_next in between */
        if (bzla_bvdomain_gen_has_next(&gen)
            && bzla_rng_pick_with_prob(&d_rng, 500))
        {
          res    = bzla_bvdomain_gen_next(&gen);
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
      while (bzla_bvdomain_gen_has_next(&gen))
      {
        ASSERT_LT(i, expected.size());
        BzlaBitVector *res = bzla_bvdomain_gen_next(&gen);
        BzlaBitVector *exp = bzla_bv_char_to_bv(d_mm, expected[i++].c_str());
        ASSERT_EQ(bzla_bv_compare(res, exp), 0);
        bzla_bv_free(d_mm, exp);
      }
      ASSERT_EQ(i, expected.size());
    }
    bzla_bvdomain_free(d_mm, d);
    bzla_bvdomain_gen_delete(&gen);
  }

  bool check_const_bits(std::string &x, std::string &s)
  {
    assert(x.size() == s.size());
    for (uint32_t i = 0, n = x.size(); i < n; ++i)
    {
      if (x[i] != 'x' && x[i] != s[i]) return false;
    }
    return true;
  }

  std::vector<std::string> generate_expected(std::string x,
                                             const std::string min,
                                             const std::string max)
  {
    std::vector<std::string> res;
    uint64_t umin = strtoul(min.c_str(), 0, 2);
    uint64_t umax = strtoul(max.c_str(), 0, 2);

    if (x.find('x') != std::string::npos)
    {
      for (uint32_t i = umin; i <= umax; ++i)
      {
        std::string v = std::bitset<TEST_BVDOMAINGEN_BW>(i).to_string();
        if (check_const_bits(x, v))
        {
          res.push_back(v);
        }
      }
    }
    return res;
  }

  void test_next(bool rand = false)
  {
    std::string ones(TEST_BVDOMAINGEN_BW, '1');
    std::string zero(TEST_BVDOMAINGEN_BW, '0');

    for (uint32_t i = 0; i < d_num_consts; ++i)
    {
      for (const std::string &min : d_values)
      {
        /* check with min and max */
        for (const std::string &max : d_values)
        {
          std::vector<std::string> expected =
              generate_expected(d_xvalues[i], min, max);
          test_next_aux(d_xvalues[i], min.c_str(), max.c_str(), expected, rand);
        }

        /* check with min (no max) */
        std::vector<std::string> expected =
            generate_expected(d_xvalues[i], min, ones);
        test_next_aux(d_xvalues[i], min.c_str(), 0, expected, rand);
      }
      /* check with max (no min) */
      for (const std::string &max : d_values)
      {
        std::vector<std::string> expected =
            generate_expected(d_xvalues[i], zero, max);
        test_next_aux(d_xvalues[i], 0, max.c_str(), expected, rand);
      }
      /* check without min and max */
      std::vector<std::string> expected =
          generate_expected(d_xvalues[i], zero, ones);
      test_next_aux(d_xvalues[i], 0, 0, expected, rand);
    }
  }

  uint32_t d_num_consts;
  char **d_xvalues;
  std::vector<std::string> d_values;
  BzlaRNG d_rng;
};

TEST_F(TestBvDomainGen, newdelete)
{
  BzlaBvDomainGenerator gen;
  for (uint32_t bw = 1; bw <= 16; ++bw)
  {
    BzlaBvDomain *d = bzla_bvdomain_new_init(d_mm, bw);
    bzla_bvdomain_gen_init(d_mm, 0, &gen, d);
    bzla_bvdomain_gen_delete(&gen);
    bzla_bvdomain_free(d_mm, d);
  }
}

TEST_F(TestBvDomainGen, has_next)
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
      d = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      bzla_bvdomain_gen_init(d_mm, 0, &gen, d);
      ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d)
                  || bzla_bvdomain_gen_has_next(&gen));
      while (bzla_bvdomain_gen_has_next(&gen))
      {
        bzla_bvdomain_gen_next(&gen);
      }
      bzla_bvdomain_free(d_mm, d);
      bzla_bvdomain_gen_delete(&gen);
    }

    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvDomainGen, next) { test_next(); }

TEST_F(TestBvDomainGen, has_next_rand)
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
      d = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      bzla_bvdomain_gen_init(d_mm, &d_rng, &gen, d);
      ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d)
                  || bzla_bvdomain_gen_has_next(&gen));
      if (bzla_bvdomain_gen_has_next(&gen))
      {
        for (n_tests = 2 * num_consts; n_tests != 0; --n_tests)
        {
          ASSERT_TRUE(bzla_bvdomain_gen_has_next(&gen));
          bzla_bvdomain_gen_random(&gen);
        }
      }
      bzla_bvdomain_free(d_mm, d);
      bzla_bvdomain_gen_delete(&gen);
    }
    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvDomainGen, next_rand) { test_next(true); }
