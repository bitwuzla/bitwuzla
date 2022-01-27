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
#include "bzlabvprop.h"
#include "utils/bzlarng.h"
}

#include <stdlib.h>

#include <algorithm>
#include <bitset>
#include <unordered_set>

#define TEST_BVDOMAINGEN_BW 4

class TestBvDomainGen : public TestBvDomainCommon
{
 protected:
  void SetUp() override
  {
    TestBvDomainCommon::SetUp();
    d_rng        = bzla_rng_new(d_mm, 0);
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
    bzla_rng_delete(d_rng);
    TestBvDomainCommon::TearDown();
  }

  void test_next_aux(const char *str_d,
                     const char *min,
                     const char *max,
                     std::vector<std::string> expected,
                     bool rand      = false,
                     bool is_signed = false)
  {
    void *gen;
    BzlaBvDomain *d       = bzla_bvdomain_new_from_char(d_mm, str_d);
    BzlaBitVector *bv_min = 0;
    BzlaBitVector *bv_max = 0;
    if (min || max)
    {
      bv_min = min ? bzla_bv_char_to_bv(d_mm, min) : 0;
      bv_max = max ? bzla_bv_char_to_bv(d_mm, max) : 0;
      if (is_signed)
      {
        BzlaBvDomainSignedGenerator *g;
        BZLA_NEW(d_mm, g);
        bzla_bvdomain_gen_signed_init_range(
            d_mm, rand ? d_rng : nullptr, g, d, bv_min, bv_max);
        gen = g;
      }
      else
      {
        BzlaBvDomainGenerator *g;
        BZLA_NEW(d_mm, g);
        bzla_bvdomain_gen_init_range(
            d_mm, rand ? d_rng : nullptr, g, d, bv_min, bv_max);
        gen = g;
      }
    }
    else
    {
      if (is_signed)
      {
        BzlaBvDomainSignedGenerator *g;
        BZLA_NEW(d_mm, g);
        bzla_bvdomain_gen_signed_init(d_mm, rand ? d_rng : nullptr, g, d);
        gen = g;
      }
      else
      {
        BzlaBvDomainGenerator *g;
        BZLA_NEW(d_mm, g);
        bzla_bvdomain_gen_init(d_mm, rand ? d_rng : nullptr, g, d);
        gen = g;
      }
    }
    if (bv_min) bzla_bv_free(d_mm, bv_min);
    if (bv_max) bzla_bv_free(d_mm, bv_max);
    if (rand)
    {
      ASSERT_TRUE(expected.size()
                  || (!is_signed
                      && !bzla_bvdomain_gen_has_next(
                          static_cast<BzlaBvDomainGenerator *>(gen)))
                  || (is_signed
                      && !bzla_bvdomain_gen_signed_has_next(
                          static_cast<BzlaBvDomainSignedGenerator *>(gen))));
      std::unordered_set<std::string> results;
      while (results.size() < expected.size())
      {
        BzlaBitVector *res =
            is_signed ? bzla_bvdomain_gen_signed_random(
                static_cast<BzlaBvDomainSignedGenerator *>(gen))
                      : bzla_bvdomain_gen_random(
                          static_cast<BzlaBvDomainGenerator *>(gen));
        char *as_str = bzla_bv_to_char(d_mm, res);
        ASSERT_NE(std::find(expected.begin(), expected.end(), as_str),
                  expected.end());
        results.insert(as_str);
        bzla_mem_freestr(d_mm, as_str);
        /* test that call to has_next in between */
        if (((!is_signed
              && !bzla_bvdomain_gen_has_next(
                  static_cast<BzlaBvDomainGenerator *>(gen)))
             || (is_signed
                 && !bzla_bvdomain_gen_signed_has_next(
                     static_cast<BzlaBvDomainSignedGenerator *>(gen))))
            && bzla_rng_pick_with_prob(d_rng, 500))
        {
          res = is_signed ? bzla_bvdomain_gen_signed_next(
                    static_cast<BzlaBvDomainSignedGenerator *>(gen))
                          : bzla_bvdomain_gen_next(
                              static_cast<BzlaBvDomainGenerator *>(gen));
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
      while ((!is_signed
              && bzla_bvdomain_gen_has_next(
                  static_cast<BzlaBvDomainGenerator *>(gen)))
             || (is_signed
                 && bzla_bvdomain_gen_signed_has_next(
                     static_cast<BzlaBvDomainSignedGenerator *>(gen))))
      {
        BzlaBitVector *res =
            is_signed ? bzla_bvdomain_gen_signed_next(
                static_cast<BzlaBvDomainSignedGenerator *>(gen))
                      : bzla_bvdomain_gen_next(
                          static_cast<BzlaBvDomainGenerator *>(gen));
        assert(i < expected.size());
        ASSERT_LT(i, expected.size());
        BzlaBitVector *exp = bzla_bv_char_to_bv(d_mm, expected[i++].c_str());
        ASSERT_EQ(bzla_bv_compare(res, exp), 0);
        bzla_bv_free(d_mm, exp);
      }
      assert(i == expected.size());
      ASSERT_EQ(i, expected.size());
    }
    bzla_bvdomain_free(d_mm, d);
    if (is_signed)
    {
      bzla_bvdomain_gen_signed_delete(
          static_cast<BzlaBvDomainSignedGenerator *>(gen));
      BZLA_DELETE(d_mm, static_cast<BzlaBvDomainSignedGenerator *>(gen));
    }
    else
    {
      bzla_bvdomain_gen_delete(static_cast<BzlaBvDomainGenerator *>(gen));
      BZLA_DELETE(d_mm, static_cast<BzlaBvDomainGenerator *>(gen));
    }
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

  std::vector<std::string> generate_expected_signed(std::string x,
                                                    const std::string min,
                                                    const std::string max)
  {
    std::vector<std::string> res;
    int64_t mask, imin, imax;
    BzlaBitVector *bv_mask;

    imin = strtol(min.c_str(), 0, 2);
    if (min[0] == '1')
    {
      bv_mask = bzla_bv_ones(d_mm, 64);
      for (uint32_t i = 0, n = min.size(); i < n; ++i)
      {
        bzla_bv_set_bit(bv_mask, i, 0);
      }
      mask = bzla_bv_to_uint64(bv_mask);
      imin |= mask;
      bzla_bv_free(d_mm, bv_mask);
    }

    imax = strtol(max.c_str(), 0, 2);
    if (max[0] == '1')
    {
      bv_mask = bzla_bv_ones(d_mm, 64);
      for (uint32_t i = 0, n = min.size(); i < n; ++i)
      {
        bzla_bv_set_bit(bv_mask, i, 0);
      }
      mask = bzla_bv_to_uint64(bv_mask);
      imax |= mask;
      bzla_bv_free(d_mm, bv_mask);
    }

    if (x.find('x') != std::string::npos)
    {
      for (int32_t i = imin; i <= imax; ++i)
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

  void test_next_signed(bool rand = false)
  {
    std::stringstream ss_max;
    ss_max << "0" << std::string(TEST_BVDOMAINGEN_BW - 1, '1');
    std::stringstream ss_min;
    ss_min << "1" << std::string(TEST_BVDOMAINGEN_BW - 1, '0');

    std::string max_signed = ss_max.str();
    std::string min_signed = ss_min.str();

    for (uint32_t i = 0; i < d_num_consts; ++i)
    {
      for (const std::string &min : d_values)
      {
        /* check with min and max */
        for (const std::string &max : d_values)
        {
          std::vector<std::string> expected =
              generate_expected_signed(d_xvalues[i], min, max);
          test_next_aux(
              d_xvalues[i], min.c_str(), max.c_str(), expected, rand, true);
        }

        /* check with min (no max) */
        std::vector<std::string> expected =
            generate_expected_signed(d_xvalues[i], min, max_signed);
        test_next_aux(d_xvalues[i], min.c_str(), 0, expected, rand, true);
      }
      /* check with max (no min) */
      for (const std::string &max : d_values)
      {
        std::vector<std::string> expected =
            generate_expected_signed(d_xvalues[i], min_signed, max);
        test_next_aux(d_xvalues[i], 0, max.c_str(), expected, rand, true);
      }
      /* check without min and max */
      std::vector<std::string> expected =
          generate_expected_signed(d_xvalues[i], min_signed, max_signed);
      test_next_aux(d_xvalues[i], 0, 0, expected, rand, true);
    }
  }

  uint32_t d_num_consts;
  char **d_xvalues;
  std::vector<std::string> d_values;
  BzlaRNG *d_rng;
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
      bzla_bvdomain_gen_init(d_mm, d_rng, &gen, d);
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

TEST_F(TestBvDomainGen, newdelete_signed)
{
  BzlaBvDomainSignedGenerator gen;
  for (uint32_t bw = 1; bw <= 16; ++bw)
  {
    BzlaBvDomain *d = bzla_bvdomain_new_init(d_mm, bw);
    bzla_bvdomain_gen_signed_init(d_mm, 0, &gen, d);
    bzla_bvdomain_gen_signed_delete(&gen);
    bzla_bvdomain_free(d_mm, d);
  }
}

TEST_F(TestBvDomainGen, has_next_signed)
{
  uint32_t bw, i, num_consts;
  BzlaBvDomainSignedGenerator gen;
  char **consts;
  BzlaBvDomain *d;

  for (bw = 1; bw <= 8; bw++)
  {
    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      bzla_bvdomain_gen_signed_init(d_mm, 0, &gen, d);
      ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d)
                  || bzla_bvdomain_gen_signed_has_next(&gen));
      while (bzla_bvdomain_gen_signed_has_next(&gen))
      {
        bzla_bvdomain_gen_signed_next(&gen);
      }
      bzla_bvdomain_free(d_mm, d);
      bzla_bvdomain_gen_signed_delete(&gen);
    }

    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvDomainGen, next_signed) { test_next_signed(); }

TEST_F(TestBvDomainGen, has_next_rand_signed)
{
  uint32_t bw, i, num_consts, n_tests;
  BzlaBvDomainSignedGenerator gen;
  char **consts;
  BzlaBvDomain *d;

  for (bw = 1; bw <= 4; bw++)
  {
    num_consts = generate_consts(bw, &consts);

    for (i = 0; i < num_consts; i++)
    {
      d = bzla_bvdomain_new_from_char(d_mm, consts[i]);
      bzla_bvdomain_gen_signed_init(d_mm, d_rng, &gen, d);
      ASSERT_TRUE(bzla_bvdomain_is_fixed(d_mm, d)
                  || bzla_bvdomain_gen_signed_has_next(&gen));
      if (bzla_bvdomain_gen_signed_has_next(&gen))
      {
        for (n_tests = 2 * num_consts; n_tests != 0; --n_tests)
        {
          ASSERT_TRUE(bzla_bvdomain_gen_signed_has_next(&gen));
          bzla_bvdomain_gen_signed_random(&gen);
        }
      }
      bzla_bvdomain_free(d_mm, d);
      bzla_bvdomain_gen_signed_delete(&gen);
    }
    free_consts(bw, num_consts, consts);
  }
}

TEST_F(TestBvDomainGen, next_rand_signed) { test_next_signed(true); }
