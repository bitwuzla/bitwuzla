/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2020 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitset>
#include <string>
#include <unordered_set>

#include "ls/bv/bitvector_domain.h"
#include "test_lib.h"

namespace bzla::ls::test {

/* -------------------------------------------------------------------------- */

class TestBvDomainGen : public ::bzla::test::TestCommon
{
 protected:
  static constexpr uint64_t TEST_BW = 4;
  void SetUp() override
  {
    TestCommon::SetUp();
    d_rng.reset(new RNG(1234));
  }
  bool check_const_bits(const std::string& x, const std::string& s);
  std::vector<std::string> generate_expected(const std::string& x,
                                             const std::string min,
                                             const std::string max);
  std::vector<std::string> generate_expected_signed(std::string x,
                                                    const std::string min,
                                                    const std::string max);
  void test_next(bool rand, bool is_signed);
  void test_next_aux(const std::string& str_d,
                     const std::string& str_min,
                     const std::string& str_max,
                     std::vector<std::string> expected,
                     bool random);
  void test_next_signed_aux(const std::string& str_d,
                            const std::string& str_min,
                            const std::string& str_max,
                            std::vector<std::string> expected,
                            bool random);
  std::unique_ptr<RNG> d_rng;
};

bool
TestBvDomainGen::check_const_bits(const std::string& x, const std::string& s)
{
  assert(x.size() == s.size());
  for (uint64_t i = 0, n = x.size(); i < n; ++i)
  {
    if (x[i] != 'x' && x[i] != s[i]) return false;
  }
  return true;
}

std::vector<std::string>
TestBvDomainGen::generate_expected(const std::string& x,
                                   const std::string min,
                                   const std::string max)
{
  std::vector<std::string> res;
  uint64_t umin = strtoul(min.c_str(), 0, 2);
  uint64_t umax = strtoul(max.c_str(), 0, 2);

  if (x.find('x') != std::string::npos)
  {
    for (uint64_t i = umin; i <= umax; ++i)
    {
      std::string v = std::bitset<TEST_BW>(i).to_string();
      if (check_const_bits(x, v))
      {
        res.push_back(v);
      }
    }
  }
  return res;
}

std::vector<std::string>
TestBvDomainGen::generate_expected_signed(std::string x,
                                          const std::string min,
                                          const std::string max)
{
  std::vector<std::string> res;
  int64_t imin = strtol(min.c_str(), 0, 2);
  int64_t imax = strtol(max.c_str(), 0, 2);

  if (min[0] == '1')
  {
    BitVector bv_mask = BitVector::mk_ones(64);
    for (uint64_t i = 0, n = min.size(); i < n; ++i)
    {
      bv_mask.set_bit(i, false);
    }
    int64_t mask = static_cast<int64_t>(bv_mask.to_uint64());
    imin |= mask;
  }

  if (max[0] == '1')
  {
    BitVector bv_mask = BitVector::mk_ones(64);
    for (uint64_t i = 0, n = min.size(); i < n; ++i)
    {
      bv_mask.set_bit(i, false);
    }
    int64_t mask = static_cast<int64_t>(bv_mask.to_uint64());
    imax |= mask;
  }

  if (x.find('x') != std::string::npos)
  {
    for (int64_t i = imin; i <= imax; ++i)
    {
      std::string v = std::bitset<TEST_BW>(static_cast<size_t>(i)).to_string();
      if (check_const_bits(x, v))
      {
        res.push_back(v);
      }
    }
  }
  return res;
}

void
TestBvDomainGen::test_next_aux(const std::string& str_d,
                               const std::string& str_min,
                               const std::string& str_max,
                               std::vector<std::string> expected,
                               bool random)
{
  BitVectorDomain d(str_d);
  std::unique_ptr<BitVectorDomainGenerator> gen;

  if (str_min.empty())
  {
    assert(str_max.empty());
    gen.reset(new BitVectorDomainGenerator(d, random ? d_rng.get() : nullptr));
  }
  else
  {
    BitVector min(str_min.size(), str_min);
    BitVector max(str_max.size(), str_max);
    gen.reset(new BitVectorDomainGenerator(
        d, random ? d_rng.get() : nullptr, min, max));
  }

  if (random)
  {
    ASSERT_TRUE(expected.size() || !gen->has_random());
    std::unordered_set<std::string> results;
    while (results.size() < expected.size())
    {
      assert(gen->has_random());
      ASSERT_TRUE(gen->has_random());
      BitVector res       = gen->random();
      std::string res_str = res.str();
      ASSERT_NE(std::find(expected.begin(), expected.end(), res_str),
                expected.end());
      results.insert(res_str);
      /* test that call to has_next in between */
      if (gen->has_next() && d_rng->flip_coin())
      {
        res     = gen->next();
        res_str = res.str();
        ASSERT_NE(std::find(expected.begin(), expected.end(), res_str),
                  expected.end());
        results.insert(res_str);
      }
    }
  }
  else
  {
    uint32_t i = 0;
    while (gen->has_next())
    {
      BitVector res = gen->next();
      assert(i < expected.size());
      ASSERT_LT(i, expected.size());
      BitVector exp(expected[i].size(), expected[i]);
      i += 1;
      ASSERT_EQ(res.compare(exp), 0);
    }
    assert(i == expected.size());
    ASSERT_EQ(i, expected.size());
  }
}

void
TestBvDomainGen::test_next_signed_aux(const std::string& str_d,
                                      const std::string& str_min,
                                      const std::string& str_max,
                                      std::vector<std::string> expected,
                                      bool random)
{
  BitVectorDomain d(str_d);
  std::unique_ptr<BitVectorDomainSignedGenerator> gen;

  if (str_min.empty())
  {
    assert(str_max.empty());
    gen.reset(
        new BitVectorDomainSignedGenerator(d, random ? d_rng.get() : nullptr));
  }
  else
  {
    assert(!str_max.empty());
    BitVector min(str_min.size(), str_min);
    BitVector max(str_max.size(), str_max);
    gen.reset(new BitVectorDomainSignedGenerator(
        d, random ? d_rng.get() : nullptr, min, max));
  }

  if (random)
  {
    ASSERT_TRUE(expected.size() || !gen->has_random());
    std::unordered_set<std::string> results;
    while (results.size() < expected.size())
    {
      assert(gen->has_random());
      ASSERT_TRUE(gen->has_random());
      BitVector res       = gen->random();
      std::string res_str = res.str();
      ASSERT_NE(std::find(expected.begin(), expected.end(), res_str),
                expected.end());
      results.insert(res_str);
      /* test that call to has_next in between */
      if (gen->has_next() && d_rng->flip_coin())
      {
        res     = gen->next();
        res_str = res.str();
        ASSERT_NE(std::find(expected.begin(), expected.end(), res_str),
                  expected.end());
        results.insert(res_str);
      }
    }
  }
  else
  {
    uint64_t i = 0;
    while (gen->has_next())
    {
      BitVector res = gen->next();
      assert(i < expected.size());
      ASSERT_LT(i, expected.size());
      BitVector exp(expected[i].size(), expected[i]);
      i += 1;
      assert(res.compare(exp) == 0);
      ASSERT_EQ(res.compare(exp), 0);
    }
    assert(i == expected.size());
    ASSERT_EQ(i, expected.size());
  }
}

void
TestBvDomainGen::test_next(bool random, bool is_signed)
{
  std::string ones(TEST_BW, '1');
  std::string zero(TEST_BW, '0');
  std::vector<std::string> xvalues;
  std::vector<std::string> values;
  gen_xvalues(TEST_BW, xvalues);
  gen_values(TEST_BW, values);

  for (uint64_t i = 0, n = values.size(); i < n; ++i)
  {
    for (const std::string& min : values)
    {
      /* check with min and max */
      for (const std::string& max : values)
      {
        if (is_signed)
        {
          std::vector<std::string> expected =
              generate_expected_signed(xvalues[i], min, max);
          test_next_signed_aux(
              xvalues[i], min.c_str(), max.c_str(), expected, random);
        }
        else
        {
          std::vector<std::string> expected =
              generate_expected_signed(xvalues[i], min, max);
          test_next_signed_aux(
              xvalues[i], min.c_str(), max.c_str(), expected, random);
        }
      }
    }
    /* check without min and max */
    std::vector<std::string> expected =
        generate_expected(xvalues[i], zero, ones);
    if (is_signed)
    {
      test_next_signed_aux(xvalues[i], "", "", expected, random);
    }
    else
    {
      test_next_aux(xvalues[i], "", "", expected, random);
    }
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBvDomainGen, ctor_dtor)
{
  for (uint64_t size = 1; size <= 16; ++size)
  {
    ASSERT_NO_FATAL_FAILURE(BitVectorDomainGenerator(BitVectorDomain(size)));
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainGenerator(BitVectorDomain(size), d_rng.get()));
    BitVector from(size, *d_rng);
    BitVector to(size, *d_rng, from, BitVector::mk_ones(size));
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainGenerator(BitVectorDomain(size), from, to));
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainGenerator(BitVectorDomain(size), d_rng.get(), from, to));
  }
}

TEST_F(TestBvDomainGen, has_next)
{
  for (uint64_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint64_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainGenerator gen(d);
      ASSERT_TRUE(d.is_fixed() || gen.has_next());
      while (gen.has_next())
      {
        gen.next();
      }
    }
  }
}

TEST_F(TestBvDomainGen, has_random)
{
  for (uint64_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint64_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainGenerator gen(d, d_rng.get());
      ASSERT_TRUE(d.is_fixed() || gen.has_random());
      if (gen.has_next())
      {
        for (uint64_t j = 0; j < size; ++j)
        {
          ASSERT_TRUE(gen.has_random());
          gen.random();
        }
      }
    }
  }
}

TEST_F(TestBvDomainGen, next)
{
  test_next(false, false);
  ASSERT_DEATH_DEBUG(BitVectorDomainGenerator(BitVector::mk_ones(4)).next(),
                     "has_next");
}

TEST_F(TestBvDomainGen, random)
{
  test_next(true, false);
  ASSERT_DEATH_DEBUG(BitVectorDomainGenerator(BitVector::mk_ones(4)).random(),
                     "has_random");
}

TEST_F(TestBvDomainGen, ctor_dtor_signed)
{
  for (uint64_t size = 1; size <= 16; ++size)
  {
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainSignedGenerator(BitVectorDomain(size)));
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainSignedGenerator(BitVectorDomain(size), d_rng.get()));
    BitVector from(size, *d_rng);
    BitVector to(size, *d_rng, from, BitVector::mk_ones(size));
    ASSERT_NO_FATAL_FAILURE(
        BitVectorDomainSignedGenerator(BitVectorDomain(size), from, to));
    ASSERT_NO_FATAL_FAILURE(BitVectorDomainSignedGenerator(
        BitVectorDomain(size), d_rng.get(), from, to));
  }
}

TEST_F(TestBvDomainGen, has_next_signed)
{
  for (uint64_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint64_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainSignedGenerator gen(d);
      while (gen.has_next())
      {
        gen.next();
      }
    }
  }
}

TEST_F(TestBvDomainGen, has_random_signed)
{
  for (uint64_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint64_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainSignedGenerator gen(d, d_rng.get());
      if (gen.has_next())
      {
        for (uint64_t j = 0; j < size; ++j)
        {
          ASSERT_TRUE(gen.has_random());
          gen.random();
        }
      }
    }
  }
}

TEST_F(TestBvDomainGen, next_signed)
{
  test_next(true, true);
  ASSERT_DEATH_DEBUG(
      BitVectorDomainSignedGenerator(BitVector::mk_ones(4)).next(), "has_next");
}

TEST_F(TestBvDomainGen, random_signed)
{
  test_next(true, true);
  ASSERT_DEATH_DEBUG(
      BitVectorDomainSignedGenerator(BitVector::mk_ones(4)).random(),
      "has_random");
}

}  // namespace bzla::ls::test
