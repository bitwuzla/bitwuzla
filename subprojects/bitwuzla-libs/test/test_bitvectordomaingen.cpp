#include <bitset>
#include <string>
#include <unordered_set>

#include "gmprandstate.h"
#include "rng.h"
#include "test.h"

namespace bzlals {
namespace test {

/* -------------------------------------------------------------------------- */

class TestBitVectorDomainGen : public TestBvDomainCommon
{
 protected:
  static constexpr uint32_t TEST_BW = 4;
  void SetUp() override
  {
    TestBvDomainCommon::SetUp();
    d_rng.reset(new RNG(1234));
  }
  bool check_const_bits(const std::string& x, const std::string& s);
  std::vector<std::string> generate_expected(const std::string& x,
                                             const std::string min,
                                             const std::string max);
  void test_next(bool rand);
  void test_next_aux(const std::string& str_d,
                     const std::string& str_min,
                     const std::string& str_max,
                     std::vector<std::string> expected,
                     bool random);
  std::unique_ptr<RNG> d_rng;
};

bool
TestBitVectorDomainGen::check_const_bits(const std::string& x,
                                         const std::string& s)
{
  assert(x.size() == s.size());
  for (uint32_t i = 0, n = x.size(); i < n; ++i)
  {
    if (x[i] != 'x' && x[i] != s[i]) return false;
  }
  return true;
}

std::vector<std::string>
TestBitVectorDomainGen::generate_expected(const std::string& x,
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
      std::string v = std::bitset<TEST_BW>(i).to_string();
      if (check_const_bits(x, v))
      {
        res.push_back(v);
      }
    }
  }
  return res;
}

void
TestBitVectorDomainGen::test_next_aux(const std::string& str_d,
                                      const std::string& str_min,
                                      const std::string& str_max,
                                      std::vector<std::string> expected,
                                      bool random)
{
  assert((!str_min.empty() && !str_max.empty())
         || (str_min.empty() && str_max.empty()));

  BitVectorDomain d(str_d);
  std::unique_ptr<BitVectorDomainGenerator> gen;

  if (str_min.empty())
  {
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
    ASSERT_TRUE(expected.size() || gen->has_next());
    std::unordered_set<std::string> results;
    while (results.size() < expected.size())
    {
      BitVector res       = gen->random();
      std::string res_str = res.to_string();
      ASSERT_NE(std::find(expected.begin(), expected.end(), res_str),
                expected.end());
      results.insert(res_str);
      /* test that call to has_next in between */
      if (gen->has_next() && d_rng->flip_coin())
      {
        res     = gen->next();
        res_str = res.to_string();
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
TestBitVectorDomainGen::test_next(bool random)
{
  std::string ones(TEST_BW, '1');
  std::string zero(TEST_BW, '0');
  std::vector<std::string> xvalues;
  std::vector<std::string> values;
  gen_xvalues(TEST_BW, xvalues);
  gen_values(TEST_BW, values);

  for (uint32_t i = 0, n = values.size(); i < n; ++i)
  {
    for (const std::string& min : values)
    {
      /* check with min and max */
      for (const std::string& max : values)
      {
        std::vector<std::string> expected =
            generate_expected(xvalues[i], min, max);
        test_next_aux(xvalues[i], min.c_str(), max.c_str(), expected, random);
      }
    }
    /* check without min and max */
    std::vector<std::string> expected =
        generate_expected(xvalues[i], zero, ones);
    test_next_aux(xvalues[i], "", "", expected, random);
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVectorDomainGen, ctor_dtor)
{
  for (uint32_t size = 1; size <= 16; ++size)
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

TEST_F(TestBitVectorDomainGen, has_next)
{
  for (uint32_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint32_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainGenerator gen(d);
      assert(d.is_fixed() || gen.has_next());
      ASSERT_TRUE(d.is_fixed() || gen.has_next());
      while (gen.has_next())
      {
        ASSERT_NO_FATAL_FAILURE(gen.next());
      }
    }
  }
}

TEST_F(TestBitVectorDomainGen, has_next_rand)
{
  for (uint32_t size = 1; size <= 8; ++size)
  {
    std::vector<std::string> xvalues;
    gen_xvalues(size, xvalues);

    for (uint32_t i = 0, n = xvalues.size(); i < n; ++i)
    {
      BitVectorDomain d(xvalues[i]);
      BitVectorDomainGenerator gen(d, d_rng.get());
      assert(d.is_fixed() || gen.has_next());
      ASSERT_TRUE(d.is_fixed() || gen.has_next());
      while (gen.has_next())
      {
        ASSERT_NO_FATAL_FAILURE(gen.next());
      }
      if (gen.has_next())
      {
        for (uint32_t n_tests = 2 * n; n_tests != 0; --n_tests)
        {
          ASSERT_TRUE(gen.has_next());
          ASSERT_NO_FATAL_FAILURE(gen.random());
        }
      }
    }
  }
}

TEST_F(TestBitVectorDomainGen, next)
{
  test_next(false);
  ASSERT_DEATH(BitVectorDomainGenerator(BitVector::mk_ones(4)).next(),
               "has_next");
}

}  // namespace test
}  // namespace bzlals
