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

#include "ls/bv/bitvector_domain.h"
#include "test_lib.h"

namespace bzla::ls::test {

/* -------------------------------------------------------------------------- */

class TestBitVectorDomain : public ::bzla::test::TestCommon
{
 protected:
  void test_match_fixed_bits(const std::string &value);
};

void
TestBitVectorDomain::test_match_fixed_bits(const std::string &value)
{
  assert(value.size() == 3);
  BitVectorDomain d(value);
  for (uint32_t i = 0; i < (1u << 3); ++i)
  {
    bool expected      = true;
    std::string bv_val = std::bitset<3>(i).to_string();
    BitVector bv(3, bv_val);
    for (uint32_t j = 0; j < 3; ++j)
    {
      if ((d.is_fixed_bit_false(j) && bv_val[2 - j] != '0')
          || (d.is_fixed_bit_true(j) && bv_val[2 - j] != '1'))
      {
        expected = false;
      }
    }
    ASSERT_EQ(d.match_fixed_bits(bv), expected);
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestBitVectorDomain, ctor_dtor)
{
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(1));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(10));
  ASSERT_NO_FATAL_FAILURE(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5)));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain("00000000"));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain("11111111"));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain("10110100"));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain("x01xxxxx"));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain("xxxxxxxx"));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(BitVector(4, "0000")));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(BitVector(8, "1010")));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(4, 0));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(8, 5));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(BitVectorDomain(8, 5)));
  ASSERT_DEATH_DEBUG(BitVectorDomain(0), "size > 0");
  ASSERT_DEATH_DEBUG(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(11, 5)),
      "lo.size\\(\\) == hi.size\\(\\)");
  ASSERT_DEATH_DEBUG(BitVectorDomain(""), "size > 0");
  ASSERT_DEATH_DEBUG(BitVectorDomain("12345"), "is_valid_bin_str");
}

TEST_F(TestBitVectorDomain, size)
{
  ASSERT_EQ(BitVectorDomain(1).size(), 1);
  ASSERT_EQ(BitVectorDomain(10).size(), 10);
  ASSERT_EQ(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5))
          .size(),
      10);
  ASSERT_EQ(BitVectorDomain("00000000").size(), 8);
  ASSERT_EQ(BitVectorDomain("11111111").size(), 8);
  ASSERT_EQ(BitVectorDomain("10110100").size(), 8);
  ASSERT_EQ(BitVectorDomain("x01xxxxx").size(), 8);
  ASSERT_EQ(BitVectorDomain("xxxxxxxx").size(), 8);
  ASSERT_EQ(BitVectorDomain(BitVector(4, "0000")).size(), 4);
  ASSERT_EQ(BitVectorDomain(BitVector(8, "1010")).size(), 8);
  ASSERT_EQ(BitVectorDomain(4, 0).size(), 4);
  ASSERT_EQ(BitVectorDomain(8, 5).size(), 8);
  ASSERT_EQ(BitVectorDomain(BitVectorDomain(8, 5)).size(), 8);
}

TEST_F(TestBitVectorDomain, is_valid)
{
  ASSERT_TRUE(BitVectorDomain(1).is_valid());
  ASSERT_TRUE(BitVectorDomain(10).is_valid());
  ASSERT_TRUE(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5))
          .is_valid());
  ASSERT_TRUE(BitVectorDomain("00000000").is_valid());
  ASSERT_TRUE(BitVectorDomain("11111111").is_valid());
  ASSERT_TRUE(BitVectorDomain("10110100").is_valid());
  ASSERT_TRUE(BitVectorDomain("x01xxxxx").is_valid());
  ASSERT_TRUE(BitVectorDomain("xxxxxxxx").is_valid());
  ASSERT_TRUE(BitVectorDomain(BitVector(4, "0000")).is_valid());
  ASSERT_TRUE(BitVectorDomain(BitVector(8, "1010")).is_valid());
  ASSERT_TRUE(BitVectorDomain(4, 0).is_valid());
  ASSERT_TRUE(BitVectorDomain(8, 5).is_valid());
  ASSERT_TRUE(BitVectorDomain(BitVectorDomain(8, 5)).is_valid());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "1000"), BitVector(4, "0111")).is_valid());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "0100"), BitVector(4, "1011")).is_valid());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "0110"), BitVector(4, "1001")).is_valid());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "1001"), BitVector(4, "0110")).is_valid());
}

TEST_F(TestBitVectorDomain, is_fixed)
{
  ASSERT_FALSE(BitVectorDomain(1).is_fixed());
  ASSERT_FALSE(BitVectorDomain(10).is_fixed());
  ASSERT_FALSE(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5))
          .is_fixed());
  ASSERT_TRUE(BitVectorDomain("00000000").is_fixed());
  ASSERT_TRUE(BitVectorDomain("11111111").is_fixed());
  ASSERT_TRUE(BitVectorDomain("10110100").is_fixed());
  ASSERT_FALSE(BitVectorDomain("x01xxxxx").is_fixed());
  ASSERT_FALSE(BitVectorDomain("xxxxxxxx").is_fixed());
  ASSERT_TRUE(BitVectorDomain(BitVector(4, "0000")).is_fixed());
  ASSERT_TRUE(BitVectorDomain(BitVector(8, "1010")).is_fixed());
  ASSERT_TRUE(BitVectorDomain(4, 0).is_fixed());
  ASSERT_TRUE(BitVectorDomain(8, 5).is_fixed());
  ASSERT_TRUE(BitVectorDomain(BitVectorDomain(8, 5)).is_fixed());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "1000"), BitVector(4, "0111")).is_fixed());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "0100"), BitVector(4, "1011")).is_fixed());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "0110"), BitVector(4, "1001")).is_fixed());
  ASSERT_FALSE(
      BitVectorDomain(BitVector(4, "1001"), BitVector(4, "0110")).is_fixed());
}

TEST_F(TestBitVectorDomain, has_fixed_bits)
{
  ASSERT_FALSE(BitVectorDomain(1).has_fixed_bits());
  ASSERT_FALSE(BitVectorDomain(10).has_fixed_bits());
  ASSERT_TRUE(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5))
          .has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain("00000000").has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain("11111111").has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain("10110100").has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain("x01xxxxx").has_fixed_bits());
  ASSERT_FALSE(BitVectorDomain("xxxxxxxx").has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain(BitVector(4, "0000")).has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain(BitVector(8, "1010")).has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain(4, 0).has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain(8, 5).has_fixed_bits());
  ASSERT_TRUE(BitVectorDomain(BitVectorDomain(8, 5)).has_fixed_bits());
  ASSERT_DEATH_DEBUG(BitVectorDomain(BitVector(4, "1000"), BitVector(4, "0111"))
                         .has_fixed_bits(),
                     "is_valid");
  ASSERT_DEATH_DEBUG(BitVectorDomain(BitVector(4, "0100"), BitVector(4, "1011"))
                         .has_fixed_bits(),
                     "is_valid");
  ASSERT_DEATH_DEBUG(BitVectorDomain(BitVector(4, "0110"), BitVector(4, "1001"))
                         .has_fixed_bits(),
                     "is_valid");
  ASSERT_DEATH_DEBUG(BitVectorDomain(BitVector(4, "1001"), BitVector(4, "0110"))
                         .has_fixed_bits(),
                     "is_valid");
}

TEST_F(TestBitVectorDomain, is_fixed_bit)
{
  BitVectorDomain d(BitVector(4, "1000"), BitVector(4, "1111"));
  ASSERT_TRUE(d.is_fixed_bit(3));
  for (uint32_t i = 0; i < 3; ++i)
  {
    ASSERT_FALSE(d.is_fixed_bit(i));
  }
  ASSERT_DEATH_DEBUG(d.is_fixed_bit(5), "< size");
}

TEST_F(TestBitVectorDomain, is_fixed_bit_true)
{
  BitVectorDomain d(BitVector(4, "1000"), BitVector(4, "1110"));
  ASSERT_TRUE(d.is_fixed_bit_true(3));
  for (uint32_t i = 0; i < 3; ++i)
  {
    ASSERT_FALSE(d.is_fixed_bit_true(i));
  }
  ASSERT_DEATH_DEBUG(d.is_fixed_bit(5), "< size");
}

TEST_F(TestBitVectorDomain, is_fixed_bit_false)
{
  BitVectorDomain d(BitVector(4, "1000"), BitVector(4, "1110"));
  ASSERT_TRUE(d.is_fixed_bit_false(0));
  for (uint32_t i = 1; i < 4; ++i)
  {
    ASSERT_FALSE(d.is_fixed_bit_false(i));
  }
  ASSERT_DEATH_DEBUG(d.is_fixed_bit(5), "< size");
}

TEST_F(TestBitVectorDomain, fix_bit)
{
  BitVectorDomain d("xxxx");
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(0, true));
  ASSERT_EQ(d, BitVectorDomain("xxx1"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(0, false));
  ASSERT_EQ(d, BitVectorDomain("xxx0"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(1, true));
  ASSERT_EQ(d, BitVectorDomain("xx10"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(1, false));
  ASSERT_EQ(d, BitVectorDomain("xx00"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(2, true));
  ASSERT_EQ(d, BitVectorDomain("x100"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(2, false));
  ASSERT_EQ(d, BitVectorDomain("x000"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(3, true));
  ASSERT_EQ(d, BitVectorDomain("1000"));
  ASSERT_NO_FATAL_FAILURE(d.fix_bit(3, false));
  ASSERT_EQ(d, BitVectorDomain("0000"));
  ASSERT_DEATH_DEBUG(d.fix_bit(5, true), "< size");
}

TEST_F(TestBitVectorDomain, match_fixed_bits)
{
  for (uint32_t i = 0; i < 3; ++i)
  {
    for (uint32_t j = 0; j < 3; ++j)
    {
      for (uint32_t k = 0; k < 3; ++k)
      {
        std::stringstream ss;
        ss << (i == 0 ? '0' : (i == 1 ? '1' : 'x'))
           << (j == 0 ? '0' : (j == 1 ? '1' : 'x'))
           << (k == 0 ? '0' : (k == 1 ? '1' : 'x'));
        test_match_fixed_bits(ss.str());
      }
    }
  }
}

TEST_F(TestBitVectorDomain, eq)
{
  BitVectorDomain d1("xxxx");
  BitVectorDomain d2("x10x");
  BitVectorDomain d3("x10x");
  ASSERT_TRUE(d2 == d3);
  ASSERT_FALSE(d1 == d2);
  ASSERT_FALSE(d1 == d3);
}

TEST_F(TestBitVectorDomain, not )
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        BitVectorDomain dnot = d.bvnot();
        ASSERT_EQ(d.size(), dnot.size());
        for (uint64_t k = 0, n = d.size(); k < n; ++k)
        {
          if (c[n - k - 1] == 'x')
          {
            ASSERT_FALSE(d.is_fixed_bit(k));
            ASSERT_FALSE(dnot.is_fixed_bit(k));
          }
          else if (c[n - k - 1] == '1')
          {
            ASSERT_TRUE(d.is_fixed_bit_true(k));
            ASSERT_TRUE(dnot.is_fixed_bit_false(k));
          }
          else
          {
            assert(c[n - k - 1] == '0');
            ASSERT_TRUE(d.is_fixed_bit_false(k));
            ASSERT_TRUE(dnot.is_fixed_bit_true(k));
          }
        }
      }
    }
  }
}

TEST_F(TestBitVectorDomain, shl)
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        for (uint64_t k = 0; k < 3; ++k)
        {
          BitVectorDomain dshl = d.bvshl(BitVector::from_ui(3, k));
          ASSERT_EQ(d.size(), dshl.size());
          for (size_t l = 0, n = d.size(); l < n; ++l)
          {
            if (l < k)
            {
              ASSERT_TRUE(dshl.is_fixed_bit_false(l));
            }
            else
            {
              if (c[n + k - l - 1] == 'x')
              {
                ASSERT_FALSE(dshl.is_fixed_bit(l));
              }
              else if (c[n + k - l - 1] == '1')
              {
                ASSERT_TRUE(dshl.is_fixed_bit_true(l));
              }
              else
              {
                assert(c[n + k - l - 1] == '0');
                ASSERT_TRUE(dshl.is_fixed_bit_false(l));
              }
            }
          }
        }
      }
    }
  }
  ASSERT_DEATH_DEBUG(BitVectorDomain(3).bvshl(BitVector(4)),
                     "size\\(\\) == size\\(\\)");
}

TEST_F(TestBitVectorDomain, shr)
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        for (uint64_t k = 0; k < 3; ++k)
        {
          BitVectorDomain dshr = d.bvshr(BitVector::from_ui(3, k));
          ASSERT_EQ(d.size(), dshr.size());
          for (size_t l = 0, n = d.size(); l < n; ++l)
          {
            if (l >= n - k)
            {
              ASSERT_TRUE(dshr.is_fixed_bit_false(l));
            }
            else
            {
              if (c[n - k - l - 1] == 'x')
              {
                ASSERT_FALSE(dshr.is_fixed_bit(l));
              }
              else if (c[n - k - l - 1] == '1')
              {
                ASSERT_TRUE(dshr.is_fixed_bit_true(l));
              }
              else
              {
                assert(c[n - k - l - 1] == '0');
                ASSERT_TRUE(dshr.is_fixed_bit_false(l));
              }
            }
          }
        }
      }
    }
  }
  ASSERT_DEATH_DEBUG(BitVectorDomain(3).bvshr(BitVector(4)),
                     "size\\(\\) == size\\(\\)");
}

TEST_F(TestBitVectorDomain, ashr)
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        for (uint64_t k = 0; k < 3; ++k)
        {
          BitVectorDomain dashr = d.bvashr(BitVector::from_ui(3, k));
          ASSERT_EQ(d.size(), dashr.size());
          for (size_t l = 0, n = d.size(); l < n; ++l)
          {
            if (l >= n - k)
            {
              if (c[0] == '0')
              {
                ASSERT_TRUE(dashr.is_fixed_bit_false(l));
              }
              else if (c[0] == '1')
              {
                ASSERT_TRUE(dashr.is_fixed_bit_true(l));
              }
              else
              {
                ASSERT_FALSE(dashr.is_fixed_bit(l));
              }
            }
            else
            {
              if (c[n - k - l - 1] == 'x')
              {
                ASSERT_FALSE(dashr.is_fixed_bit(l));
              }
              else if (c[n - k - l - 1] == '1')
              {
                ASSERT_TRUE(dashr.is_fixed_bit_true(l));
              }
              else
              {
                assert(c[n - k - l - 1] == '0');
                ASSERT_TRUE(dashr.is_fixed_bit_false(l));
              }
            }
          }
        }
      }
    }
  }
  ASSERT_DEATH_DEBUG(BitVectorDomain(3).bvashr(BitVector(4)),
                     "size\\(\\) == size\\(\\)");
}

TEST_F(TestBitVectorDomain, concat)
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int32_t i = 2; i >= 0; --i)
    {
      for (int32_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        for (int64_t k = 0; k < 3; ++k)
        {
          BitVector bvk           = BitVector::from_si(3, k);
          BitVectorDomain dconcat = d.bvconcat(bvk);
          ASSERT_EQ(dconcat.size(), d.size() + bvk.size());
          for (size_t l = 0, n = d.size(); l < n; ++l)
          {
            if (l >= 3)
            {
              ASSERT_FALSE(dconcat.is_fixed_bit(l));
            }
            else
            {
              ASSERT_TRUE(dconcat.is_fixed_bit(l));
              ASSERT_TRUE(bvk.bit(l) || dconcat.is_fixed_bit_false(l));
              ASSERT_TRUE(!bvk.bit(l) || dconcat.is_fixed_bit_true(l));
            }
          }
        }
      }
    }
  }
}

TEST_F(TestBitVectorDomain, extract)
{
  std::vector<std::string> consts;
  gen_xvalues(3, consts);

  for (const std::string &c : consts)
  {
    for (int64_t i = 2; i >= 0; --i)
    {
      for (int64_t j = i; j >= 0; --j)
      {
        BitVectorDomain d(c);
        BitVectorDomain dext =
            d.bvextract(static_cast<uint64_t>(i), static_cast<uint64_t>(j));
        ASSERT_EQ(dext.size(), i - j + 1);
        for (size_t k = 0, n = d.size(), m = dext.size(); k < m; ++k)
        {
          if (c[n - k - static_cast<uint64_t>(j) - 1] == 'x')
          {
            ASSERT_FALSE(dext.is_fixed_bit(k));
          }
          else if (c[n - k - static_cast<uint64_t>(j) - 1] == '1')
          {
            ASSERT_TRUE(dext.is_fixed_bit_true(k));
          }
          else
          {
            assert(c[n - k - static_cast<uint64_t>(j) - 1] == '0');
            ASSERT_TRUE(dext.is_fixed_bit_false(k));
          }
        }
      }
    }
  }
}

TEST_F(TestBitVectorDomain, str)
{
  ASSERT_EQ(BitVectorDomain(1).str(), "x");
  ASSERT_EQ(BitVectorDomain(10).str(), "xxxxxxxxxx");
  ASSERT_EQ(
      BitVectorDomain(BitVector::from_ui(10, 4), BitVector::from_ui(10, 5))
          .str(),
      "000000010x");
  ASSERT_EQ(BitVectorDomain("00000000").str(), "00000000");
  ASSERT_EQ(BitVectorDomain("11111111").str(), "11111111");
  ASSERT_EQ(BitVectorDomain("10110100").str(), "10110100");
  ASSERT_EQ(BitVectorDomain("x01xxxxx").str(), "x01xxxxx");
  ASSERT_EQ(BitVectorDomain("xxxxxxxx").str(), "xxxxxxxx");
  ASSERT_EQ(BitVectorDomain(BitVector(4, "0000")).str(), "0000");
  ASSERT_EQ(BitVectorDomain(BitVector(8, "1010")).str(), "00001010");
  ASSERT_EQ(BitVectorDomain(4, 0).str(), "0000");
  ASSERT_EQ(BitVectorDomain(8, 5).str(), "00000101");
  ASSERT_EQ(BitVectorDomain(BitVectorDomain(8, 5)).str(), "00000101");
  ASSERT_EQ(BitVectorDomain(BitVector(4, "1000"), BitVector(4, "0111")).str(),
            "ixxx");
  ASSERT_EQ(BitVectorDomain(BitVector(4, "0100"), BitVector(4, "1011")).str(),
            "xixx");
  ASSERT_EQ(BitVectorDomain(BitVector(4, "0110"), BitVector(4, "1001")).str(),
            "xiix");
  ASSERT_EQ(BitVectorDomain(BitVector(4, "1001"), BitVector(4, "0110")).str(),
            "ixxi");
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::ls::test
