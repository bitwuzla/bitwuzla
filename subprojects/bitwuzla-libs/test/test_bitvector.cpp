#include "bitvector.h"
#include "gmprandstate.h"
#include "gtest/gtest.h"
#include "rng.h"

namespace bzlals {

class TestBitVector : public ::testing::Test
{
 protected:
  void SetUp() override { d_rng.reset(new RNG(1234)); }

  std::unique_ptr<RNG> d_rng;
};

TEST_F(TestBitVector, ctor_dtor)
{
  ASSERT_NO_FATAL_FAILURE(BitVector(1));
  ASSERT_NO_FATAL_FAILURE(BitVector(10));
  ASSERT_NO_FATAL_FAILURE(BitVector(6, "101010"));
  ASSERT_NO_FATAL_FAILURE(BitVector(8, "101010"));
  ASSERT_NO_FATAL_FAILURE(BitVector(16, 1234));
  ASSERT_NO_FATAL_FAILURE(BitVector(16, 123412341234));
  ASSERT_DEATH(BitVector(0), "> 0");
  ASSERT_DEATH(BitVector(2, "101010"), "<= size");
  ASSERT_DEATH(BitVector(6, "123412"), "is_bin_str");
  ASSERT_DEATH(BitVector(0, 1234), "> 0");
}

TEST_F(TestBitVector, ctor_rand)
{
  for (uint32_t size = 1; size <= 64; ++size)
  {
    BitVector bv1(size, *d_rng);
    BitVector bv2(size, *d_rng);
    BitVector bv3(size, *d_rng);
    assert(bv1.compare(bv2) || bv1.compare(bv3) || bv2.compare(bv3));
  }
}

TEST_F(TestBitVector, to_string)
{
  EXPECT_EQ(BitVector(1).to_string(), "0");
  EXPECT_EQ(BitVector(10).to_string(), "0000000000");
  EXPECT_EQ(BitVector(6, "101010").to_string(), "101010");
  EXPECT_EQ(BitVector(8, "101010").to_string(), "00101010");
  EXPECT_EQ(BitVector(16, 1234).to_string(), "0000010011010010");
  EXPECT_EQ(BitVector(16, 123412341234).to_string(), "1110000111110010");
}

TEST_F(TestBitVector, compare)
{
  for (uint32_t i = 0; i < 15; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i);
    ASSERT_EQ(bv1.compare(bv2), 0);
  }

  for (uint32_t i = 0; i < 15 - 1; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i + 1);
    ASSERT_LT(bv1.compare(bv2), 0);
    ASSERT_GT(bv2.compare(bv1), 0);
  }

  for (uint32_t i = 0, j = 0; i < 15; ++i)
  {
    uint32_t k = rand() % 16;
    do
    {
      j = rand() % 16;
    } while (j == k);

    BitVector bv1(4, j);
    BitVector bv2(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.compare(bv2), 0);
      ASSERT_LT(bv2.compare(bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.compare(bv2), 0);
      ASSERT_GT(bv2.compare(bv1), 0);
    }
  }
}

TEST_F(TestBitVector, set_get_flip_bit)
{
  for (uint32_t i = 1; i < 32; ++i)
  {
    BitVector bv(i, *d_rng);
    uint32_t n  = d_rng->pick<uint32_t>(0, i - 1);
    uint32_t v  = bv.get_bit(n);
    uint32_t vv = d_rng->flip_coin() ? 1 : 0;
    bv.set_bit(n, vv);
    EXPECT_EQ(bv.get_bit(n), vv);
    EXPECT_TRUE(v == vv || bv.get_bit(n) == (((~v) << 31) >> 31));
    bv.flip_bit(n);
    EXPECT_EQ(bv.get_bit(n), (((~vv) << 31) >> 31));
  }
}

}  // namespace bzlals
