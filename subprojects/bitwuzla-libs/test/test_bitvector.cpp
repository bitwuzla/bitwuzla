#include "bitvector.h"
#include "gmpmpz.h"
#include "gmprandstate.h"
#include "gtest/gtest.h"
#include "rng.h"

namespace bzlals {

class TestBitVector : public ::testing::Test
{
 protected:
  static constexpr uint32_t N_BITVEC_TESTS = 100000;
  void SetUp() override { d_rng.reset(new RNG(1234)); }

  void test_concat(uint32_t size);
  std::unique_ptr<RNG> d_rng;
};

void
TestBitVector::test_concat(uint32_t size)
{
  for (uint32_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint32_t size1 = d_rng->pick<uint32_t>(1, size - 1);
    uint32_t size2 = size - size1;
    BitVector bv1(size1, *d_rng);
    BitVector bv2(size2, *d_rng);
    BitVector res = bv1.bvconcat(bv2);
    ASSERT_EQ(res.get_size(), size1 + size2);
    uint64_t u1   = bv1.to_uint64();
    uint64_t u2   = bv2.to_uint64();
    uint64_t u    = (u1 << size2) | u2;
    uint64_t ures = res.to_uint64();
    ASSERT_EQ(u, ures);
  }
}

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
  ASSERT_EQ(BitVector(1).to_string(), "0");
  ASSERT_EQ(BitVector(10).to_string(), "0000000000");
  ASSERT_EQ(BitVector(6, "101010").to_string(), "101010");
  ASSERT_EQ(BitVector(8, "101010").to_string(), "00101010");
  ASSERT_EQ(BitVector(16, 1234).to_string(), "0000010011010010");
  ASSERT_EQ(BitVector(16, 123412341234).to_string(), "1110000111110010");
  ASSERT_EQ(BitVector(16, UINT64_MAX).to_string(), "1111111111111111");
}

TEST_F(TestBitVector, to_uint64)
{
  for (uint64_t i = 0; i < N_BITVEC_TESTS; ++i)
  {
    uint64_t x = (d_rng->pick<uint64_t>() << 32) | d_rng->pick<uint64_t>();
    BitVector bv(64, x);
    uint64_t y = bv.to_uint64();
    ASSERT_EQ(x, y);
  }
  ASSERT_NO_FATAL_FAILURE(BitVector(28).to_uint64());
  ASSERT_DEATH(BitVector(128).to_uint64(), "");
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
  ASSERT_DEATH(BitVector(1).compare(BitVector(2)), "");
}

TEST_F(TestBitVector, signed_compare)
{
  for (int32_t i = -8; i < 7; ++i)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i);
    ASSERT_EQ(bv1.signed_compare(bv2), 0);
  }

  for (int32_t i = -8; i < 7 - 1; i++)
  {
    BitVector bv1(4, i);
    BitVector bv2(4, i + 1);
    ASSERT_LT(bv1.signed_compare(bv2), 0);
    ASSERT_GT(bv2.signed_compare(bv1), 0);
  }

  for (int32_t i = 0, j = 0; i < 15; i++)
  {
    /* j <= 0, k <= 0 */
    int32_t k = rand() % 9;
    do
    {
      j = rand() % 9;
    } while (j == k);
    j = -j;
    k = -k;
    BitVector bv1(4, j);
    BitVector bv2(4, k);
    if (j > k)
    {
      ASSERT_GT(bv1.signed_compare(bv2), 0);
      ASSERT_LT(bv2.signed_compare(bv1), 0);
    }
    if (j < k)
    {
      ASSERT_LT(bv1.signed_compare(bv2), 0);
      ASSERT_GT(bv2.signed_compare(bv1), 0);
    }

    {
      /* j <= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 9;
      } while (j == k);
      j = -j;
      BitVector bv1(4, j);
      BitVector bv2(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }

    {
      /* j >= 0, k <= 0 */
      k = rand() % 9;
      do
      {
        j = rand() % 8;
      } while (j == k);
      k = -k;
      BitVector bv1(4, j);
      BitVector bv2(4, k);
      if (j > k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (j < k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }

    {
      /* j >= 0, k >= 0 */
      k = rand() % 8;
      do
      {
        j = rand() % 8;
      } while (j == k);
      BitVector bv1(4, -j);
      BitVector bv2(4, -k);
      if (-j > -k)
      {
        ASSERT_GT(bv1.signed_compare(bv2), 0);
        ASSERT_LT(bv2.signed_compare(bv1), 0);
      }
      if (-j < -k)
      {
        ASSERT_LT(bv1.signed_compare(bv2), 0);
        ASSERT_GT(bv2.signed_compare(bv1), 0);
      }
    }
  }
  ASSERT_DEATH(BitVector(1).signed_compare(BitVector(2)), "");
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
    ASSERT_EQ(bv.get_bit(n), vv);
    ASSERT_TRUE(v == vv || bv.get_bit(n) == (((~v) << 31) >> 31));
    bv.flip_bit(n);
    ASSERT_EQ(bv.get_bit(n), (((~vv) << 31) >> 31));
  }
}

TEST_F(TestBitVector, concat)
{
  test_concat(2);
  test_concat(7);
  test_concat(31);
  test_concat(33);
  test_concat(64);
}

}  // namespace bzlals
