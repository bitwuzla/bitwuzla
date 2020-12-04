#include "bitvector.h"
#include "gtest/gtest.h"

namespace bzlals {

class TestBitVector : public ::testing::Test
{
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

}  // namespace bzlals
