#include "bitvector.h"
#include "gtest/gtest.h"

namespace bzlals {

class TestBitVector : public ::testing::Test
{
};

TEST_F(TestBitVector, ctor_dtor)
{
  BitVector bv1(1);
  BitVector bv10(10);
  BitVector bv1010106(6, "101010");
  BitVector bv1010108(8, "101010");
  ASSERT_DEATH(BitVector(0), "> 0");
  ASSERT_DEATH(BitVector(2, "101010"), "<= size");
}

}  // namespace bzlals
