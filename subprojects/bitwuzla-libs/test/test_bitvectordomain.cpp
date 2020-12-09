#include "bitvector_domain.h"
#include "gmpmpz.h"
#include "gtest/gtest.h"

namespace bzlals {

class TestBitVectorDomain : public ::testing::Test
{
};

TEST_F(TestBitVectorDomain, ctor_dtor)
{
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(1));
  ASSERT_NO_FATAL_FAILURE(BitVectorDomain(10));
  ASSERT_DEATH(BitVectorDomain(0), "> 0");
  ASSERT_DEATH(BitVector(2, "101010"), "<= size");
}

}  // namespace bzlals
