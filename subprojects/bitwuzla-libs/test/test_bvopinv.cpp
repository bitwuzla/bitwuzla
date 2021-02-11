#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpInv : public TestBvOp
{
};

TEST_F(TestBvOpInv, add)
{
  test_binary<BitVectorAdd>(INV, ADD, 0);
  test_binary<BitVectorAdd>(INV, ADD, 1);
}

}  // namespace test
}  // namespace bzlals
