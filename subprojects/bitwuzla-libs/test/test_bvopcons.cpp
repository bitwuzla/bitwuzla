#include "test.h"
namespace bzlals {
namespace test {

class TestBvOpCons : public TestBvOp
{
};

TEST_F(TestBvOpCons, add)
{
  test_binary<BitVectorAdd>(CONS, ADD, 0);
  test_binary<BitVectorAdd>(CONS, ADD, 1);
}

TEST_F(TestBvOpCons, and)
{
  test_binary<BitVectorAnd>(CONS, AND, 0);
  test_binary<BitVectorAnd>(CONS, AND, 1);
}

}  // namespace test
}  // namespace bzlals
