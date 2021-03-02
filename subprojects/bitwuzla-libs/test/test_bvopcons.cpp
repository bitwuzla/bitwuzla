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

TEST_F(TestBvOpCons, concat)
{
  test_binary<BitVectorConcat>(CONS, CONCAT, 0);
  test_binary<BitVectorConcat>(CONS, CONCAT, 1);
}

TEST_F(TestBvOpCons, eq)
{
  test_binary<BitVectorEq>(CONS, EQ, 0);
  test_binary<BitVectorEq>(CONS, EQ, 1);
}

}  // namespace test
}  // namespace bzlals
