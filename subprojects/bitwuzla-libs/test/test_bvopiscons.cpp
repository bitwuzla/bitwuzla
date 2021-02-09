#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpIsCons : public TestBvOp
{
};

TEST_F(TestBvOpIsCons, add)
{
  test_binary<BitVectorAdd>(IS_CONS, ADD, 0, false);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 1, false);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 0, true);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 1, true);
}

TEST_F(TestBvOpIsCons, and)
{
  test_binary<BitVectorAnd>(IS_CONS, AND, 0, false);
  test_binary<BitVectorAnd>(IS_CONS, AND, 1, false);
  test_binary<BitVectorAnd>(IS_CONS, AND, 0, true);
  test_binary<BitVectorAnd>(IS_CONS, AND, 1, true);
}

TEST_F(TestBvOpIsCons, concat)
{
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 0, false);
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 1, false);
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 0, true);
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 1, true);
}

TEST_F(TestBvOpIsCons, eq)
{
  test_binary<BitVectorEq>(IS_CONS, EQ, 0, false);
  test_binary<BitVectorEq>(IS_CONS, EQ, 1, false);
  test_binary<BitVectorEq>(IS_CONS, EQ, 0, true);
  test_binary<BitVectorEq>(IS_CONS, EQ, 1, true);
}
}
}
