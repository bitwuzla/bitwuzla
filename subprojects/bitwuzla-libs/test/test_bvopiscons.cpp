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

TEST_F(TestBvOpIsCons, mul)
{
  test_binary<BitVectorMul>(IS_CONS, MUL, 0, false);
  test_binary<BitVectorMul>(IS_CONS, MUL, 1, false);
  test_binary<BitVectorMul>(IS_CONS, MUL, 0, true);
  test_binary<BitVectorMul>(IS_CONS, MUL, 1, true);
}

TEST_F(TestBvOpIsCons, shl)
{
  test_binary<BitVectorShl>(IS_CONS, SHL, 0, false);
  test_binary<BitVectorShl>(IS_CONS, SHL, 1, false);
  test_binary<BitVectorShl>(IS_CONS, SHL, 0, true);
  test_binary<BitVectorShl>(IS_CONS, SHL, 1, true);
}

TEST_F(TestBvOpIsCons, shr)
{
  test_binary<BitVectorShr>(IS_CONS, SHR, 0, false);
  test_binary<BitVectorShr>(IS_CONS, SHR, 1, false);
  test_binary<BitVectorShr>(IS_CONS, SHR, 0, true);
  test_binary<BitVectorShr>(IS_CONS, SHR, 1, true);
}

TEST_F(TestBvOpIsCons, ashr)
{
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 0, false);
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 1, false);
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 0, true);
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 1, true);
}
}
}
