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

TEST_F(TestBvOpCons, mul)
{
  test_binary<BitVectorMul>(CONS, MUL, 0);
  test_binary<BitVectorMul>(CONS, MUL, 1);
}

TEST_F(TestBvOpCons, shl)
{
  test_binary<BitVectorShl>(CONS, SHL, 0);
  test_binary<BitVectorShl>(CONS, SHL, 1);
}

TEST_F(TestBvOpCons, shr)
{
  test_binary<BitVectorShr>(CONS, SHR, 0);
  test_binary<BitVectorShr>(CONS, SHR, 1);
}

TEST_F(TestBvOpCons, ashr)
{
  test_binary<BitVectorAshr>(CONS, ASHR, 0);
  test_binary<BitVectorAshr>(CONS, ASHR, 1);
}

TEST_F(TestBvOpCons, udiv)
{
  test_binary<BitVectorUdiv>(CONS, UDIV, 0);
  test_binary<BitVectorUdiv>(CONS, UDIV, 1);
}

TEST_F(TestBvOpCons, ult)
{
  test_binary<BitVectorUlt>(CONS, ULT, 0);
  test_binary<BitVectorUlt>(CONS, ULT, 1);
}

}  // namespace test
}  // namespace bzlals
