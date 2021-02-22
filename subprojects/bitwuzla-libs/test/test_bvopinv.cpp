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

TEST_F(TestBvOpInv, and)
{
  test_binary<BitVectorAnd>(INV, AND, 0);
  test_binary<BitVectorAnd>(INV, AND, 1);
}

TEST_F(TestBvOpInv, concat)
{
  test_binary<BitVectorConcat>(INV, CONCAT, 0);
  test_binary<BitVectorConcat>(INV, CONCAT, 1);
}

TEST_F(TestBvOpInv, eq)
{
  test_binary<BitVectorEq>(INV, EQ, 0);
  test_binary<BitVectorEq>(INV, EQ, 1);
}

TEST_F(TestBvOpInv, mul)
{
  test_binary<BitVectorMul>(INV, MUL, 0);
  test_binary<BitVectorMul>(INV, MUL, 1);
}

TEST_F(TestBvOpInv, shl)
{
  test_binary<BitVectorShl>(INV, SHL, 0);
  test_binary<BitVectorShl>(INV, SHL, 1);
}

TEST_F(TestBvOpInv, shr)
{
  test_binary<BitVectorShr>(INV, SHR, 0);
  test_binary<BitVectorShr>(INV, SHR, 1);
}

TEST_F(TestBvOpInv, ashr)
{
  test_binary<BitVectorAshr>(INV, ASHR, 0);
  test_binary<BitVectorAshr>(INV, ASHR, 1);
}

TEST_F(TestBvOpInv, slt)
{
  test_binary<BitVectorSlt>(INV, SLT, 0);
  test_binary<BitVectorSlt>(INV, SLT, 1);
}

TEST_F(TestBvOpInv, udiv)
{
  test_binary<BitVectorUdiv>(INV, UDIV, 0);
  test_binary<BitVectorUdiv>(INV, UDIV, 1);
}

TEST_F(TestBvOpInv, ult)
{
  test_binary<BitVectorUlt>(INV, ULT, 0);
  test_binary<BitVectorUlt>(INV, ULT, 1);
}

TEST_F(TestBvOpInv, urem)
{
  test_binary<BitVectorUrem>(INV, UREM, 0);
  test_binary<BitVectorUrem>(INV, UREM, 1);
}

TEST_F(TestBvOpInv, xor)
{
  test_binary<BitVectorXor>(INV, XOR, 0);
  test_binary<BitVectorXor>(INV, XOR, 1);
}

TEST_F(TestBvOpInv, ite)
{
  test_ite(INV, 0);
  test_ite(INV, 1);
  test_ite(INV, 2);
}

}  // namespace test
}  // namespace bzlals
