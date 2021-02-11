#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpIsInv : public TestBvOp
{
};

TEST_F(TestBvOpIsInv, add)
{
  test_binary<BitVectorAdd>(IS_INV, ADD, 0);
  test_binary<BitVectorAdd>(IS_INV, ADD, 1);
}

TEST_F(TestBvOpIsInv, and)
{
  test_binary<BitVectorAnd>(IS_INV, AND, 0);
  test_binary<BitVectorAnd>(IS_INV, AND, 1);
}

TEST_F(TestBvOpIsInv, concat)
{
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 0);
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 1);
}

TEST_F(TestBvOpIsInv, eq)
{
  test_binary<BitVectorEq>(IS_INV, EQ, 0);
  test_binary<BitVectorEq>(IS_INV, EQ, 1);
}

TEST_F(TestBvOpIsInv, mul)
{
  test_binary<BitVectorMul>(IS_INV, MUL, 0);
  test_binary<BitVectorMul>(IS_INV, MUL, 1);
}

TEST_F(TestBvOpIsInv, shl)
{
  test_binary<BitVectorShl>(IS_INV, SHL, 0);
  test_binary<BitVectorShl>(IS_INV, SHL, 1);
}

TEST_F(TestBvOpIsInv, shr)
{
  test_binary<BitVectorShr>(IS_INV, SHR, 0);
  test_binary<BitVectorShr>(IS_INV, SHR, 1);
}

TEST_F(TestBvOpIsInv, ashr)
{
  test_binary<BitVectorAshr>(IS_INV, ASHR, 0);
  test_binary<BitVectorAshr>(IS_INV, ASHR, 1);
}

TEST_F(TestBvOpIsInv, udiv)
{
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 0);
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 1);
}

TEST_F(TestBvOpIsInv, ult)
{
  test_binary<BitVectorUlt>(IS_INV, ULT, 0);
  test_binary<BitVectorUlt>(IS_INV, ULT, 1);
}

TEST_F(TestBvOpIsInv, slt)
{
  test_binary<BitVectorSlt>(IS_INV, SLT, 0);
  test_binary<BitVectorSlt>(IS_INV, SLT, 1);
}

TEST_F(TestBvOpIsInv, urem)
{
  test_binary<BitVectorUrem>(IS_INV, UREM, 0);
  test_binary<BitVectorUrem>(IS_INV, UREM, 1);
}

TEST_F(TestBvOpIsInv, xor)
{
  test_binary<BitVectorXor>(IS_INV, XOR, 0);
  test_binary<BitVectorXor>(IS_INV, XOR, 1);
}

TEST_F(TestBvOpIsInv, ite)
{
  test_ite(IS_INV, 0);
  test_ite(IS_INV, 1);
  test_ite(IS_INV, 2);
}

TEST_F(TestBvOpIsInv, extract) { test_extract(IS_INV); }

TEST_F(TestBvOpIsInv, sext) { test_sext(IS_INV); }

}  // namespace test
}  // namespace bzlals
