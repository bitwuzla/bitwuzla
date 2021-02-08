#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpIsInv : public TestBvOp
{
};

TEST_F(TestBvOpIsInv, add)
{
  test_binary<BitVectorAdd>(IS_INV, ADD, 0, false);
  test_binary<BitVectorAdd>(IS_INV, ADD, 1, false);
  test_binary<BitVectorAdd>(IS_INV, ADD, 0, true);
  test_binary<BitVectorAdd>(IS_INV, ADD, 1, true);
}

TEST_F(TestBvOpIsInv, and)
{
  test_binary<BitVectorAnd>(IS_INV, AND, 0, false);
  test_binary<BitVectorAnd>(IS_INV, AND, 1, false);
  test_binary<BitVectorAnd>(IS_INV, AND, 0, true);
  test_binary<BitVectorAnd>(IS_INV, AND, 1, true);
}

TEST_F(TestBvOpIsInv, concat)
{
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 0, false);
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 1, false);
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 0, true);
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 1, true);
}

TEST_F(TestBvOpIsInv, eq)
{
  test_binary<BitVectorEq>(IS_INV, EQ, 0, false);
  test_binary<BitVectorEq>(IS_INV, EQ, 1, false);
  test_binary<BitVectorEq>(IS_INV, EQ, 0, true);
  test_binary<BitVectorEq>(IS_INV, EQ, 1, true);
}

TEST_F(TestBvOpIsInv, mul)
{
  test_binary<BitVectorMul>(IS_INV, MUL, 0, false);
  test_binary<BitVectorMul>(IS_INV, MUL, 1, false);
  test_binary<BitVectorMul>(IS_INV, MUL, 0, true);
  test_binary<BitVectorMul>(IS_INV, MUL, 1, true);
}

TEST_F(TestBvOpIsInv, shl)
{
  test_binary<BitVectorShl>(IS_INV, SHL, 0, false);
  test_binary<BitVectorShl>(IS_INV, SHL, 1, false);
  test_binary<BitVectorShl>(IS_INV, SHL, 0, true);
  test_binary<BitVectorShl>(IS_INV, SHL, 1, true);
}

TEST_F(TestBvOpIsInv, shr)
{
  test_binary<BitVectorShr>(IS_INV, SHR, 0, false);
  test_binary<BitVectorShr>(IS_INV, SHR, 1, false);
  test_binary<BitVectorShr>(IS_INV, SHR, 0, true);
  test_binary<BitVectorShr>(IS_INV, SHR, 1, true);
}

TEST_F(TestBvOpIsInv, ashr)
{
  test_binary<BitVectorAshr>(IS_INV, ASHR, 0, false);
  test_binary<BitVectorAshr>(IS_INV, ASHR, 1, false);
  test_binary<BitVectorAshr>(IS_INV, ASHR, 0, true);
  test_binary<BitVectorAshr>(IS_INV, ASHR, 1, true);
}

TEST_F(TestBvOpIsInv, udiv)
{
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 0, false);
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 1, false);
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 0, true);
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 1, true);
}

TEST_F(TestBvOpIsInv, ult)
{
  test_binary<BitVectorUlt>(IS_INV, ULT, 0, false);
  test_binary<BitVectorUlt>(IS_INV, ULT, 1, false);
  test_binary<BitVectorUlt>(IS_INV, ULT, 0, true);
  test_binary<BitVectorUlt>(IS_INV, ULT, 1, true);
}

TEST_F(TestBvOpIsInv, slt)
{
  test_binary<BitVectorSlt>(IS_INV, SLT, 0, false);
  test_binary<BitVectorSlt>(IS_INV, SLT, 1, false);
  test_binary<BitVectorSlt>(IS_INV, SLT, 0, true);
  test_binary<BitVectorSlt>(IS_INV, SLT, 1, true);
}

TEST_F(TestBvOpIsInv, urem)
{
  test_binary<BitVectorUrem>(IS_INV, UREM, 0, false);
  test_binary<BitVectorUrem>(IS_INV, UREM, 1, false);
  test_binary<BitVectorUrem>(IS_INV, UREM, 0, true);
  test_binary<BitVectorUrem>(IS_INV, UREM, 1, true);
}

TEST_F(TestBvOpIsInv, xor)
{
  test_binary<BitVectorXor>(IS_INV, XOR, 0, false);
  test_binary<BitVectorXor>(IS_INV, XOR, 1, false);
  test_binary<BitVectorXor>(IS_INV, XOR, 0, true);
  test_binary<BitVectorXor>(IS_INV, XOR, 1, true);
}

TEST_F(TestBvOpIsInv, ite)
{
  test_ite(IS_INV, 0, false);
  test_ite(IS_INV, 1, false);
  test_ite(IS_INV, 2, false);
  test_ite(IS_INV, 0, true);
  test_ite(IS_INV, 1, true);
  test_ite(IS_INV, 2, true);
}

TEST_F(TestBvOpIsInv, extract)
{
  test_extract(IS_INV, false);
  test_extract(IS_INV, true);
}

TEST_F(TestBvOpIsInv, sext)
{
  test_sext(IS_INV, false);
  test_sext(IS_INV, true);
}

}  // namespace test
}  // namespace bzlals
