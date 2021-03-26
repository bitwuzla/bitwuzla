#include "test.h"

namespace bzlals {
namespace test {

class TestBvOpIsEss : public TestBvOp
{
};

TEST_F(TestBvOpIsEss, add)
{
  test_binary<BitVectorAdd>(IS_ESS, ADD, 0);
  test_binary<BitVectorAdd>(IS_ESS, ADD, 1);
}

TEST_F(TestBvOpIsEss, and)
{
  test_binary<BitVectorAnd>(IS_ESS, AND, 0);
  test_binary<BitVectorAnd>(IS_ESS, AND, 1);
}

TEST_F(TestBvOpIsEss, concat)
{
  test_binary<BitVectorConcat>(IS_ESS, CONCAT, 0);
  test_binary<BitVectorConcat>(IS_ESS, CONCAT, 1);
}

TEST_F(TestBvOpIsEss, eq)
{
  test_binary<BitVectorEq>(IS_ESS, EQ, 0);
  test_binary<BitVectorEq>(IS_ESS, EQ, 1);
}

TEST_F(TestBvOpIsEss, mul)
{
  test_binary<BitVectorMul>(IS_ESS, MUL, 0);
  test_binary<BitVectorMul>(IS_ESS, MUL, 1);
}

TEST_F(TestBvOpIsEss, shl)
{
  test_binary<BitVectorShl>(IS_ESS, SHL, 0);
  test_binary<BitVectorShl>(IS_ESS, SHL, 1);
}

TEST_F(TestBvOpIsEss, shr)
{
  test_binary<BitVectorShr>(IS_ESS, SHR, 0);
  test_binary<BitVectorShr>(IS_ESS, SHR, 1);
}

TEST_F(TestBvOpIsEss, ashr)
{
  test_binary<BitVectorAshr>(IS_ESS, ASHR, 0);
  test_binary<BitVectorAshr>(IS_ESS, ASHR, 1);
}

TEST_F(TestBvOpIsEss, udiv)
{
  test_binary<BitVectorUdiv>(IS_ESS, UDIV, 0);
  test_binary<BitVectorUdiv>(IS_ESS, UDIV, 1);
}

TEST_F(TestBvOpIsEss, ult)
{
  test_binary<BitVectorUlt>(IS_ESS, ULT, 0);
  test_binary<BitVectorUlt>(IS_ESS, ULT, 1);
}

TEST_F(TestBvOpIsEss, slt)
{
  test_binary<BitVectorSlt>(IS_ESS, SLT, 0);
  test_binary<BitVectorSlt>(IS_ESS, SLT, 1);
}

TEST_F(TestBvOpIsEss, urem)
{
  test_binary<BitVectorUrem>(IS_ESS, UREM, 0);
  test_binary<BitVectorUrem>(IS_ESS, UREM, 1);
}

TEST_F(TestBvOpIsEss, xor)
{
  test_binary<BitVectorXor>(IS_ESS, XOR, 0);
  test_binary<BitVectorXor>(IS_ESS, XOR, 1);
}

TEST_F(TestBvOpIsEss, ite)
{
  test_ite(IS_ESS, 0);
  test_ite(IS_ESS, 1);
  test_ite(IS_ESS, 2);
}

TEST_F(TestBvOpIsEss, extract) { test_extract(IS_ESS); }

TEST_F(TestBvOpIsEss, sext) { test_sext(IS_ESS); }

}  // namespace test
}  // namespace bzlals
