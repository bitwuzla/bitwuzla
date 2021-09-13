#include "test_ls_common.h"

namespace bzla {
namespace ls {
namespace test {

class TestBvNodeIsCons : public TestBvNode
{
};

TEST_F(TestBvNodeIsCons, add)
{
  test_binary<BitVectorAdd>(IS_CONS, ADD, 0);
  test_binary<BitVectorAdd>(IS_CONS, ADD, 1);
}

TEST_F(TestBvNodeIsCons, and)
{
  test_binary<BitVectorAnd>(IS_CONS, AND, 0);
  test_binary<BitVectorAnd>(IS_CONS, AND, 1);
}

TEST_F(TestBvNodeIsCons, concat)
{
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 0);
  test_binary<BitVectorConcat>(IS_CONS, CONCAT, 1);
}

TEST_F(TestBvNodeIsCons, eq)
{
  test_binary<BitVectorEq>(IS_CONS, EQ, 0);
  test_binary<BitVectorEq>(IS_CONS, EQ, 1);
}

TEST_F(TestBvNodeIsCons, mul)
{
  test_binary<BitVectorMul>(IS_CONS, MUL, 0);
  test_binary<BitVectorMul>(IS_CONS, MUL, 1);
}

TEST_F(TestBvNodeIsCons, shl)
{
  test_binary<BitVectorShl>(IS_CONS, SHL, 0);
  test_binary<BitVectorShl>(IS_CONS, SHL, 1);
}

TEST_F(TestBvNodeIsCons, shr)
{
  test_binary<BitVectorShr>(IS_CONS, SHR, 0);
  test_binary<BitVectorShr>(IS_CONS, SHR, 1);
}

TEST_F(TestBvNodeIsCons, ashr)
{
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 0);
  test_binary<BitVectorAshr>(IS_CONS, ASHR, 1);
}

TEST_F(TestBvNodeIsCons, udiv)
{
  test_binary<BitVectorUdiv>(IS_CONS, UDIV, 0);
  test_binary<BitVectorUdiv>(IS_CONS, UDIV, 1);
}

TEST_F(TestBvNodeIsCons, ult)
{
  test_binary<BitVectorUlt>(IS_CONS, ULT, 0);
  test_binary<BitVectorUlt>(IS_CONS, ULT, 1);
}

TEST_F(TestBvNodeIsCons, urem)
{
  test_binary<BitVectorUrem>(IS_CONS, UREM, 0);
  test_binary<BitVectorUrem>(IS_CONS, UREM, 1);
}

TEST_F(TestBvNodeIsCons, slt)
{
  test_binary<BitVectorSlt>(IS_CONS, SLT, 0);
  test_binary<BitVectorSlt>(IS_CONS, SLT, 1);
}

TEST_F(TestBvNodeIsCons, xor)
{
  test_binary<BitVectorXor>(IS_CONS, XOR, 0);
  test_binary<BitVectorXor>(IS_CONS, XOR, 1);
}

TEST_F(TestBvNodeIsCons, ite)
{
  test_ite(IS_CONS, 0);
  test_ite(IS_CONS, 1);
  test_ite(IS_CONS, 2);
}

TEST_F(TestBvNodeIsCons, not ) { test_not(IS_CONS); }

TEST_F(TestBvNodeIsCons, extract) { test_extract(IS_CONS); }

TEST_F(TestBvNodeIsCons, sext) { test_sext(IS_CONS); }

}  // namespace test
}  // namespace ls
}  // namespace bzla
