#include "test_bvnode.h"

namespace bzla::ls::test {

class TestBvNodeCons : public TestBvNode
{
};

TEST_F(TestBvNodeCons, add)
{
  test_binary<BitVectorAdd>(CONS, ADD, 0);
  test_binary<BitVectorAdd>(CONS, ADD, 1);
}

TEST_F(TestBvNodeCons, and)
{
  test_binary<BitVectorAnd>(CONS, AND, 0);
  test_binary<BitVectorAnd>(CONS, AND, 1);
}

TEST_F(TestBvNodeCons, concat)
{
  test_binary<BitVectorConcat>(CONS, OpKind::CONCAT, 0);
  test_binary<BitVectorConcat>(CONS, OpKind::CONCAT, 1);
}

TEST_F(TestBvNodeCons, eq)
{
  test_binary<BitVectorEq>(CONS, EQ, 0);
  test_binary<BitVectorEq>(CONS, EQ, 1);
}

TEST_F(TestBvNodeCons, mul)
{
  test_binary<BitVectorMul>(CONS, MUL, 0);
  test_binary<BitVectorMul>(CONS, MUL, 1);
}

TEST_F(TestBvNodeCons, shl)
{
  test_binary<BitVectorShl>(CONS, SHL, 0);
  test_binary<BitVectorShl>(CONS, SHL, 1);
}

TEST_F(TestBvNodeCons, shr)
{
  test_binary<BitVectorShr>(CONS, SHR, 0);
  test_binary<BitVectorShr>(CONS, SHR, 1);
}

TEST_F(TestBvNodeCons, ashr)
{
  test_binary<BitVectorAshr>(CONS, ASHR, 0);
  test_binary<BitVectorAshr>(CONS, ASHR, 1);
}

TEST_F(TestBvNodeCons, udiv)
{
  test_binary<BitVectorUdiv>(CONS, UDIV, 0);
  test_binary<BitVectorUdiv>(CONS, UDIV, 1);
}

TEST_F(TestBvNodeCons, ult)
{
  test_binary<BitVectorUlt>(CONS, ULT, 0);
  test_binary<BitVectorUlt>(CONS, ULT, 1);
}

TEST_F(TestBvNodeCons, slt)
{
  test_binary<BitVectorSlt>(CONS, SLT, 0);
  test_binary<BitVectorSlt>(CONS, SLT, 1);
}

TEST_F(TestBvNodeCons, urem)
{
  test_binary<BitVectorUrem>(CONS, UREM, 0);
  test_binary<BitVectorUrem>(CONS, UREM, 1);
}

TEST_F(TestBvNodeCons, xor)
{
  test_binary<BitVectorXor>(CONS, XOR, 0);
  test_binary<BitVectorXor>(CONS, XOR, 1);
}

TEST_F(TestBvNodeCons, ite)
{
  test_ite(CONS, 0);
  test_ite(CONS, 1);
  test_ite(CONS, 2);
}

TEST_F(TestBvNodeCons, not ) { test_not(CONS); }

TEST_F(TestBvNodeCons, extract) { test_extract(CONS); }

TEST_F(TestBvNodeCons, sext) { test_sext(CONS); }

}  // namespace bzla::ls::test
