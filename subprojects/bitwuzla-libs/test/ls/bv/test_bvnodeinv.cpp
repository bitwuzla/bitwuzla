#include "test_bvnode.h"

namespace bzla::ls::test {

/* -------------------------------------------------------------------------- */

class TestBvNodeInv : public TestBvNode
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestBvNodeInv, add)
{
  test_binary<BitVectorAdd>(INV, ADD, 0);
  test_binary<BitVectorAdd>(INV, ADD, 1);
}

TEST_F(TestBvNodeInv, and)
{
  test_binary<BitVectorAnd>(INV, AND, 0);
  test_binary<BitVectorAnd>(INV, AND, 1);
  test_binary<BitVectorAnd>(INV, AND, 0, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(INV, AND, 1, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(INV, AND, 0, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorAnd>(INV, AND, 1, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorAnd>(INV, AND, 0, TestBvNode::BoundsKind::BOTH);
  test_binary<BitVectorAnd>(INV, AND, 1, TestBvNode::BoundsKind::BOTH);
}

TEST_F(TestBvNodeInv, concat)
{
  test_binary<BitVectorConcat>(INV, OpKind::CONCAT, 0);
  test_binary<BitVectorConcat>(INV, OpKind::CONCAT, 1);
}

TEST_F(TestBvNodeInv, eq)
{
  test_binary<BitVectorEq>(INV, EQ, 0);
  test_binary<BitVectorEq>(INV, EQ, 1);
}

TEST_F(TestBvNodeInv, mul)
{
  test_binary<BitVectorMul>(INV, MUL, 0);
  test_binary<BitVectorMul>(INV, MUL, 1);
}

TEST_F(TestBvNodeInv, shl)
{
  test_binary<BitVectorShl>(INV, SHL, 0);
  test_binary<BitVectorShl>(INV, SHL, 1);
}

TEST_F(TestBvNodeInv, shr)
{
  test_binary<BitVectorShr>(INV, SHR, 0);
  test_binary<BitVectorShr>(INV, SHR, 1);
}

TEST_F(TestBvNodeInv, ashr)
{
  test_binary<BitVectorAshr>(INV, ASHR, 0);
  test_binary<BitVectorAshr>(INV, ASHR, 1);
}

TEST_F(TestBvNodeInv, slt)
{
  test_binary<BitVectorSlt>(INV, SLT, 0);
  test_binary<BitVectorSlt>(INV, SLT, 1);
  test_binary<BitVectorUlt>(INV, SLT, 0, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, SLT, 1, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, SLT, 0, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, SLT, 1, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, SLT, 0, SIGNED);
  test_binary<BitVectorSlt>(INV, SLT, 1, SIGNED);
  test_binary<BitVectorSlt>(INV, SLT, 0, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(INV, SLT, 1, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(INV, SLT, 0, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, SLT, 1, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, SLT, 0, BOTH);
  test_binary<BitVectorSlt>(INV, SLT, 1, BOTH);
  test_binary<BitVectorSlt>(INV, SLT, 0, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(INV, SLT, 1, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(INV, SLT, 0, BOTH, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, SLT, 1, BOTH, OptimizationKind::SEXT);
}

TEST_F(TestBvNodeInv, udiv)
{
  test_binary<BitVectorUdiv>(INV, UDIV, 0);
  test_binary<BitVectorUdiv>(INV, UDIV, 1);
}

TEST_F(TestBvNodeInv, ult)
{
  test_binary<BitVectorUlt>(INV, ULT, 0);
  test_binary<BitVectorUlt>(INV, ULT, 1);
  test_binary<BitVectorUlt>(INV, ULT, 0, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 1, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 0, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 1, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 0, UNSIGNED);
  test_binary<BitVectorUlt>(INV, ULT, 1, UNSIGNED);
  test_binary<BitVectorUlt>(INV, ULT, 0, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 1, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 0, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 1, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 0, SIGNED);
  test_binary<BitVectorUlt>(INV, ULT, 1, SIGNED);
  test_binary<BitVectorUlt>(INV, ULT, 0, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 1, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 0, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 1, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 0, BOTH);
  test_binary<BitVectorUlt>(INV, ULT, 1, BOTH);
  test_binary<BitVectorUlt>(INV, ULT, 0, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 1, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(INV, ULT, 0, BOTH, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, ULT, 1, BOTH, OptimizationKind::SEXT);
}

TEST_F(TestBvNodeInv, urem)
{
  test_binary<BitVectorUrem>(INV, UREM, 0);
  test_binary<BitVectorUrem>(INV, UREM, 1);
}

TEST_F(TestBvNodeInv, xor)
{
  test_binary<BitVectorXor>(INV, XOR, 0);
  test_binary<BitVectorXor>(INV, XOR, 1);
}

TEST_F(TestBvNodeInv, ite)
{
  test_ite(INV, 0);
  test_ite(INV, 1);
  test_ite(INV, 2);
}

TEST_F(TestBvNodeInv, not ) { test_not(INV); }

TEST_F(TestBvNodeInv, extract) { test_extract(INV); }

TEST_F(TestBvNodeInv, sext) { test_sext(INV); }

}  // namespace bzla::ls::test
