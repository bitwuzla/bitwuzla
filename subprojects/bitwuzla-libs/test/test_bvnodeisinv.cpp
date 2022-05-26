#include "test_ls_common.h"

namespace bzla {
namespace ls {
namespace test {

class TestBvNodeIsInv : public TestBvNode
{
};

TEST_F(TestBvNodeIsInv, add)
{
  test_binary<BitVectorAdd>(IS_INV, ADD, 0);
  test_binary<BitVectorAdd>(IS_INV, ADD, 1);
}

TEST_F(TestBvNodeIsInv, and)
{
  test_binary<BitVectorAnd>(IS_INV, AND, 0);
  test_binary<BitVectorAnd>(IS_INV, AND, 1);
  test_binary<BitVectorAnd>(IS_INV, AND, 0, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(IS_INV, AND, 1, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorAnd>(IS_INV, AND, 0, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorAnd>(IS_INV, AND, 1, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorAnd>(IS_INV, AND, 0, TestBvNode::BoundsKind::BOTH);
  test_binary<BitVectorAnd>(IS_INV, AND, 1, TestBvNode::BoundsKind::BOTH);
}

TEST_F(TestBvNodeIsInv, concat)
{
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 0);
  test_binary<BitVectorConcat>(IS_INV, CONCAT, 1);
}

TEST_F(TestBvNodeIsInv, eq)
{
  test_binary<BitVectorEq>(IS_INV, EQ, 0);
  test_binary<BitVectorEq>(IS_INV, EQ, 1);
}

TEST_F(TestBvNodeIsInv, mul)
{
  test_binary<BitVectorMul>(IS_INV, MUL, 0);
  test_binary<BitVectorMul>(IS_INV, MUL, 1);
}

TEST_F(TestBvNodeIsInv, shl)
{
  test_binary<BitVectorShl>(IS_INV, SHL, 0);
  test_binary<BitVectorShl>(IS_INV, SHL, 1);
}

TEST_F(TestBvNodeIsInv, shr)
{
  test_binary<BitVectorShr>(IS_INV, SHR, 0);
  test_binary<BitVectorShr>(IS_INV, SHR, 1);
}

TEST_F(TestBvNodeIsInv, ashr)
{
  test_binary<BitVectorAshr>(IS_INV, ASHR, 0);
  test_binary<BitVectorAshr>(IS_INV, ASHR, 1);
}

TEST_F(TestBvNodeIsInv, udiv)
{
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 0);
  test_binary<BitVectorUdiv>(IS_INV, UDIV, 1);
}

TEST_F(TestBvNodeIsInv, ult)
{
  test_binary<BitVectorUlt>(IS_INV, ULT, 0);
  test_binary<BitVectorUlt>(IS_INV, ULT, 1);
  test_binary<BitVectorUlt>(IS_INV, ULT, 0, TestBvNode::BoundsKind::UNSIGNED);
  test_binary<BitVectorUlt>(IS_INV, ULT, 1, TestBvNode::BoundsKind::UNSIGNED);
  // test_binary<BitVectorUlt>(IS_INV, ULT, 0, TestBvNode::BoundsKind::SIGNED);
  // test_binary<BitVectorUlt>(IS_INV, ULT, 1, TestBvNode::BoundsKind::SIGNED);
}

TEST_F(TestBvNodeIsInv, slt)
{
  test_binary<BitVectorSlt>(IS_INV, SLT, 0);
  test_binary<BitVectorSlt>(IS_INV, SLT, 1);
  // test_binary<BitVectorSlt>(IS_INV, SLT, 0,
  // TestBvNode::BoundsKind::UNSIGNED); test_binary<BitVectorSlt>(IS_INV, SLT,
  // 1, TestBvNodeIsInv::UNSIGNED);
  test_binary<BitVectorSlt>(IS_INV, SLT, 0, TestBvNode::BoundsKind::SIGNED);
  test_binary<BitVectorSlt>(IS_INV, SLT, 1, TestBvNodeIsInv::SIGNED);
}

TEST_F(TestBvNodeIsInv, urem)
{
  test_binary<BitVectorUrem>(IS_INV, UREM, 0);
  test_binary<BitVectorUrem>(IS_INV, UREM, 1);
}

TEST_F(TestBvNodeIsInv, xor)
{
  test_binary<BitVectorXor>(IS_INV, XOR, 0);
  test_binary<BitVectorXor>(IS_INV, XOR, 1);
}

TEST_F(TestBvNodeIsInv, ite)
{
  test_ite(IS_INV, 0);
  test_ite(IS_INV, 1);
  test_ite(IS_INV, 2);
}

TEST_F(TestBvNodeIsInv, not ) { test_not(IS_INV); }

TEST_F(TestBvNodeIsInv, extract) { test_extract(IS_INV); }

TEST_F(TestBvNodeIsInv, sext) { test_sext(IS_INV); }

}  // namespace test
}  // namespace ls
}  // namespace bzla
