/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2021 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "test_bvnode.h"

namespace bzla::ls::test {

class TestBvNodeIsCons : public TestBvNode
{
 protected:
  /**
   * Exercise the consistent-value fallback of the shift operators for target
   * value t = 0 (pos_x = 1, i.e., x is the shift amount).
   */
  template <class T>
  void test_cons_shift_zero_target(uint64_t bw)
  {
    BitVector t = BitVector::mk_zero(bw);
    BitVector first;
    bool not_all_equal = false;
    for (uint32_t i = 0; i < 100; ++i)
    {
      // s = value to be shifted (pos_s = 0), x = shift amount (pos_x = 1) with
      // an unconstrained domain.
      std::unique_ptr<BitVectorNode> op_s(new BitVectorNode(d_rng.get(), bw));
      std::unique_ptr<BitVectorNode> op_x(new BitVectorNode(d_rng.get(), bw));
      T op(d_rng.get(), bw, op_s.get(), op_x.get());
      // t = 0 is always consistent for the shift amount.
      ASSERT_TRUE(op.is_consistent(t, 1));
      BitVector cons = op.consistent_value(t, 1);
      ASSERT_EQ(cons.size(), bw);
      if (i == 0)
      {
        first = cons;
      }
      else if (cons.compare(first) != 0)
      {
        not_all_equal = true;
      }
    }
    ASSERT_TRUE(not_all_equal);
  }
};

TEST_F(TestBvNodeIsCons, add)
{
  test_binary<BitVectorAdd>(IS_CONS, NodeKind::BV_ADD, 0);
  test_binary<BitVectorAdd>(IS_CONS, NodeKind::BV_ADD, 1);
}

TEST_F(TestBvNodeIsCons, and)
{
  test_binary<BitVectorAnd>(IS_CONS, NodeKind::BV_AND, 0);
  test_binary<BitVectorAnd>(IS_CONS, NodeKind::BV_AND, 1);
}

TEST_F(TestBvNodeIsCons, concat)
{
  test_binary<BitVectorConcat>(IS_CONS, NodeKind::BV_CONCAT, 0);
  test_binary<BitVectorConcat>(IS_CONS, NodeKind::BV_CONCAT, 1);
}

TEST_F(TestBvNodeIsCons, eq)
{
  test_binary<BitVectorEq>(IS_CONS, NodeKind::EQ, 0);
  test_binary<BitVectorEq>(IS_CONS, NodeKind::EQ, 1);
}

TEST_F(TestBvNodeIsCons, mul)
{
  test_binary<BitVectorMul>(IS_CONS, NodeKind::BV_MUL, 0);
  test_binary<BitVectorMul>(IS_CONS, NodeKind::BV_MUL, 1);
}

TEST_F(TestBvNodeIsCons, shl)
{
  test_binary<BitVectorShl>(IS_CONS, NodeKind::BV_SHL, 0);
  test_binary<BitVectorShl>(IS_CONS, NodeKind::BV_SHL, 1);
}

TEST_F(TestBvNodeIsCons, shr)
{
  test_binary<BitVectorShr>(IS_CONS, NodeKind::BV_SHR, 0);
  test_binary<BitVectorShr>(IS_CONS, NodeKind::BV_SHR, 1);
}

TEST_F(TestBvNodeIsCons, ashr)
{
  test_binary<BitVectorAshr>(IS_CONS, NodeKind::BV_ASHR, 0);
  test_binary<BitVectorAshr>(IS_CONS, NodeKind::BV_ASHR, 1);
}

TEST_F(TestBvNodeIsCons, shift_cons_zero_target)
{
  // Bit-widths around and beyond the 32/64-bit literal boundaries that the
  // full-range max computation in the consistent-value fallback must handle.
  for (uint64_t bw : {31, 32, 33, 63, 64, 65, 128})
  {
    test_cons_shift_zero_target<BitVectorShl>(bw);
    test_cons_shift_zero_target<BitVectorShr>(bw);
    test_cons_shift_zero_target<BitVectorAshr>(bw);
  }
}

TEST_F(TestBvNodeIsCons, udiv)
{
  test_binary<BitVectorUdiv>(IS_CONS, NodeKind::BV_UDIV, 0);
  test_binary<BitVectorUdiv>(IS_CONS, NodeKind::BV_UDIV, 1);
}

TEST_F(TestBvNodeIsCons, ult)
{
  test_binary<BitVectorUlt>(IS_CONS, NodeKind::BV_ULT, 0);
  test_binary<BitVectorUlt>(IS_CONS, NodeKind::BV_ULT, 1);
}

TEST_F(TestBvNodeIsCons, urem)
{
  test_binary<BitVectorUrem>(IS_CONS, NodeKind::BV_UREM, 0);
  test_binary<BitVectorUrem>(IS_CONS, NodeKind::BV_UREM, 1);
}

TEST_F(TestBvNodeIsCons, slt)
{
  test_binary<BitVectorSlt>(IS_CONS, NodeKind::BV_SLT, 0);
  test_binary<BitVectorSlt>(IS_CONS, NodeKind::BV_SLT, 1);
}

TEST_F(TestBvNodeIsCons, xor)
{
  test_binary<BitVectorXor>(IS_CONS, NodeKind::BV_XOR, 0);
  test_binary<BitVectorXor>(IS_CONS, NodeKind::BV_XOR, 1);
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

}  // namespace bzla::ls::test
