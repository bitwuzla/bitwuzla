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
