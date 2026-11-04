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

class TestBvNodeCons : public TestBvNode
{
};

TEST_F(TestBvNodeCons, add)
{
  test_binary<BitVectorAdd>(CONS, NodeKind::BV_ADD, 0);
  test_binary<BitVectorAdd>(CONS, NodeKind::BV_ADD, 1);
}

TEST_F(TestBvNodeCons, and)
{
  test_binary<BitVectorAnd>(CONS, NodeKind::BV_AND, 0);
  test_binary<BitVectorAnd>(CONS, NodeKind::BV_AND, 1);
}

TEST_F(TestBvNodeCons, concat)
{
  test_binary<BitVectorConcat>(CONS, NodeKind::BV_CONCAT, 0);
  test_binary<BitVectorConcat>(CONS, NodeKind::BV_CONCAT, 1);
}

TEST_F(TestBvNodeCons, eq)
{
  test_binary<BitVectorEq>(CONS, NodeKind::EQ, 0);
  test_binary<BitVectorEq>(CONS, NodeKind::EQ, 1);
}

TEST_F(TestBvNodeCons, mul)
{
  test_binary<BitVectorMul>(CONS, NodeKind::BV_MUL, 0);
  test_binary<BitVectorMul>(CONS, NodeKind::BV_MUL, 1);
}

TEST_F(TestBvNodeCons, shl)
{
  test_binary<BitVectorShl>(CONS, NodeKind::BV_SHL, 0);
  test_binary<BitVectorShl>(CONS, NodeKind::BV_SHL, 1);
}

TEST_F(TestBvNodeCons, shr)
{
  test_binary<BitVectorShr>(CONS, NodeKind::BV_SHR, 0);
  test_binary<BitVectorShr>(CONS, NodeKind::BV_SHR, 1);
}

TEST_F(TestBvNodeCons, ashr)
{
  test_binary<BitVectorAshr>(CONS, NodeKind::BV_ASHR, 0);
  test_binary<BitVectorAshr>(CONS, NodeKind::BV_ASHR, 1);
}

TEST_F(TestBvNodeCons, udiv)
{
  test_binary<BitVectorUdiv>(CONS, NodeKind::BV_UDIV, 0);
  test_binary<BitVectorUdiv>(CONS, NodeKind::BV_UDIV, 1);
}

TEST_F(TestBvNodeCons, ult)
{
  test_binary<BitVectorUlt>(CONS, NodeKind::BV_ULT, 0);
  test_binary<BitVectorUlt>(CONS, NodeKind::BV_ULT, 1);
}

TEST_F(TestBvNodeCons, slt)
{
  test_binary<BitVectorSlt>(CONS, NodeKind::BV_SLT, 0);
  test_binary<BitVectorSlt>(CONS, NodeKind::BV_SLT, 1);
}

TEST_F(TestBvNodeCons, urem)
{
  test_binary<BitVectorUrem>(CONS, NodeKind::BV_UREM, 0);
  test_binary<BitVectorUrem>(CONS, NodeKind::BV_UREM, 1);
}

TEST_F(TestBvNodeCons, xor)
{
  test_binary<BitVectorXor>(CONS, NodeKind::BV_XOR, 0);
  test_binary<BitVectorXor>(CONS, NodeKind::BV_XOR, 1);
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
