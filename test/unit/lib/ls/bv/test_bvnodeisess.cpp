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

class TestBvNodeIsEss : public TestBvNode
{
};

TEST_F(TestBvNodeIsEss, add)
{
  test_binary<BitVectorAdd>(IS_ESS, NodeKind::BV_ADD, 0);
  test_binary<BitVectorAdd>(IS_ESS, NodeKind::BV_ADD, 1);
}

TEST_F(TestBvNodeIsEss, and)
{
  test_binary<BitVectorAnd>(IS_ESS, NodeKind::BV_AND, 0);
  test_binary<BitVectorAnd>(IS_ESS, NodeKind::BV_AND, 1);
}

TEST_F(TestBvNodeIsEss, concat)
{
  test_binary<BitVectorConcat>(IS_ESS, NodeKind::BV_CONCAT, 0);
  test_binary<BitVectorConcat>(IS_ESS, NodeKind::BV_CONCAT, 1);
}

TEST_F(TestBvNodeIsEss, eq)
{
  test_binary<BitVectorEq>(IS_ESS, NodeKind::EQ, 0);
  test_binary<BitVectorEq>(IS_ESS, NodeKind::EQ, 1);
}

TEST_F(TestBvNodeIsEss, mul)
{
  test_binary<BitVectorMul>(IS_ESS, NodeKind::BV_MUL, 0);
  test_binary<BitVectorMul>(IS_ESS, NodeKind::BV_MUL, 1);
}

TEST_F(TestBvNodeIsEss, shl)
{
  test_binary<BitVectorShl>(IS_ESS, NodeKind::BV_SHL, 0);
  test_binary<BitVectorShl>(IS_ESS, NodeKind::BV_SHL, 1);
}

TEST_F(TestBvNodeIsEss, shr)
{
  test_binary<BitVectorShr>(IS_ESS, NodeKind::BV_SHR, 0);
  test_binary<BitVectorShr>(IS_ESS, NodeKind::BV_SHR, 1);
}

TEST_F(TestBvNodeIsEss, ashr)
{
  test_binary<BitVectorAshr>(IS_ESS, NodeKind::BV_ASHR, 0);
  test_binary<BitVectorAshr>(IS_ESS, NodeKind::BV_ASHR, 1);
}

TEST_F(TestBvNodeIsEss, udiv)
{
  test_binary<BitVectorUdiv>(IS_ESS, NodeKind::BV_UDIV, 0);
  test_binary<BitVectorUdiv>(IS_ESS, NodeKind::BV_UDIV, 1);
}

TEST_F(TestBvNodeIsEss, ult)
{
  test_binary<BitVectorUlt>(IS_ESS, NodeKind::BV_ULT, 0);
  test_binary<BitVectorUlt>(IS_ESS, NodeKind::BV_ULT, 1);
}

TEST_F(TestBvNodeIsEss, slt)
{
  test_binary<BitVectorSlt>(IS_ESS, NodeKind::BV_SLT, 0);
  test_binary<BitVectorSlt>(IS_ESS, NodeKind::BV_SLT, 1);
}

TEST_F(TestBvNodeIsEss, urem)
{
  test_binary<BitVectorUrem>(IS_ESS, NodeKind::BV_UREM, 0);
  test_binary<BitVectorUrem>(IS_ESS, NodeKind::BV_UREM, 1);
}

TEST_F(TestBvNodeIsEss, xor)
{
  test_binary<BitVectorXor>(IS_ESS, NodeKind::BV_XOR, 0);
  test_binary<BitVectorXor>(IS_ESS, NodeKind::BV_XOR, 1);
}

TEST_F(TestBvNodeIsEss, ite)
{
  test_ite(IS_ESS, 0);
  test_ite(IS_ESS, 1);
  test_ite(IS_ESS, 2);
}

TEST_F(TestBvNodeIsEss, not ) { test_not(IS_ESS); }

TEST_F(TestBvNodeIsEss, extract) { test_extract(IS_ESS); }

TEST_F(TestBvNodeIsEss, sext) { test_sext(IS_ESS); }

}  // namespace bzla::ls::test
