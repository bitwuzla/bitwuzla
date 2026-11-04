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

/* -------------------------------------------------------------------------- */

class TestBvNodeInv : public TestBvNode
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestBvNodeInv, add)
{
  test_binary<BitVectorAdd>(INV, NodeKind::BV_ADD, 0);
  test_binary<BitVectorAdd>(INV, NodeKind::BV_ADD, 1);
}

TEST_F(TestBvNodeInv, and)
{
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 0);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 1);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 0, UNSIGNED);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 1, UNSIGNED);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 0, SIGNED);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 1, SIGNED);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 0, BOTH);
  test_binary<BitVectorAnd>(INV, NodeKind::BV_AND, 1, BOTH);
}

TEST_F(TestBvNodeInv, concat)
{
  test_binary<BitVectorConcat>(INV, NodeKind::BV_CONCAT, 0);
  test_binary<BitVectorConcat>(INV, NodeKind::BV_CONCAT, 1);
}

TEST_F(TestBvNodeInv, eq)
{
  test_binary<BitVectorEq>(INV, NodeKind::EQ, 0);
  test_binary<BitVectorEq>(INV, NodeKind::EQ, 1);
}

TEST_F(TestBvNodeInv, mul)
{
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 0);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 1);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 0, UNSIGNED);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 1, UNSIGNED);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 0, SIGNED);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 0, SIGNED);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 1, BOTH);
  test_binary<BitVectorMul>(INV, NodeKind::BV_MUL, 1, BOTH);
}

TEST_F(TestBvNodeInv, shl)
{
  test_binary<BitVectorShl>(INV, NodeKind::BV_SHL, 0);
  test_binary<BitVectorShl>(INV, NodeKind::BV_SHL, 1);
}

TEST_F(TestBvNodeInv, shr)
{
  test_binary<BitVectorShr>(INV, NodeKind::BV_SHR, 0);
  test_binary<BitVectorShr>(INV, NodeKind::BV_SHR, 1);
}

TEST_F(TestBvNodeInv, ashr)
{
  test_binary<BitVectorAshr>(INV, NodeKind::BV_ASHR, 0);
  test_binary<BitVectorAshr>(INV, NodeKind::BV_ASHR, 1);
}

TEST_F(TestBvNodeInv, slt)
{
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 0);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 1);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_SLT, 0, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_SLT, 1, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_SLT, 0, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_SLT, 1, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 0, UNSIGNED);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 1, UNSIGNED);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 0, SIGNED);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 1, SIGNED);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 0, BOTH);
  test_binary<BitVectorSlt>(INV, NodeKind::BV_SLT, 1, BOTH);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 0, BOTH, OptimizationKind::SEXT);
  test_binary<BitVectorSlt>(
      INV, NodeKind::BV_SLT, 1, BOTH, OptimizationKind::SEXT);
}

TEST_F(TestBvNodeInv, udiv)
{
  test_binary<BitVectorUdiv>(INV, NodeKind::BV_UDIV, 0);
  test_binary<BitVectorUdiv>(INV, NodeKind::BV_UDIV, 1);
}

TEST_F(TestBvNodeInv, ult)
{
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 0);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 1);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, NONE, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, NONE, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 0, UNSIGNED);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 1, UNSIGNED);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, UNSIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, UNSIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 0, SIGNED);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 1, SIGNED);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, SIGNED, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, SIGNED, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 0, BOTH);
  test_binary<BitVectorUlt>(INV, NodeKind::BV_ULT, 1, BOTH);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, BOTH, OptimizationKind::CONCAT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 0, BOTH, OptimizationKind::SEXT);
  test_binary<BitVectorUlt>(
      INV, NodeKind::BV_ULT, 1, BOTH, OptimizationKind::SEXT);
}

TEST_F(TestBvNodeInv, urem)
{
  test_binary<BitVectorUrem>(INV, NodeKind::BV_UREM, 0);
  test_binary<BitVectorUrem>(INV, NodeKind::BV_UREM, 1);
}

TEST_F(TestBvNodeInv, xor)
{
  test_binary<BitVectorXor>(INV, NodeKind::BV_XOR, 0);
  test_binary<BitVectorXor>(INV, NodeKind::BV_XOR, 1);
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
