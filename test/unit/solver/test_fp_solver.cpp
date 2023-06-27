/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <iostream>

#include "node/node_manager.h"
#include "option/option.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;
using namespace option;

class TestFpSolver : public TestCommon
{
 protected:
  void SetUp() override
  {
    TestCommon::SetUp();
    d_fp16     = d_nm.mk_fp_type(5, 11);
    d_fp_a     = d_nm.mk_const(d_fp16, "a");
    d_fp_b     = d_nm.mk_const(d_fp16, "b");
    d_fp_pzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp16, false));
    d_fp_nzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp16, true));
    d_fp_pinf  = d_nm.mk_value(FloatingPoint::fpinf(d_fp16, false));
    d_fp_ninf  = d_nm.mk_value(FloatingPoint::fpinf(d_fp16, true));
    d_fp_nan   = d_nm.mk_value(FloatingPoint::fpnan(d_fp16));
    d_rm       = d_nm.mk_const(d_nm.mk_rm_type());
  }

  Type d_fp16;
  Node d_fp_a;
  Node d_fp_b;
  Node d_fp_pzero;
  Node d_fp_nzero;
  Node d_fp_pinf;
  Node d_fp_ninf;
  Node d_fp_nan;
  Node d_rm;

  /** The node manager. */
  NodeManager& d_nm = NodeManager::get();
  /** The solver options. */
  Options d_options;
};

TEST_F(TestFpSolver, fp_abs)
{
  SolvingContext ctx = SolvingContext(d_options);

  ctx.assert_formula(d_nm.mk_node(
      Kind::EQUAL,
      {d_fp_a,
       d_nm.mk_node(Kind::FP_ABS, {d_nm.mk_node(Kind::FP_NEG, {d_fp_b})})}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  std::cout << "a: " << ctx.get_value(d_fp_a) << std::endl;
  std::cout << "b: " << ctx.get_value(d_fp_b) << std::endl;
  std::cout << "(fp.abs (fp.neg a)): "
            << ctx.get_value(d_nm.mk_node(
                   Kind::FP_ABS, {d_nm.mk_node(Kind::FP_NEG, {d_fp_a})}))
            << std::endl;
  std::cout << "(fp.abs (fp.neg b)): "
            << ctx.get_value(d_nm.mk_node(
                   Kind::FP_ABS, {d_nm.mk_node(Kind::FP_NEG, {d_fp_b})}))
            << std::endl;

  ctx.assert_formula(d_nm.mk_node(Kind::DISTINCT, {d_fp_b, d_fp_a}));
  ctx.assert_formula(d_nm.mk_node(
      Kind::DISTINCT, {d_fp_b, d_nm.mk_node(Kind::FP_NEG, {d_fp_a})}));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

TEST_F(TestFpSolver, fp_add)
{
  SolvingContext ctx = SolvingContext(d_options);
  ctx.assert_formula(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {d_fp_a})}));
  ctx.assert_formula(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {d_fp_b})}));
  ctx.assert_formula(d_nm.mk_node(
      Kind::EQUAL,
      {d_fp_nan, d_nm.mk_node(Kind::FP_ADD, {d_rm, d_fp_a, d_fp_b})}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  std::cout << "a: " << ctx.get_value(d_fp_a) << std::endl;
  std::cout << "b: " << ctx.get_value(d_fp_b) << std::endl;
  std::cout << "rm: " << ctx.get_value(d_rm) << std::endl;
  std::cout << "(fp.add rm a b): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_ADD, {d_rm, d_fp_a, d_fp_b}))
            << std::endl;
  std::cout << "(fp.sub rm a b): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_SUB, {d_rm, d_fp_a, d_fp_b}))
            << std::endl;
  std::cout << "(fp.div rm a b): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_DIV, {d_rm, d_fp_a, d_fp_b}))
            << std::endl;
  std::cout << "(fp.rem a b): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_REM, {d_fp_a, d_fp_b}))
            << std::endl;
}

TEST_F(TestFpSolver, fp_fma)
{
  SolvingContext ctx = SolvingContext(d_options);
  ctx.assert_formula(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {d_fp_a})}));
  ctx.assert_formula(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_NAN, {d_fp_b})}));
  ctx.assert_formula(d_nm.mk_node(Kind::FP_IS_NORMAL, {d_fp_a}));
  ctx.assert_formula(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {d_fp_b})}));
  ctx.assert_formula(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::FP_FMA, {d_rm, d_fp_a, d_fp_b, d_fp_a}),
       d_nm.mk_node(Kind::FP_ADD,
                    {d_rm,
                     d_nm.mk_node(Kind::FP_MUL, {d_rm, d_fp_a, d_fp_b}),
                     d_fp_a})}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  std::cout << "a: " << ctx.get_value(d_fp_a) << std::endl;
  std::cout << "b: " << ctx.get_value(d_fp_b) << std::endl;
  std::cout << "rm: " << ctx.get_value(d_rm) << std::endl;
  std::cout << "(fp.isSubnormal a): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {d_fp_a}))
            << std::endl;
  std::cout << "(fp.isZero b): "
            << ctx.get_value(d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp_b}))
            << std::endl;
  std::cout << "(fp.fma a b a): "
            << ctx.get_value(
                   d_nm.mk_node(Kind::FP_FMA, {d_rm, d_fp_a, d_fp_b, d_fp_a}))
            << std::endl;
  std::cout << "(fp.fma a b b): "
            << ctx.get_value(
                   d_nm.mk_node(Kind::FP_FMA, {d_rm, d_fp_a, d_fp_b, d_fp_b}))
            << std::endl;
}
}  // namespace bzla::test
