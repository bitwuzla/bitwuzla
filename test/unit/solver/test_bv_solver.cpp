/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_manager.h"
#include "solving_context.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

class TestBvSolver : public TestCommon
{
 protected:
  option::Options d_options;
};

TEST_F(TestBvSolver, ctor_dtor)
{
  SolvingContext ctx = SolvingContext(d_options);
}

TEST_F(TestBvSolver, solve_empty)
{
  SolvingContext ctx = SolvingContext(d_options);
  ASSERT_EQ(ctx.solve(), Result::SAT);
}

TEST_F(TestBvSolver, solve_true)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);
  ctx.assert_formula(nm.mk_value(true));
  ASSERT_EQ(ctx.solve(), Result::SAT);
}

TEST_F(TestBvSolver, solve_false)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);
  ctx.assert_formula(nm.mk_value(false));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

TEST_F(TestBvSolver, solve_eq1)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(8);
  Node x   = nm.mk_const(bv8);
  Node one = nm.mk_value(BitVector::from_ui(8, 1));

  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {x, one}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_EQ(ctx.get_value(x), one);
}

TEST_F(TestBvSolver, solve_eq2)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(8);
  Node x   = nm.mk_const(bv8);
  Node y   = nm.mk_const(bv8);

  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {x, y}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_EQ(ctx.get_value(x), ctx.get_value(y));
}

TEST_F(TestBvSolver, solve_ne)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(2);
  Node x   = nm.mk_const(bv8);
  Node y   = nm.mk_const(bv8);

  ctx.assert_formula(nm.mk_node(Kind::NOT, {nm.mk_node(Kind::EQUAL, {x, y})}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_NE(ctx.get_value(x), ctx.get_value(y));
}

TEST_F(TestBvSolver, solve_diseq)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(8);
  Node x   = nm.mk_const(bv8);
  Node y   = nm.mk_const(bv8);

  ctx.assert_formula(nm.mk_node(Kind::NOT, {nm.mk_node(Kind::EQUAL, {x, x})}));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

TEST_F(TestBvSolver, solve_add)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8     = nm.mk_bv_type(8);
  Node x       = nm.mk_const(bv8);
  Node y       = nm.mk_const(bv8);
  Node x_add_y = nm.mk_node(Kind::BV_ADD, {x, y});
  Node y_add_x = nm.mk_node(Kind::BV_ADD, {y, x});

  ASSERT_NE(x_add_y, y_add_x);
  ctx.assert_formula(
      nm.mk_node(Kind::NOT, {nm.mk_node(Kind::EQUAL, {x_add_y, y_add_x})}));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

TEST_F(TestBvSolver, solve_mul)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8     = nm.mk_bv_type(4);
  Node x       = nm.mk_const(bv8);
  Node y       = nm.mk_const(bv8);
  Node x_mul_y = nm.mk_node(Kind::BV_MUL, {x, y});
  Node y_mul_x = nm.mk_node(Kind::BV_MUL, {y, x});

  ASSERT_NE(x_mul_y, y_mul_x);
  ctx.assert_formula(
      nm.mk_node(Kind::NOT, {nm.mk_node(Kind::EQUAL, {x_mul_y, y_mul_x})}));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

TEST_F(TestBvSolver, value1)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(8);
  Node x   = nm.mk_const(bv8);

  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_EQ(ctx.get_value(x), nm.mk_value(BitVector::from_ui(8, 0)));
}

TEST_F(TestBvSolver, value2)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(8);
  Node x   = nm.mk_const(bv8);
  Node y   = nm.mk_const(bv8);

  ctx.assert_formula(
      nm.mk_node(Kind::EQUAL, {x, nm.mk_value(BitVector::from_ui(8, 2))}));
  ctx.assert_formula(
      nm.mk_node(Kind::EQUAL, {y, nm.mk_value(BitVector::from_ui(8, 5))}));
  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_EQ(ctx.get_value(x), nm.mk_value(BitVector::from_ui(8, 2)));
  ASSERT_EQ(ctx.get_value(y), nm.mk_value(BitVector::from_ui(8, 5)));
  ASSERT_EQ(ctx.get_value(nm.mk_node(Kind::BV_MUL, {x, y})),
            nm.mk_value(BitVector::from_ui(8, 10)));
}

TEST_F(TestBvSolver, multiple_ctxs)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx1 = SolvingContext(d_options);

  Type bv8 = nm.mk_bv_type(2);
  Node x   = nm.mk_const(bv8);
  Node y   = nm.mk_const(bv8);

  ctx1.assert_formula(nm.mk_node(Kind::NOT, {nm.mk_node(Kind::EQUAL, {x, y})}));
  ASSERT_EQ(ctx1.solve(), Result::SAT);
  ASSERT_NE(ctx1.get_value(x), ctx1.get_value(y));

  SolvingContext ctx2 = SolvingContext(d_options);
  ctx2.assert_formula(nm.mk_node(Kind::EQUAL, {x, ctx1.get_value(x)}));
  ctx2.assert_formula(nm.mk_node(Kind::EQUAL, {y, ctx1.get_value(y)}));
  ASSERT_EQ(ctx2.solve(), Result::SAT);
  ASSERT_EQ(ctx2.get_value(x), ctx1.get_value(x));
  ASSERT_EQ(ctx2.get_value(y), ctx1.get_value(y));
}

TEST_F(TestBvSolver, solve1)
{
  NodeManager& nm = NodeManager::get();
  SolvingContext ctx = SolvingContext(d_options);

  Type bv2 = nm.mk_bv_type(2);
  Node x   = nm.mk_const(bv2);
  Node concat =
      nm.mk_node(Kind::BV_CONCAT, {nm.mk_value(BitVector::from_ui(6, 0)), x});

  ctx.assert_formula(nm.mk_node(
      Kind::EQUAL,
      {concat,
       nm.mk_node(Kind::BV_SHL,
                  {nm.mk_value(BitVector::from_ui(8, 1)), concat})}));
  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

}  // namespace bzla::test
