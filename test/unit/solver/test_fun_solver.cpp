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

#include <iostream>

namespace bzla::test {

using namespace node;

class TestFunSolver : public TestCommon
{
};

TEST_F(TestFunSolver, fc1)
{
  option::Options options;
  SolvingContext ctx(options);
  NodeManager& nm = NodeManager::get();

  Type bv_type = nm.mk_bv_type(16);
  Type bool_type = nm.mk_bool_type();
  Node a = nm.mk_const(bv_type);
  Node b = nm.mk_const(bool_type);
  Node c = nm.mk_const(bv_type);
  Node d = nm.mk_const(bool_type);
  Type fun_type = nm.mk_fun_type({bv_type, bool_type, bv_type});
  Node f = nm.mk_const(fun_type);
  Node f_ab = nm.mk_node(Kind::APPLY, {f, a, b});
  Node f_cd = nm.mk_node(Kind::APPLY, {f, c, d});

  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {f_ab, f_cd}));
  ctx.assert_formula(nm.mk_node(Kind::DISTINCT, {a, c}));

  ASSERT_EQ(ctx.solve(), Result::SAT);
  ASSERT_NE(ctx.get_value(a), ctx.get_value(c));
  ASSERT_EQ(ctx.get_value(f_ab), ctx.get_value(f_cd));
  Node f_value = ctx.get_value(f);

// TODO: requires equality handling
//  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {f, f_value}));
//  ASSERT_EQ(ctx.solve(), Result::SAT);
//  ASSERT_EQ(ctx.preprocessor().process(f), f_value);
}

TEST_F(TestFunSolver, fc2)
{
  option::Options options;
  SolvingContext ctx(options);
  NodeManager& nm = NodeManager::get();

  Type bv_type = nm.mk_bv_type(16);
  Type bool_type = nm.mk_bool_type();
  Node a = nm.mk_const(bv_type);
  Node b = nm.mk_const(bool_type);
  Node c = nm.mk_const(bv_type);
  Node d = nm.mk_const(bool_type);
  Type fun_type = nm.mk_fun_type({bv_type, bool_type, bv_type});
  Node f = nm.mk_const(fun_type);
  Node f_ab = nm.mk_node(Kind::APPLY, {f, a, b});
  Node f_cd = nm.mk_node(Kind::APPLY, {f, c, d});

  ctx.assert_formula(nm.mk_node(Kind::DISTINCT, {f_ab, f_cd}));
  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {a, c}));
  ctx.assert_formula(nm.mk_node(Kind::EQUAL, {b, d}));

  ASSERT_EQ(ctx.solve(), Result::UNSAT);
}

}
