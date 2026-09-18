/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "backtrack/backtrackable.h"
#include "preprocess/pass/elim_lambda.h"
#include "sat/sat_solver_factory.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassElimLambda : public TestPreprocessingPass
{
 public:
  TestPassElimLambda()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_pass(d_env, &d_bm) {};

 protected:
  Node apply(const Node& assertion)
  {
    d_as.push_back(assertion);
    preprocess::AssertionVector assertions(d_as.view());
    d_pass.apply(assertions);
    return d_as[0];
  }

  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  preprocess::pass::PassElimLambda d_pass;
};

TEST_F(TestPassElimLambda, reduce)
{
  Type bv4 = d_nm.mk_bv_type(4);
  Node a   = d_nm.mk_const(bv4, "a");
  Node b   = d_nm.mk_const(bv4, "b");
  Node v   = d_nm.mk_var(bv4, "v");
  Node l   = d_nm.mk_node(Kind::LAMBDA, {v, d_nm.mk_node(Kind::EQUAL, {v, a})});

  ASSERT_EQ(apply(d_nm.mk_node(Kind::APPLY, {l, b})),
            d_nm.mk_node(Kind::EQUAL, {b, a}));
}

TEST_F(TestPassElimLambda, reduce_nested)
{
  Type bv4 = d_nm.mk_bv_type(4);
  Node a   = d_nm.mk_const(bv4, "a");
  Node v   = d_nm.mk_var(bv4, "v");
  Node w   = d_nm.mk_var(bv4, "w");
  Node l1 = d_nm.mk_node(Kind::LAMBDA, {w, d_nm.mk_node(Kind::BV_ADD, {w, a})});
  // (lambda v (= (l1 v) a))
  Node l2 = d_nm.mk_node(
      Kind::LAMBDA,
      {v, d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::APPLY, {l1, v}), a})});

  ASSERT_EQ(apply(d_nm.mk_node(Kind::APPLY, {l2, a})),
            d_nm.mk_node(Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {a, a}), a}));
}

TEST_F(TestPassElimLambda, reduce_capture)
{
  Type bv4 = d_nm.mk_bv_type(4);
  Node u   = d_nm.mk_var(bv4, "u");
  Node v   = d_nm.mk_var(bv4, "v");
  // (forall u ((lambda v (forall u (= v u))) u))
  //
  // The argument of the application is bound by the outer binder, the binder
  // in the body of the lambda binds the same node. Reducing the application
  // without renaming it yields (forall u (forall u (= u u))), which rewrites
  // to true.
  Node l = d_nm.mk_node(
      Kind::LAMBDA,
      {v, d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::EQUAL, {v, u})})});
  Node res =
      apply(d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::APPLY, {l, u})}));

  ASSERT_EQ(res.kind(), Kind::FORALL);
  ASSERT_EQ(res[0], u);
  ASSERT_EQ(res[1].kind(), Kind::FORALL);
  ASSERT_NE(res[1][0], u);
  ASSERT_EQ(res[1][1], d_nm.mk_node(Kind::EQUAL, {u, res[1][0]}));
}

}  // namespace bzla::test
