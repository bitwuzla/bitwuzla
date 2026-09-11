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
        d_env(d_nm, d_sat_factory, d_options),
        d_pass(d_env, &d_bm)
  {
    d_bv2 = d_nm.mk_bv_type(2);
  };

 protected:
  Node apply(const Node& assertion)
  {
    d_as.push_back(assertion);
    preprocess::AssertionVector assertions(d_as.view());
    d_pass.apply(assertions);
    return d_as[0];
  }

 protected:
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  preprocess::pass::PassElimLambda d_pass;
  Type d_bv2;
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

TEST_F(TestPassElimLambda, shadowing_quantifier)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node v = d_nm.mk_var(d_bv2, "v");

  // ((lambda v. (forall v. (bvule v c))) d), i.e., the quantifier rebinds
  // (shadows) the variable of the lambda. Note that binding one variable node
  // with more than one binder is not reachable via the parser (which creates
  // a fresh variable per binder), but is not disallowed via the API.
  Node quant =
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})});
  Node app =
      d_nm.mk_node(Kind::APPLY, {d_nm.mk_node(Kind::LAMBDA, {v, quant}), d});

  d_as.push_back(app);
  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // The quantifier binds `v`, thus every occurrence of `v` in its body is
  // bound by the quantifier and must not be substituted with `d`.
  // Note: The pass does not rewrite, it only rebuilds.
  ASSERT_EQ(assertions[0], quant);
}

TEST_F(TestPassElimLambda, shadowing_quantifier_remaining_substitution)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node u = d_nm.mk_var(d_bv2, "u");
  Node v = d_nm.mk_var(d_bv2, "v");

  // ((lambda u. (lambda v. (forall v. (bvule v u)))) c d), i.e., the
  // quantifier shadows `v` but not `u`, which still has to be substituted in
  // its body.
  Node quant =
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, u})});
  Node lambda =
      d_nm.mk_node(Kind::LAMBDA, {u, d_nm.mk_node(Kind::LAMBDA, {v, quant})});
  Node app = d_nm.mk_node(Kind::APPLY, {lambda, c, d});

  d_as.push_back(app);
  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  Node expected =
      d_nm.mk_node(Kind::FORALL, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})});
  ASSERT_EQ(assertions[0], expected);
}

TEST_F(TestPassElimLambda, shadowing_lambda)
{
  Node c = d_nm.mk_const(d_bv2, "c");
  Node d = d_nm.mk_const(d_bv2, "d");
  Node v = d_nm.mk_var(d_bv2, "v");

  // ((lambda v. ((lambda v. (bvule v c)) d)) c), i.e., the inner lambda
  // rebinds (shadows) the variable of the outer lambda.
  Node inner = d_nm.mk_node(
      Kind::APPLY,
      {d_nm.mk_node(Kind::LAMBDA, {v, d_nm.mk_node(Kind::BV_ULE, {v, c})}), d});
  Node app =
      d_nm.mk_node(Kind::APPLY, {d_nm.mk_node(Kind::LAMBDA, {v, inner}), c});

  d_as.push_back(app);
  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(assertions[0], d_nm.mk_node(Kind::BV_ULE, {d, c}));
}

}  // namespace bzla::test
