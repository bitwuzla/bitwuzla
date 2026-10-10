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

#include "preprocess/pass/embedded_constraints.h"
#include "sat/sat_solver_factory.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace preprocess;
using namespace node;

class TestPassEmbeddedConstraints : public TestPreprocessingPass
{
 public:
  TestPassEmbeddedConstraints()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_pass(d_env, &d_bm),
        d_view(d_as.view()),
        d_rw(d_env.rewriter()),
        d_k(d_rw.rewrite(
            d_nm.mk_node(Kind::XOR,
                         {d_nm.mk_const(d_nm.mk_bool_type(), "u"),
                          d_nm.mk_const(d_nm.mk_bool_type(), "v")}))),
        d_z(d_nm.mk_const(d_nm.mk_bool_type(), "z")),
        d_e(d_nm.mk_const(d_nm.mk_bool_type(), "e")),
        d_k_and_z(d_rw.rewrite(d_nm.mk_node(Kind::AND, {d_k, d_z})))
  {
  }

 protected:
  /** Apply the pass to the assertions added since the last call. */
  void apply()
  {
    AssertionVector assertions(d_view);
    d_pass.apply(assertions);
    d_view.set_index(d_view.begin() + assertions.size());
  }

  Node mk_or(const Node& a, const Node& b)
  {
    return d_rw.rewrite(d_nm.mk_node(Kind::OR, {a, b}));
  }

  /** @return The rewritten assertion at given index. */
  Node assertion(size_t i) { return d_rw.rewrite(d_as[i]); }

  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  pass::PassEmbeddedConstraints d_pass;
  backtrack::AssertionView& d_view;
  Rewriter& d_rw;
  Node d_k;
  Node d_z;
  /** Created before `k & z` such that `k & z` is not skipped as too old. */
  Node d_e;
  Node d_k_and_z;
};

TEST_F(TestPassEmbeddedConstraints, subst)
{
  Node w = d_nm.mk_const(d_nm.mk_bool_type(), "w");
  d_as.push_back(d_k);
  d_as.push_back(mk_or(d_k_and_z, w));
  apply();
  ASSERT_EQ(assertion(0), d_k);
  ASSERT_EQ(assertion(1), mk_or(d_z, w));
}

TEST_F(TestPassEmbeddedConstraints, inc_new_constraint)
{
  // The children of the first assertion are processed and cached before `k`
  // becomes an embedded constraint.
  Node w1 = d_nm.mk_const(d_nm.mk_bool_type(), "w1");
  Node w2 = d_nm.mk_const(d_nm.mk_bool_type(), "w2");
  d_as.push_back(d_e);
  d_as.push_back(mk_or(d_k_and_z, w1));
  apply();
  ASSERT_EQ(assertion(1), mk_or(d_k_and_z, w1));

  d_as.push_back(d_k);
  d_as.push_back(mk_or(d_k_and_z, w2));
  apply();
  ASSERT_EQ(assertion(3), mk_or(d_z, w2));
  ASSERT_EQ(d_pass.process(d_k_and_z), d_z);
}

TEST_F(TestPassEmbeddedConstraints, inc_pop)
{
  d_as.push_back(d_e);
  apply();
  ASSERT_EQ(d_pass.process(d_k_and_z), d_k_and_z);

  d_bm.push();
  d_as.push();
  d_as.push_back(d_k);
  apply();
  ASSERT_EQ(d_pass.process(d_k_and_z), d_z);

  // Results cached while `k` was an embedded constraint must not be reused.
  d_as.pop();
  d_bm.pop();
  d_view.set_index(d_as.size());
  ASSERT_EQ(d_pass.process(d_k_and_z), d_k_and_z);
}

TEST_F(TestPassEmbeddedConstraints, inc_pop_restore)
{
  const uint64_t& num_substs = d_env.statistics().new_or_get_stat<uint64_t>(
      "preprocess::embedded_constraints::num_substs");
  Node e_and_z = d_rw.rewrite(d_nm.mk_node(Kind::AND, {d_e, d_z}));
  d_as.push_back(d_e);
  apply();
  ASSERT_EQ(d_pass.process(e_and_z), d_z);
  ASSERT_EQ(num_substs, 1);

  // `k` is older than `e`, the cached results are recomputed.
  d_bm.push();
  d_as.push();
  d_as.push_back(d_k);
  apply();
  ASSERT_EQ(d_pass.process(e_and_z), d_z);
  ASSERT_EQ(num_substs, 2);

  // The results of the first call are valid again and reused.
  d_as.pop();
  d_bm.pop();
  d_view.set_index(d_as.size());
  ASSERT_EQ(d_pass.process(e_and_z), d_z);
  ASSERT_EQ(num_substs, 2);
}

}  // namespace bzla::test
