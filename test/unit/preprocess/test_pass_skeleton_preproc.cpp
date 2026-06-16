/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#if BZLA_USE_CADICAL

#include <gtest/gtest.h>

#include <unordered_set>

#include "option/option.h"
#include "preprocess/pass/skeleton_preproc.h"
#include "sat/sat_solver_factory.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace node;

/* -------------------------------------------------------------------------- */

class TestPassSkeletonPreproc : public TestPreprocessingPass
{
 protected:
  TestPassSkeletonPreproc() : d_sat_factory(d_options)
  {
    d_options.rewrite_level.set(0);
    d_env.reset(new Env(d_nm, d_sat_factory, d_options));
    d_pass.reset(new preprocess::pass::PassSkeletonPreproc(*d_env, &d_bm));
  }

  /**
   * Apply the pass to `assertion` and return the set of assertions added by the
   * pass, i.e., the literals CaDiCaL fixed during skeleton preprocessing.
   */
  std::unordered_set<Node> apply(const Node& assertion)
  {
    AssertionStack as;
    as.push_back(assertion);
    preprocess::AssertionVector assertions(as.view());
    d_pass->apply(assertions);

    // The original assertion stays at index 0, all new assertions are appended.
    std::unordered_set<Node> new_assertions;
    for (size_t i = 1, size = assertions.size(); i < size; ++i)
    {
      new_assertions.insert(assertions[i]);
    }
    return new_assertions;
  }

  Type d_bool = d_nm.mk_bool_type();
  Node d_p    = d_nm.mk_const(d_bool, "p");
  Node d_q    = d_nm.mk_const(d_bool, "q");
  Type d_bv1  = d_nm.mk_bv_type(1);
  Node d_x    = d_nm.mk_const(d_bv1, "x");
  Node d_y    = d_nm.mk_const(d_bv1, "y");
  Node d_one  = d_nm.mk_value(BitVector::mk_true());

  sat::SatSolverFactory d_sat_factory;
  std::unique_ptr<Env> d_env;
  std::unique_ptr<preprocess::pass::PassSkeletonPreproc> d_pass;
};

/* -------------------------------------------------------------------------- */

// Asserting `(and p q)` forces both `p` and `q` to true. CaDiCaL fixes both
// literals during simplification, and the pass must map them back to nodes and
// add `p` and `q` as new assertions.
TEST_F(TestPassSkeletonPreproc, fixed_literals_positive)
{
  Node assertion = d_nm.mk_node(Kind::AND, {d_p, d_q});
  ASSERT_EQ(apply(assertion), (std::unordered_set<Node>{d_p, d_q}));
}

// Asserting `(not (or p q))` forces both `p` and `q` to false. The fixed
// literals are negative, exercising the inversion path: the pass must add the
// inverted nodes `(not p)` and `(not q)`.
TEST_F(TestPassSkeletonPreproc, fixed_literals_negative)
{
  Node assertion =
      d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::OR, {d_p, d_q})});
  ASSERT_EQ(apply(assertion),
            (std::unordered_set<Node>{d_nm.mk_node(Kind::NOT, {d_p}),
                                      d_nm.mk_node(Kind::NOT, {d_q})}));
}

// Asserting `(= (bvand x y) #b1)` forces the 1-bit bit-vectors `x` and `y` to
// 1. The fixed nodes are bit-vectors (not Booleans), so the pass must wrap them
// into equalities and add `(= x #b1)` and `(= y #b1)`.
TEST_F(TestPassSkeletonPreproc, fixed_literals_bv1)
{
  Node assertion = d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {d_x, d_y}), d_one});
  ASSERT_EQ(
      apply(assertion),
      (std::unordered_set<Node>{d_nm.mk_node(Kind::EQUAL, {d_x, d_one}),
                                d_nm.mk_node(Kind::EQUAL, {d_y, d_one})}));
}

// Asserting `(= (bvand (bvnot x) (bvnot y)) #b1)` forces the 1-bit bit-vectors
// `x` and `y` to 0. The fixed bit-vector literals are negative, so the pass
// must invert and wrap them, adding `(= (bvnot x) #b1)` and `(= (bvnot y)
// #b1)`.
TEST_F(TestPassSkeletonPreproc, fixed_literals_bv1_negative)
{
  Node not_x     = d_nm.mk_node(Kind::BV_NOT, {d_x});
  Node not_y     = d_nm.mk_node(Kind::BV_NOT, {d_y});
  Node assertion = d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_AND, {not_x, not_y}), d_one});
  ASSERT_EQ(
      apply(assertion),
      (std::unordered_set<Node>{d_nm.mk_node(Kind::EQUAL, {not_x, d_one}),
                                d_nm.mk_node(Kind::EQUAL, {not_y, d_one})}));
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test

#endif
