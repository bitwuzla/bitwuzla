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

#include "preprocess/pass/quant.h"
#include "sat/sat_solver_factory.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassQuant : public TestPreprocessingPass
{
 public:
  TestPassQuant()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_pass(d_env, &d_bm)
  {
    d_bv2 = d_nm.mk_bv_type(2);
  };

 protected:
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  preprocess::pass::PassQuant d_pass;
  Type d_bv2;
};

// Corresponds to test regress/preprocess/quant/alpha6.smt2 and serves as an
// isolated test case (only the quant preprocessing pass is applied, no SAT
// solver involved).
TEST_F(TestPassQuant, alpha_no_merge_of_non_equivalent_quants)
{
  Node body;
  Node g = d_nm.mk_const(d_bv2, "g");
  Node h = d_nm.mk_const(d_bv2, "h");
  Node k = d_nm.mk_const(d_bv2, "k");
  //(define-fun block () Bool
  //  (forall ((o (_ BitVec 2)))
  //    (and (forall ((p (_ BitVec 2)) (q (_ BitVec 2))) (bvule (bvand p q) k))
  //         (bvule o k))))
  Node p = d_nm.mk_var(d_bv2, "p");
  Node q = d_nm.mk_var(d_bv2, "q");
  Node o = d_nm.mk_var(d_bv2, "o");
  body   = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_AND, {p, q}), k});
  Node forall_q  = d_nm.mk_node(Kind::FORALL, {q, body});
  Node forall_pq = d_nm.mk_node(Kind::FORALL, {p, forall_q});
  Node block     = d_nm.mk_node(
      Kind::FORALL,
      {o,
       d_nm.mk_node(Kind::AND,
                    {forall_pq, d_nm.mk_node(Kind::BV_ULE, {o, k})})});

  // (assert (not (forall ((x (_ BitVec 2)))
  //   (and (forall ((v (_ BitVec 2))) (bvule (bvadd v g) x))
  //        block
  //        (bvule x h)))))
  Node x = d_nm.mk_var(d_bv2, "x");
  Node v = d_nm.mk_var(d_bv2, "v");
  body   = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_ADD, {v, g}), x});
  Node forall_v = d_nm.mk_node(Kind::FORALL, {v, body});
  body          = d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::BV_ULE, {x, h}),
                                d_nm.mk_node(Kind::AND, {block, forall_v})});
  Node forall_x = d_nm.mk_node(Kind::FORALL, {x, body});

  // (assert (forall ((x2 (_ BitVec 2)))
  //   (and (forall ((v2 (_ BitVec 2))) (bvule (bvadd v2 g) v2))
  //        block
  //        (bvule x2 h))))
  Node x2 = d_nm.mk_var(d_bv2, "x2");
  Node v2 = d_nm.mk_var(d_bv2, "v2");
  body = d_nm.mk_node(Kind::BV_ULE, {d_nm.mk_node(Kind::BV_ADD, {v2, g}), v2});
  Node forall_v2 = d_nm.mk_node(Kind::FORALL, {v2, body});
  body           = d_nm.mk_node(Kind::AND,
                                {d_nm.mk_node(Kind::BV_ULE, {x2, h}),
                                 d_nm.mk_node(Kind::AND, {block, forall_v2})});
  Node forall_x2 = d_nm.mk_node(Kind::FORALL, {x2, body});

  d_as.push_back(forall_x);
  d_as.push_back(forall_x2);
  ASSERT_EQ(d_as.size(), 2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // forall_x and forall_x2 are not alpha-equivalent and must not be merged.
  ASSERT_NE(assertions[0], assertions[1]);
}

}  // namespace bzla::test
