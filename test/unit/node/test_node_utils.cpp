/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewriter.h"
#include "sat/sat_solver_factory.h"

namespace bzla::test {

using namespace bzla::node;

class TestNodeUtils : public ::testing::Test
{
  void SetUp() override
  {
    d_a        = d_nm.mk_const(d_nm.mk_bool_type());
    d_b        = d_nm.mk_const(d_nm.mk_bool_type());
    d_c        = d_nm.mk_const(d_nm.mk_bool_type());
    d_bv4_type = d_nm.mk_bv_type(4);
    d_a4       = d_nm.mk_const(d_bv4_type);
    d_b4       = d_nm.mk_const(d_bv4_type);
    d_c4       = d_nm.mk_const(d_bv4_type);
  }

 protected:
  TestNodeUtils()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_rewriter(d_env.rewriter())
  {
  }

  NodeManager d_nm;
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  Rewriter& d_rewriter;
  Type d_bv4_type;
  Node d_a;
  Node d_b;
  Node d_c;
  Node d_a4;
  Node d_b4;
  Node d_c4;
};

TEST_F(TestNodeUtils, is_bv_sext)
{
  Node res, child;
  RewriteRuleKind kind;
  Node bvsext = d_nm.mk_node(Kind::BV_SIGN_EXTEND, {d_a4}, {3});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_ELIM>::apply(d_rewriter,
                                                               bvsext);
  assert(utils::is_bv_sext(res, child));
  ASSERT_TRUE(utils::is_bv_sext(res, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3}),
                          d_nm.mk_value(BitVector::mk_one(1))}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_one(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3}),
                          d_nm.mk_value(BitVector::mk_zero(1))}),
            d_nm.mk_value(BitVector::mk_zero(3)),
            d_nm.mk_value(BitVector::mk_ones(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_zero(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_zero(3)),
            d_nm.mk_value(BitVector::mk_ones(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_zero(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_FALSE(utils::is_bv_sext(bvsext, child));
  ASSERT_FALSE(utils::is_bv_sext(
      d_nm.mk_node(Kind::BV_ZERO_EXTEND, {d_a4}, {3}), child));
}

// Regression test for the zero-copy indices() span on the indexed-node rebuild
// hot path: rebuild_node() must preserve the kind and indices of indexed
// operators (extracts, extends) and the unique table must dedup the result
// identically regardless of whether the indices are passed as a std::span
// (indices()) or as a std::vector (braced-init-list).
TEST_F(TestNodeUtils, rebuild_indexed)
{
  Node extract = d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {2, 1});
  Node sext    = d_nm.mk_node(Kind::BV_SIGN_EXTEND, {d_a4}, {3});

  // Rebuilding with the same children yields the identical (deduplicated) node.
  ASSERT_EQ(utils::rebuild_node(d_nm, extract, {d_a4}), extract);
  ASSERT_EQ(utils::rebuild_node(d_nm, sext, {d_a4}), sext);

  // Rebuilding with new children preserves kind and indices, and matches the
  // node built directly via the braced-init-list (std::vector) overload.
  Node extract_b = utils::rebuild_node(d_nm, extract, {d_b4});
  ASSERT_EQ(extract_b.kind(), Kind::BV_EXTRACT);
  ASSERT_EQ(extract_b.num_indices(), 2);
  ASSERT_EQ(extract_b.index(0), 2);
  ASSERT_EQ(extract_b.index(1), 1);
  ASSERT_EQ(extract_b, d_nm.mk_node(Kind::BV_EXTRACT, {d_b4}, {2, 1}));

  Node sext_b = utils::rebuild_node(d_nm, sext, {d_b4});
  ASSERT_EQ(sext_b.kind(), Kind::BV_SIGN_EXTEND);
  ASSERT_EQ(sext_b.num_indices(), 1);
  ASSERT_EQ(sext_b.index(0), 3);
  ASSERT_EQ(sext_b, d_nm.mk_node(Kind::BV_SIGN_EXTEND, {d_b4}, {3}));

  // The std::span (indices()) and std::vector mk_node overloads must converge
  // on the same node.
  std::vector<uint64_t> idx{2, 1};
  ASSERT_EQ(d_nm.mk_node(Kind::BV_EXTRACT, {d_c4}, extract.indices()),
            d_nm.mk_node(Kind::BV_EXTRACT, {d_c4}, idx));
}

}  // namespace bzla::test
