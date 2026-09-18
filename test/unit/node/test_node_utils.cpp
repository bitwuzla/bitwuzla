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
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

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

TEST_F(TestNodeUtils, next_value)
{
  {
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(false)),
              d_nm.mk_value(true));
    ASSERT_TRUE(utils::next_value(d_nm, d_nm.mk_value(true)).is_null());
  }

  {
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(BitVector::from_ui(2, 0))),
              d_nm.mk_value(BitVector::from_ui(2, 1)));
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(BitVector::from_ui(2, 1))),
              d_nm.mk_value(BitVector::from_ui(2, 2)));
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(BitVector::from_ui(2, 2))),
              d_nm.mk_value(BitVector::from_ui(2, 3)));
    ASSERT_TRUE(utils::next_value(d_nm, d_nm.mk_value(BitVector::from_ui(2, 3)))
                    .is_null());
  }

  {
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(RoundingMode::RNA)),
              d_nm.mk_value(RoundingMode::RNE));
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(RoundingMode::RNE)),
              d_nm.mk_value(RoundingMode::RTN));
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(RoundingMode::RTN)),
              d_nm.mk_value(RoundingMode::RTP));
    ASSERT_EQ(utils::next_value(d_nm, d_nm.mk_value(RoundingMode::RTP)),
              d_nm.mk_value(RoundingMode::RTZ));
    ASSERT_TRUE(
        utils::next_value(d_nm, d_nm.mk_value(RoundingMode::RTZ)).is_null());
  }

  {
    Type fp8     = d_nm.mk_fp_type(3, 5);
    Node n       = d_nm.mk_value(FloatingPoint::fpzero(3, 5, false));
    BitVector bv = BitVector::mk_zero(8);

    while (!n.value<FloatingPoint>().fpisnan())
    {
      ASSERT_EQ(n.value<FloatingPoint>().as_bv(), bv);
      bv.flip_bit(bv.size() - 1);
      if (!bv.msb())
      {
        bv.ibvinc();
      }
      n = utils::next_value(d_nm, n);
    }
    n = utils::next_value(d_nm, n);
    ASSERT_TRUE(n.is_null());
  }
}

TEST_F(TestNodeUtils, free_vars)
{
  Type bool_type = d_nm.mk_bool_type();
  Node x         = d_nm.mk_var(bool_type, "x");
  Node y         = d_nm.mk_var(bool_type, "y");

  // A bare variable is free, a constant is not.
  ASSERT_TRUE(utils::free_vars(x));
  ASSERT_FALSE(utils::free_vars(d_a));

  // A quantifier binds its variable.
  Node all_x =
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::AND, {x, d_a})});
  ASSERT_FALSE(utils::free_vars(all_x));

  // Only the bound variable is bound, y stays free.
  Node all_x_y =
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::AND, {x, y})});
  std::unordered_set<Node> fvs;
  ASSERT_TRUE(utils::free_vars(all_x_y, &fvs));
  ASSERT_EQ(fvs, std::unordered_set<Node>{y});

  // x occurs both free and bound: it must be reported free. Determining the
  // bound variables of the whole term in one set would consider it bound.
  Node mixed = d_nm.mk_node(Kind::AND, {x, all_x});
  fvs.clear();
  ASSERT_TRUE(utils::free_vars(mixed, &fvs));
  ASSERT_EQ(fvs, std::unordered_set<Node>{x});

  // The same variable node bound at two nested levels is still closed.
  Node nested = d_nm.mk_node(Kind::FORALL, {x, all_x});
  ASSERT_FALSE(utils::free_vars(nested));

  // `fvs` accumulates across calls and is not cleared.
  fvs.clear();
  utils::free_vars(x, &fvs);
  utils::free_vars(y, &fvs);
  ASSERT_EQ(fvs.size(), 2);
}

TEST_F(TestNodeUtils, substitute)
{
  Node t = d_nm.mk_node(Kind::BV_ADD, {d_a4, d_b4});

  std::unordered_map<Node, Node> substs{{d_a4, d_c4}};
  std::unordered_map<Node, Node> cache;
  ASSERT_EQ(utils::substitute(d_nm, t, substs, cache),
            d_nm.mk_node(Kind::BV_ADD, {d_c4, d_b4}));

  // Without substitutions the node is returned as is.
  std::unordered_map<Node, Node> empty;
  cache.clear();
  ASSERT_EQ(utils::substitute(d_nm, t, empty, cache), t);
}

TEST_F(TestNodeUtils, substitute_follow_substs)
{
  std::unordered_map<Node, Node> substs{{d_a4, d_b4}, {d_b4, d_c4}};
  std::unordered_map<Node, Node> cache;

  // Substitutions are applied to substituted terms.
  ASSERT_EQ(utils::substitute(d_nm, d_a4, substs, cache), d_c4);

  // Substitutions are applied simultaneously.
  cache.clear();
  ASSERT_EQ(utils::substitute(d_nm, d_a4, substs, cache, false), d_b4);
}

TEST_F(TestNodeUtils, substitute_num_substs)
{
  Node t = d_nm.mk_node(Kind::BV_ADD, {d_a4, d_b4});

  std::unordered_map<Node, Node> substs{{d_a4, d_c4}, {d_b4, d_c4}};
  std::unordered_map<Node, Node> cache;
  uint64_t num_substs = 0;
  ASSERT_EQ(utils::substitute(d_nm, t, substs, cache, false, &num_substs),
            d_nm.mk_node(Kind::BV_ADD, {d_c4, d_c4}));
  ASSERT_EQ(num_substs, 2);
}

TEST_F(TestNodeUtils, substitute_shadow)
{
  Node x = d_nm.mk_var(d_bv4_type, "x");
  // (and (= x a4) (forall x (= x b4))), both occurrences of x are the same
  // node but only the first one is free.
  Node bound =
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::EQUAL, {x, d_b4})});
  Node t =
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::EQUAL, {x, d_a4}), bound});

  std::unordered_map<Node, Node> substs{{x, d_c4}};
  std::unordered_map<Node, Node> cache;
  // The binder shadows x, its body is left untouched.
  ASSERT_EQ(utils::substitute(d_nm, t, substs, cache),
            d_nm.mk_node(Kind::AND,
                         {d_nm.mk_node(Kind::EQUAL, {d_c4, d_a4}), bound}));
}

TEST_F(TestNodeUtils, substitute_bound_variable)
{
  Node x = d_nm.mk_var(d_bv4_type, "x");
  Node y = d_nm.mk_var(d_bv4_type, "y");
  // x does not occur free in the quantifier, substituting it is the identity.
  Node q =
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::EQUAL, {x, d_a4})});

  std::unordered_map<Node, Node> substs{{x, d_b4}};
  std::unordered_map<Node, Node> cache;
  ASSERT_EQ(utils::substitute(d_nm, q, substs, cache), q);

  // Only the free occurrences below the binder are substituted, the binder
  // itself is kept.
  Node qy = d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::EQUAL, {x, y})});
  std::unordered_map<Node, Node> substs_xy{{x, d_b4}, {y, d_c4}};
  cache.clear();
  ASSERT_EQ(
      utils::substitute(d_nm, qy, substs_xy, cache),
      d_nm.mk_node(Kind::FORALL, {x, d_nm.mk_node(Kind::EQUAL, {x, d_c4})}));
}

TEST_F(TestNodeUtils, substitute_capture)
{
  Node u = d_nm.mk_var(d_bv4_type, "u");
  Node v = d_nm.mk_var(d_bv4_type, "v");
  // (forall u (= v u)), substituting v with u would capture u.
  Node t = d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::EQUAL, {v, u})});

  std::unordered_map<Node, Node> substs{{v, u}};
  std::unordered_map<Node, Node> cache;
  Node res = utils::substitute(d_nm, t, substs, cache);

  // The binder is renamed, u stays free.
  ASSERT_EQ(res.kind(), Kind::FORALL);
  ASSERT_NE(res[0], u);
  ASSERT_EQ(res[1], d_nm.mk_node(Kind::EQUAL, {u, res[0]}));
  std::unordered_set<Node> fvs;
  ASSERT_TRUE(utils::free_vars(res, &fvs));
  ASSERT_EQ(fvs, std::unordered_set<Node>{u});
}

TEST_F(TestNodeUtils, substitute_capture_vacuous_binder)
{
  Node w = d_nm.mk_var(d_bv4_type, "w");
  Node x = d_nm.mk_var(d_bv4_type, "x");
  // (forall w (= x a4)): w does not occur in the body of the binder.
  Node q =
      d_nm.mk_node(Kind::FORALL, {w, d_nm.mk_node(Kind::EQUAL, {x, d_a4})});

  // Substituting x with a term in which w occurs free must not let the binder
  // capture w, even though renaming w in the body changes nothing.
  Node t = d_nm.mk_node(Kind::BV_ADD, {w, d_a4});
  std::unordered_map<Node, Node> substs{{x, t}};
  std::unordered_map<Node, Node> cache;
  Node res = utils::substitute(d_nm, q, substs, cache);

  ASSERT_EQ(res.kind(), Kind::FORALL);
  ASSERT_NE(res[0], w);
  ASSERT_EQ(res[1], d_nm.mk_node(Kind::EQUAL, {t, d_a4}));
  std::unordered_set<Node> fvs;
  ASSERT_TRUE(utils::free_vars(res, &fvs));
  ASSERT_EQ(fvs, std::unordered_set<Node>{w});
}

TEST_F(TestNodeUtils, substitute_no_capture)
{
  Node u = d_nm.mk_var(d_bv4_type, "u");
  Node v = d_nm.mk_var(d_bv4_type, "v");
  // (and (= v b4) (forall u (= u a4))). Nothing is substituted in the scope of
  // the binder, hence it must not be renamed even though its variable occurs
  // in the range of the substitution map.
  Node q =
      d_nm.mk_node(Kind::FORALL, {u, d_nm.mk_node(Kind::EQUAL, {u, d_a4})});
  Node t = d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::EQUAL, {v, d_b4}), q});

  std::unordered_map<Node, Node> substs{{v, u}};
  std::unordered_map<Node, Node> cache;
  ASSERT_EQ(utils::substitute(d_nm, t, substs, cache),
            d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::EQUAL, {u, d_b4}), q}));
}

}  // namespace bzla::test
