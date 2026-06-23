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

#include <set>

#include "bv/bitvector.h"
#include "option/option.h"
#include "preprocess/pass/variable_substitution.h"
#include "preprocess/preprocessor.h"
#include "sat/sat_solver_factory.h"
#include "solving_context.h"
#include "test/unit/preprocess/test_preprocess_pass.h"
#include "util/hash.h"

namespace bzla::test {

using namespace preprocess;
using namespace backtrack;
using namespace node;

class TestPassVariableSubstitution : public TestPreprocessingPass
{
 public:
  TestPassVariableSubstitution()
      : d_sat_factory(d_options),
        d_env(d_nm, d_sat_factory),
        d_pass(d_env, &d_bm)
  {
    d_options.rewrite_level.set(0);
    d_options.pp_embedded_constr.set(false);
    d_options.pp_flatten_and.set(false);
    d_options.pp_skeleton_preproc.set(false);
    d_options.pp_normalize.set(false);
  };

 protected:
  option::Options d_options;
  sat::SatSolverFactory d_sat_factory;
  Env d_env;
  preprocess::pass::PassVariableSubstitution d_pass;
};

TEST_F(TestPassVariableSubstitution, subst1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node t  = d_nm.mk_const(d_nm.mk_bool_type(), "t");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, t});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as.size(), 1);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(eq), d_nm.mk_value(true));
}

TEST_F(TestPassVariableSubstitution, subst2)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type());
  Node y  = d_nm.mk_const(d_nm.mk_bool_type());
  Node t  = d_nm.mk_const(d_nm.mk_bool_type());
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, t})});

  d_as.push_back(eq);
  d_as.push_back(di);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  Node expected = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
  ASSERT_EQ(d_as.size(), 2);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], expected);
  ASSERT_EQ(d_pass.process(eq), d_nm.mk_value(true));
  ASSERT_EQ(d_pass.process(di), expected);
}

// Gaussian elimination must descend into an inverted (bvnot) sub-term to
// detect the linear factor. Regression for a bug where the inverted branch
// recursed on nm.invert_node(node) (= ~~node[0]) instead of node[0]: since
// the NodeManager does not cancel double negation, the recursion never
// terminated until the shared bound was exhausted, so no linear term was
// found (and a sibling attempt sharing the bound failed too).
TEST_F(TestPassVariableSubstitution, gauss_inverted_term)
{
  Type bv8   = d_nm.mk_bv_type(8);
  Node x     = d_nm.mk_const(bv8, "x");
  Node s     = d_nm.mk_const(bv8, "s");
  Node t     = d_nm.mk_const(bv8, "t");
  Node three = d_nm.mk_value(BitVector::from_ui(8, 3));
  // ~(3 * x) = (s & t): x is linear only through the inverted wrapper, the
  // right-hand side is non-linear, so the only possible Gaussian elimination
  // is via the inverted left-hand side.
  Node lhs = d_nm.invert_node(d_nm.mk_node(Kind::BV_MUL, {three, x}));
  Node rhs = d_nm.mk_node(Kind::BV_AND, {s, t});
  Node eq  = d_nm.mk_node(Kind::EQUAL, {lhs, rhs});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // x is eliminated, so the defining equation is rewritten to true.
  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
}

TEST_F(TestPassVariableSubstitution, cycle1)
{
  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, x});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(assertions[0], eq);
}

TEST_F(TestPassVariableSubstitution, cycle2)
{
  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq1     = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});
  Node eq2     = d_nm.mk_node(Kind::EQUAL, {y, x_and_y});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(x_and_y);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], y);
}

TEST_F(TestPassVariableSubstitution, cycle3)
{
  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z       = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node x_and_z = d_nm.mk_node(Kind::AND, {x, z});
  Node eq1     = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2     = d_nm.mk_node(Kind::EQUAL, {y, x_and_z});

  d_as.push_back(x_and_z);
  d_as.push_back(eq2);
  d_as.push_back(eq1);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  Node y_and_z = d_nm.mk_node(Kind::AND, {y, z});
  ASSERT_EQ(d_as[0], y_and_z);
  ASSERT_EQ(d_as[1], d_nm.mk_node(Kind::EQUAL, {y, y_and_z}));
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
}

TEST_F(TestPassVariableSubstitution, cycle4)
{
  Node x   = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y   = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z   = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node eq1 = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2 = d_nm.mk_node(Kind::EQUAL, {y, z});
  Node eq3 = d_nm.mk_node(Kind::EQUAL, {z, x});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
}

TEST_F(TestPassVariableSubstitution, cycle5)
{
  Node x   = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y   = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z   = d_nm.mk_const(d_nm.mk_bool_type(), "z");
  Node eq1 = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node eq2 = d_nm.mk_node(Kind::EQUAL, {y, z});
  Node eq3 = d_nm.mk_node(Kind::EQUAL, {z, x});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], d_nm.mk_value(true));

  d_as.push_back(eq3);
  preprocess::AssertionVector assertions2(d_as.view());
  d_pass.apply(assertions);
  ASSERT_EQ(d_as[2], d_nm.mk_value(true));
}

/* --- Incremental tests ---------------------------------------------------- */

TEST_F(TestPassVariableSubstitution, inc1)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Preprocessor& pp = ctx.preprocessor();

  Node x  = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y  = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node t  = d_nm.mk_const(d_nm.mk_bool_type(), "t");
  Node eq = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, t})});

  ctx.assert_formula(eq);
  ctx.push();
  ctx.assert_formula(di);

  ctx.preprocess();
  auto as = ctx.assertions();

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_t = d_nm.invert_node(t);
    ASSERT_EQ(as.size(), 2);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(as[1], d_nm.mk_node(Kind::EQUAL, {y, not_t}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_t, not_t}));
    ASSERT_EQ(pp.process(di),
              d_nm.invert_node(d_nm.mk_node(Kind::EQUAL, {not_t, t})));

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di),
              d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})}));
  }
  else
  {
    Node expected =
        d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {y, t})});
    ASSERT_EQ(as.size(), 2);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(as[1], expected);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di), expected);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(di), expected);
  }
}

TEST_F(TestPassVariableSubstitution, inc2)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_and_y);

  ctx.preprocess();
  auto as = ctx.assertions();

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_y       = d_nm.invert_node(y);
    Node not_y_and_y = d_nm.mk_node(Kind::AND, {not_y, y});
    ASSERT_EQ(as[0], d_nm.invert_node(d_nm.mk_node(Kind::EQUAL, {not_y, y})));
    ASSERT_EQ(as[1], d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(as[2], not_y_and_y);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {not_y, y}));
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
  }
  else
  {
    Node y_and_y = d_nm.mk_node(Kind::AND, {y, y});
    ASSERT_EQ(as[0], di);
    ASSERT_EQ(as[1], eq);
    ASSERT_EQ(as[2], y_and_y);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);

    ctx.pop();
    ctx.preprocess();
    ASSERT_EQ(pp.process(eq), eq);
    ASSERT_EQ(pp.process(x_and_y), x_and_y);
  }
}

TEST_F(TestPassVariableSubstitution, inc3)
{
  SolvingContext ctx(d_nm, d_options, d_sat_factory);
  Preprocessor& pp = ctx.preprocessor();

  Node x       = d_nm.mk_const(d_nm.mk_bool_type(), "x");
  Node y       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node z       = d_nm.mk_const(d_nm.mk_bool_type(), "y");
  Node eq      = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node di      = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::EQUAL, {x, y})});
  Node x_and_y = d_nm.mk_node(Kind::AND, {x, y});
  Node x_and_z = d_nm.mk_node(Kind::AND, {x, z});

  ctx.assert_formula(di);
  ctx.push();
  ctx.assert_formula(eq);
  ctx.assert_formula(x_and_y);
  ctx.push();
  ctx.push();
  ctx.assert_formula(x_and_z);

  ctx.preprocess();
  auto as = ctx.assertions();

  if (d_options.pp_variable_subst_norm_diseq())
  {
    Node not_y       = d_nm.invert_node(y);
    Node not_y_eq_y  = d_nm.mk_node(Kind::EQUAL, {not_y, y});
    Node not_y_and_z = d_nm.mk_node(Kind::AND, {not_y, z});
    Node not_y_and_y = d_nm.mk_node(Kind::AND, {not_y, y});
    ASSERT_EQ(as[0], d_nm.invert_node(not_y_eq_y));
    ASSERT_EQ(as[1], not_y_eq_y);
    ASSERT_EQ(as[2], not_y_and_y);
    ASSERT_EQ(as[3], not_y_and_z);
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);

    ctx.pop();
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);

    ctx.pop();
    ctx.pop();
    ASSERT_EQ(pp.process(eq), not_y_eq_y);
    ASSERT_EQ(pp.process(x_and_y), not_y_and_y);
    ASSERT_EQ(pp.process(x_and_z), not_y_and_z);
  }
  else
  {
    Node y_and_z = d_nm.mk_node(Kind::AND, {y, z});
    Node y_and_y = d_nm.mk_node(Kind::AND, {y, y});
    ASSERT_EQ(as[0], di);
    ASSERT_EQ(as[1], eq);
    ASSERT_EQ(as[2], y_and_y);
    ASSERT_EQ(as[3], y_and_z);
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);
    ASSERT_EQ(pp.process(x_and_z), y_and_z);

    ctx.pop();
    ASSERT_EQ(pp.process(eq), d_nm.mk_node(Kind::EQUAL, {y, y}));
    ASSERT_EQ(pp.process(x_and_y), y_and_y);
    ASSERT_EQ(pp.process(x_and_z), y_and_z);

    ctx.pop();
    ctx.pop();
    ASSERT_EQ(pp.process(eq), eq);
    ASSERT_EQ(pp.process(x_and_y), x_and_y);
    ASSERT_EQ(pp.process(x_and_z), x_and_z);
  }
}

/* --- compute_non_overlapping() tests -------------------------------------- */

using IndicesMap =
    std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>>;
using Range = preprocess::pass::PassVariableSubstitution::Range;

static bool
has_range(const std::vector<Range>& ranges, uint64_t hi, uint64_t lo)
{
  for (const auto& r : ranges)
  {
    if (r.upper == hi && r.lower == lo) return true;
  }
  return false;
}

static const Range*
find_range(const std::vector<Range>& ranges, uint64_t hi, uint64_t lo)
{
  for (const auto& r : ranges)
  {
    if (r.upper == hi && r.lower == lo) return &r;
  }
  return nullptr;
}

// Helper to verify invariants on the result vector
static void
verify_non_overlapping(const std::vector<Range>& result)
{
  for (size_t i = 0; i < result.size(); ++i)
  {
    ASSERT_GE(result[i].upper, result[i].lower) << "Empty range";
    ASSERT_FALSE(result[i].terms.empty()) << "No terms for range";
    for (size_t j = i + 1; j < result.size(); ++j)
    {
      bool overlaps = !(result[i].lower > result[j].upper
                        || result[i].upper < result[j].lower);
      ASSERT_FALSE(overlaps) << "Ranges [" << result[i].upper << ":"
                             << result[i].lower << "] and [" << result[j].upper
                             << ":" << result[j].lower << "] overlap";
    }
  }
}

// Helper to compute the union of bits covered by ranges (input map version)
static std::set<uint64_t>
covered_bits(const IndicesMap& indices)
{
  std::set<uint64_t> bits;
  for (const auto& [range, terms] : indices)
  {
    for (uint64_t b = range.second; b <= range.first; ++b)
    {
      bits.insert(b);
    }
  }
  return bits;
}

// Helper to compute the union of bits covered by ranges (result vector version)
static std::set<uint64_t>
covered_bits(const std::vector<Range>& result)
{
  std::set<uint64_t> bits;
  for (const auto& r : result)
  {
    for (uint64_t b = r.lower; b <= r.upper; ++b)
    {
      bits.insert(b);
    }
  }
  return bits;
}

TEST_F(TestPassVariableSubstitution, cno_no_overlap)
{
  // [7:4] and [3:0] on an 8-bit var - already disjoint
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4}));
  indices[{3, 0}].push_back(d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0}));

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  ASSERT_EQ(result.size(), 2u);
  verify_non_overlapping(result);
}

TEST_F(TestPassVariableSubstitution, cno_identical_ranges)
{
  // [7:4] and [7:4] merge in map (same key)
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4}));
  indices[{7, 4}].push_back(a);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_TRUE(result.empty());
  ASSERT_EQ(result.size(), 0u);
}

TEST_F(TestPassVariableSubstitution, cno_same_upper_s1_wider)
{
  // [7:0] and [7:4] -> [7:4] and [3:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{7, 4}].push_back(a);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

TEST_F(TestPassVariableSubstitution, cno_same_upper_s2_wider)
{
  // [7:4] and [7:0] -> [7:4] and [3:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);
  indices[{7, 0}].push_back(x);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

TEST_F(TestPassVariableSubstitution, cno_same_lower_s1_wider)
{
  // [7:0] and [3:0] -> [7:4] and [3:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{3, 0}].push_back(a);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

TEST_F(TestPassVariableSubstitution, cno_same_lower_s2_wider)
{
  // [3:0] and [7:0] -> [7:4] and [3:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{3, 0}].push_back(a);
  indices[{7, 0}].push_back(x);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

TEST_F(TestPassVariableSubstitution, cno_s1_contains_s2)
{
  // [7:0] and [5:2] -> [7:6], [5:2], [1:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{5, 2}].push_back(a);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 2));
  ASSERT_TRUE(has_range(result, 1, 0));
}

TEST_F(TestPassVariableSubstitution, cno_s2_contains_s1)
{
  // [5:2] and [7:0] -> [7:6], [5:2], [1:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{5, 2}].push_back(a);
  indices[{7, 0}].push_back(x);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 2));
  ASSERT_TRUE(has_range(result, 1, 0));
}

TEST_F(TestPassVariableSubstitution, cno_partial_overlap_s1_higher)
{
  // [7:3] and [5:0] -> [7:6], [5:3], [2:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(5), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(6), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 3}].push_back(a);
  indices[{5, 0}].push_back(b);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 3));
  ASSERT_TRUE(has_range(result, 2, 0));
}

TEST_F(TestPassVariableSubstitution, cno_partial_overlap_s2_higher)
{
  // [5:0] and [7:3] -> [7:6], [5:3], [2:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(5), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(6), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{5, 0}].push_back(b);
  indices[{7, 3}].push_back(a);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 3));
  ASSERT_TRUE(has_range(result, 2, 0));
}

TEST_F(TestPassVariableSubstitution, cno_adjacent)
{
  // [7:4] and [3:0] - adjacent, no overlap
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(4), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);
  indices[{3, 0}].push_back(b);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  ASSERT_EQ(result.size(), 2u);
}

TEST_F(TestPassVariableSubstitution, cno_single_bit_overlap)
{
  // [4:3] and [3:2] covers [4:2], not [7:0] -> empty result
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(2), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(2), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{4, 3}].push_back(a);
  indices[{3, 2}].push_back(b);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_TRUE(result.empty());
  ASSERT_EQ(result.size(), 0u);
}

TEST_F(TestPassVariableSubstitution, cno_single_bit_overlap_full)
{
  // [7:5]+[4:3]+[3:2]+[1:0] covers [7:0] -> splitting of [4:3]+[3:2] works
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(2), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(2), "b");
  Node c   = d_nm.mk_const(d_nm.mk_bv_type(3), "c");
  Node d   = d_nm.mk_const(d_nm.mk_bv_type(2), "d");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 5}].push_back(c);
  indices[{4, 3}].push_back(a);
  indices[{3, 2}].push_back(b);
  indices[{1, 0}].push_back(d);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 4, 4));
  ASSERT_TRUE(has_range(result, 3, 3));
  ASSERT_TRUE(has_range(result, 2, 2));
}

TEST_F(TestPassVariableSubstitution, cno_multiple_overlaps_chain)
{
  // [7:0], [5:2], [3:0] -> iterative splitting
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(4), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{5, 2}].push_back(a);
  indices[{3, 0}].push_back(b);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
}

TEST_F(TestPassVariableSubstitution, cno_full_range_plus_subrange)
{
  // [7:0] and [7:4] -> [7:4], [3:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{7, 4}].push_back(a);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

/* --- Multi-extract compute_non_overlapping() tests ------------------------ */

TEST_F(TestPassVariableSubstitution, cno_three_pairwise_overlapping)
{
  // 16-bit var, [15:0], [11:4], [7:0] -> [15:12], [11:8], [7:4], [3:0]
  Type bv16 = d_nm.mk_bv_type(16);
  Node x    = d_nm.mk_const(bv16, "x");
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(8), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(8), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{15, 0}].push_back(x);
  indices[{11, 4}].push_back(a);
  indices[{7, 0}].push_back(b);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 16, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 15, 12));
  ASSERT_TRUE(has_range(result, 11, 8));
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 0));
}

TEST_F(TestPassVariableSubstitution, cno_cascading_containment)
{
  // 32-bit, [31:0], [23:8], [15:8] -> [31:24], [23:16], [15:8], [7:0]
  Type bv32 = d_nm.mk_bv_type(32);
  Node x    = d_nm.mk_const(bv32, "x");
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(16), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(8), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{31, 0}].push_back(x);
  indices[{23, 8}].push_back(a);
  indices[{15, 8}].push_back(b);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 32, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 31, 24));
  ASSERT_TRUE(has_range(result, 23, 16));
  ASSERT_TRUE(has_range(result, 15, 8));
  ASSERT_TRUE(has_range(result, 7, 0));
}

TEST_F(TestPassVariableSubstitution, cno_four_ranges_staircase)
{
  // 16-bit, [15:10], [12:7], [9:4], [6:0] -> 7 disjoint slices covering [15:0]
  Type bv16 = d_nm.mk_bv_type(16);
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(6), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(6), "b");
  Node c    = d_nm.mk_const(d_nm.mk_bv_type(6), "c");
  Node d    = d_nm.mk_const(d_nm.mk_bv_type(7), "d");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{15, 10}].push_back(a);
  indices[{12, 7}].push_back(b);
  indices[{9, 4}].push_back(c);
  indices[{6, 0}].push_back(d);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 16, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
}

TEST_F(TestPassVariableSubstitution, cno_three_ranges_sharing_upper)
{
  // [7:4], [7:2], [7:0] -> [7:4], [3:2], [1:0]
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(6), "b");
  Node c   = d_nm.mk_const(bv8, "c");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);
  indices[{7, 2}].push_back(b);
  indices[{7, 0}].push_back(c);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 4));
  ASSERT_TRUE(has_range(result, 3, 2));
  ASSERT_TRUE(has_range(result, 1, 0));
}

TEST_F(TestPassVariableSubstitution, cno_contained_plus_disjoint)
{
  // [15:8], [12:10], [7:0] -> [15:13], [12:10], [9:8], [7:0]
  Type bv16 = d_nm.mk_bv_type(16);
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(8), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(3), "b");
  Node c    = d_nm.mk_const(d_nm.mk_bv_type(8), "c");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{15, 8}].push_back(a);
  indices[{12, 10}].push_back(b);
  indices[{7, 0}].push_back(c);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 16, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 15, 13));
  ASSERT_TRUE(has_range(result, 12, 10));
  ASSERT_TRUE(has_range(result, 9, 8));
  ASSERT_TRUE(has_range(result, 7, 0));
}

TEST_F(TestPassVariableSubstitution, cno_wide_64bit)
{
  // 64-bit with [63:0], [63:48], [47:32], [31:16], [15:0]
  Type bv64 = d_nm.mk_bv_type(64);
  Node x    = d_nm.mk_const(bv64, "x");
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(16), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(16), "b");
  Node c    = d_nm.mk_const(d_nm.mk_bv_type(16), "c");
  Node d    = d_nm.mk_const(d_nm.mk_bv_type(16), "d");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{63, 0}].push_back(x);
  indices[{63, 48}].push_back(a);
  indices[{47, 32}].push_back(b);
  indices[{31, 16}].push_back(c);
  indices[{15, 0}].push_back(d);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 64, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 63, 48));
  ASSERT_TRUE(has_range(result, 47, 32));
  ASSERT_TRUE(has_range(result, 31, 16));
  ASSERT_TRUE(has_range(result, 15, 0));
}

TEST_F(TestPassVariableSubstitution, cno_overlap_at_single_bit)
{
  // [5:3]+[3:1]+[3:0] covers [5:0], not [7:0] -> empty result
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(3), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(3), "b");
  Node c   = d_nm.mk_const(d_nm.mk_bv_type(4), "c");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{5, 3}].push_back(a);
  indices[{3, 1}].push_back(b);
  indices[{3, 0}].push_back(c);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_TRUE(result.empty());
  ASSERT_EQ(result.size(), 0u);
}

TEST_F(TestPassVariableSubstitution, cno_overlap_at_single_bit_full)
{
  // [7:6]+[5:3]+[3:1]+[3:0] covers [7:0] -> splitting works
  Type bv8 = d_nm.mk_bv_type(8);
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(3), "a");
  Node b   = d_nm.mk_const(d_nm.mk_bv_type(3), "b");
  Node c   = d_nm.mk_const(d_nm.mk_bv_type(4), "c");
  Node d   = d_nm.mk_const(d_nm.mk_bv_type(2), "d");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 6}].push_back(d);
  indices[{5, 3}].push_back(a);
  indices[{3, 1}].push_back(b);
  indices[{3, 0}].push_back(c);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
}

TEST_F(TestPassVariableSubstitution, cno_progressive_narrowing)
{
  // [31:0], [24:8], [20:12], [16:12]
  Type bv32 = d_nm.mk_bv_type(32);
  Node x    = d_nm.mk_const(bv32, "x");
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(17), "a");
  Node b    = d_nm.mk_const(d_nm.mk_bv_type(9), "b");
  Node c    = d_nm.mk_const(d_nm.mk_bv_type(5), "c");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{31, 0}].push_back(x);
  indices[{24, 8}].push_back(a);
  indices[{20, 12}].push_back(b);
  indices[{16, 12}].push_back(c);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 32, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
}

/* --- process_extracts() via apply() tests --------------------------------- */

TEST_F(TestPassVariableSubstitution, extract_simple_full_coverage)
{
  // 8-bit var x, two non-overlapping extracts equal to values covering full
  // range
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xF));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0x0));

  Node ext_hi = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext_lo = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1    = d_nm.mk_node(Kind::EQUAL, {ext_hi, v1});
  Node eq2    = d_nm.mk_node(Kind::EQUAL, {ext_lo, v2});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  Node concat = d_nm.mk_node(Kind::BV_CONCAT, {v1, v2});
  ASSERT_EQ(substs.at(x), concat);
}

TEST_F(TestPassVariableSubstitution, extract_overlapping)
{
  // 8-bit var x, overlapping extracts equal to values
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(6, 0x3F));
  Node v2  = d_nm.mk_value(BitVector::from_ui(6, 0x00));

  Node ext1 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 2});
  Node ext2 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {5, 0});
  Node eq1  = d_nm.mk_node(Kind::EQUAL, {ext1, v1});
  Node eq2  = d_nm.mk_node(Kind::EQUAL, {ext2, v2});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(substs.at(x).type().bv_size(), 8);
}

TEST_F(TestPassVariableSubstitution, extract_incomplete_no_subst)
{
  // Only upper bits covered -> no substitution for x via extract path
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xA));

  Node ext = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node eq  = d_nm.mk_node(Kind::EQUAL, {ext, v1});

  d_as.push_back(eq);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // x should NOT be substituted (incomplete coverage, lower bits unknown)
  const auto& substs = d_pass.substitutions();
  ASSERT_EQ(substs.find(x), substs.end());
}

TEST_F(TestPassVariableSubstitution, extract_equals_value)
{
  // (= (extract x 7 4) 0b1010) and (= (extract x 3 0) 0b0101)
  Type bv8 = d_nm.mk_bv_type(8);
  Type bv4 = d_nm.mk_bv_type(4);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0b1010));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0b0101));

  Node ext_hi = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext_lo = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1    = d_nm.mk_node(Kind::EQUAL, {ext_hi, v1});
  Node eq2    = d_nm.mk_node(Kind::EQUAL, {ext_lo, v2});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  // Substitution should be a concat of the two values
  Node concat = d_nm.mk_node(Kind::BV_CONCAT, {v1, v2});
  ASSERT_EQ(substs.at(x), concat);
}

TEST_F(TestPassVariableSubstitution, extract_three_non_overlapping)
{
  // 12-bit var, three non-overlapping extracts covering full range with values
  Type bv12 = d_nm.mk_bv_type(12);
  Node x    = d_nm.mk_const(bv12, "x");
  Node v1   = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node v2   = d_nm.mk_value(BitVector::from_ui(4, 0xB));
  Node v3   = d_nm.mk_value(BitVector::from_ui(4, 0xC));

  Node ext1 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {11, 8});
  Node ext2 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext3 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1  = d_nm.mk_node(Kind::EQUAL, {ext1, v1});
  Node eq2  = d_nm.mk_node(Kind::EQUAL, {ext2, v2});
  Node eq3  = d_nm.mk_node(Kind::EQUAL, {ext3, v3});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(substs.at(x).type().bv_size(), 12);
}

TEST_F(TestPassVariableSubstitution, extract_three_overlapping)
{
  // 8-bit var, three overlapping extracts equal to values
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(6, 0x15));
  Node v2  = d_nm.mk_value(BitVector::from_ui(6, 0x2A));
  Node v3  = d_nm.mk_value(BitVector::from_ui(4, 0x5));

  Node ext1 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 2});
  Node ext2 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {5, 0});
  Node ext3 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node eq1  = d_nm.mk_node(Kind::EQUAL, {ext1, v1});
  Node eq2  = d_nm.mk_node(Kind::EQUAL, {ext2, v2});
  Node eq3  = d_nm.mk_node(Kind::EQUAL, {ext3, v3});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(substs.at(x).type().bv_size(), 8);
}

TEST_F(TestPassVariableSubstitution, extract_four_covering_16bit)
{
  // Four extracts covering 16-bit var, each equal to distinct 4-bit constants
  Type bv16 = d_nm.mk_bv_type(16);
  Type bv4  = d_nm.mk_bv_type(4);
  Node x    = d_nm.mk_const(bv16, "x");
  Node c1   = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node c2   = d_nm.mk_value(BitVector::from_ui(4, 0xB));
  Node c3   = d_nm.mk_value(BitVector::from_ui(4, 0xC));
  Node c4   = d_nm.mk_value(BitVector::from_ui(4, 0xD));

  Node ext1 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {15, 12});
  Node ext2 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {11, 8});
  Node ext3 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext4 = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1  = d_nm.mk_node(Kind::EQUAL, {ext1, c1});
  Node eq2  = d_nm.mk_node(Kind::EQUAL, {ext2, c2});
  Node eq3  = d_nm.mk_node(Kind::EQUAL, {ext3, c3});
  Node eq4  = d_nm.mk_node(Kind::EQUAL, {ext4, c4});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);
  d_as.push_back(eq4);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(substs.at(x).type().bv_size(), 16);
}

/* --- Additional compute_non_overlapping() tests --------------------------- */

TEST_F(TestPassVariableSubstitution, cno_single_entry)
{
  // Single range -> no pairs to compare, returns false
  Node a = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_TRUE(result.empty());
  ASSERT_EQ(result.size(), 0u);
}

TEST_F(TestPassVariableSubstitution, cno_multi_terms_split)
{
  // Range [7:0] with 2 terms and [5:2] with 1 term.
  // After splitting into [7:6], [5:2], [1:0], verify term counts.
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node y   = d_nm.mk_const(bv8, "y");
  Node a   = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(x);
  indices[{7, 0}].push_back(y);
  indices[{5, 2}].push_back(a);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 2));
  ASSERT_TRUE(has_range(result, 1, 0));

  // [7:6] should have 2 re-extracted terms from x and y
  ASSERT_EQ(find_range(result, 7, 6)->terms.size(), 2u);
  // [5:2] should have 3 terms: original a + 2 re-extracted from x and y
  ASSERT_EQ(find_range(result, 5, 2)->terms.size(), 3u);
  // [1:0] should have 2 re-extracted terms from x and y
  ASSERT_EQ(find_range(result, 1, 0)->terms.size(), 2u);
}

TEST_F(TestPassVariableSubstitution, cno_extract_term_input)
{
  // Range [7:0] with a BV_EXTRACT term, [5:2] with a plain variable.
  // After split, verify BV_EXTRACT terms are flattened (no nested extracts).
  Type bv8  = d_nm.mk_bv_type(8);
  Type bv10 = d_nm.mk_bv_type(10);
  Node y    = d_nm.mk_const(bv10, "y");
  Node a    = d_nm.mk_const(d_nm.mk_bv_type(4), "a");

  // extract(y, 9, 2) is an 8-bit term
  Node ext_y = d_nm.mk_node(Kind::BV_EXTRACT, {y}, {9, 2});

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 0}].push_back(ext_y);
  indices[{5, 2}].push_back(a);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 2));
  ASSERT_TRUE(has_range(result, 1, 0));

  // Check that re-extracted terms from ext_y are flattened
  const auto* r76 = find_range(result, 7, 6);
  const auto* r10 = find_range(result, 1, 0);
  ASSERT_NE(r76, nullptr);
  ASSERT_NE(r10, nullptr);
  for (const auto& t : r76->terms)
  {
    if (t.kind() == Kind::BV_EXTRACT)
    {
      // Should be extract(y, ...) not extract(extract(y,...), ...)
      ASSERT_EQ(t[0], y) << "Expected flattened extract on y, got nested";
    }
  }
  for (const auto& t : r10->terms)
  {
    if (t.kind() == Kind::BV_EXTRACT)
    {
      ASSERT_EQ(t[0], y) << "Expected flattened extract on y, got nested";
    }
  }
}

TEST_F(TestPassVariableSubstitution, cno_non_zero_lower_overlap)
{
  // [7:4] and [5:2] covers [7:2], not [7:0] -> empty result
  Node a = d_nm.mk_const(d_nm.mk_bv_type(4), "a");
  Node b = d_nm.mk_const(d_nm.mk_bv_type(4), "b");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);
  indices[{5, 2}].push_back(b);

  auto result = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_TRUE(result.empty());
  ASSERT_EQ(result.size(), 0u);
}

TEST_F(TestPassVariableSubstitution, cno_non_zero_lower_overlap_full)
{
  // [7:4]+[5:2]+[1:0] covers [7:0] -> splitting works
  Node a = d_nm.mk_const(d_nm.mk_bv_type(4), "a");
  Node b = d_nm.mk_const(d_nm.mk_bv_type(4), "b");
  Node c = d_nm.mk_const(d_nm.mk_bv_type(2), "c");

  std::unordered_map<std::pair<uint64_t, uint64_t>, std::vector<Node>> indices;
  indices[{7, 4}].push_back(a);
  indices[{5, 2}].push_back(b);
  indices[{1, 0}].push_back(c);

  auto input_bits = covered_bits(indices);
  auto result     = d_pass.compute_non_overlapping(d_nm, 8, indices);
  ASSERT_FALSE(result.empty());
  verify_non_overlapping(result);
  ASSERT_EQ(covered_bits(result), input_bits);
  ASSERT_TRUE(has_range(result, 7, 6));
  ASSERT_TRUE(has_range(result, 5, 4));
  ASSERT_TRUE(has_range(result, 3, 2));
  ASSERT_TRUE(has_range(result, 1, 0));
}

/* --- Additional process_extracts() via apply() tests ---------------------- */

TEST_F(TestPassVariableSubstitution, extract_var_already_substituted)
{
  // Assert (= x y) first (creates regular substitution for x),
  // then extract equalities for x. x should get the regular substitution.
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node y   = d_nm.mk_const(bv8, "y");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0x5));

  Node eq_xy  = d_nm.mk_node(Kind::EQUAL, {x, y});
  Node ext_hi = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext_lo = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1    = d_nm.mk_node(Kind::EQUAL, {ext_hi, v1});
  Node eq2    = d_nm.mk_node(Kind::EQUAL, {ext_lo, v2});

  d_as.push_back(eq_xy);
  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // x should be substituted to y (from the regular equality), not from extracts
  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_EQ(substs.at(x), y);
}

TEST_F(TestPassVariableSubstitution, extract_excluded_variable)
{
  // Exclude x, then assert extract equalities. x should not be substituted.
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0x5));

  d_pass.exclude({x});

  Node ext_hi = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext_lo = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  Node eq1    = d_nm.mk_node(Kind::EQUAL, {ext_hi, v1});
  Node eq2    = d_nm.mk_node(Kind::EQUAL, {ext_lo, v2});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_EQ(substs.find(x), substs.end());
}

TEST_F(TestPassVariableSubstitution, extract_on_rhs)
{
  // (= v1 (extract x 7 4)) and (= v2 (extract x 3 0)) — extract on the RHS
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xF));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0x0));

  Node ext_hi = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4});
  Node ext_lo = d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0});
  // Put extract on RHS of equality
  Node eq1 = d_nm.mk_node(Kind::EQUAL, {v1, ext_hi});
  Node eq2 = d_nm.mk_node(Kind::EQUAL, {v2, ext_lo});

  d_as.push_back(eq1);
  d_as.push_back(eq2);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  Node concat = d_nm.mk_node(Kind::BV_CONCAT, {v1, v2});
  ASSERT_EQ(substs.at(x), concat);
}

TEST_F(TestPassVariableSubstitution, extract_two_independent_vars)
{
  // Two 8-bit vars x and y, each with full extract coverage to distinct values.
  Type bv8 = d_nm.mk_bv_type(8);
  Node x   = d_nm.mk_const(bv8, "x");
  Node y   = d_nm.mk_const(bv8, "y");
  Node v1  = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node v2  = d_nm.mk_value(BitVector::from_ui(4, 0xB));
  Node v3  = d_nm.mk_value(BitVector::from_ui(4, 0xC));
  Node v4  = d_nm.mk_value(BitVector::from_ui(4, 0xD));

  Node eq1 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4}), v1});
  Node eq2 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {3, 0}), v2});
  Node eq3 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {y}, {7, 4}), v3});
  Node eq4 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {y}, {3, 0}), v4});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);
  d_as.push_back(eq4);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  const auto& substs = d_pass.substitutions();
  ASSERT_NE(substs.find(x), substs.end());
  ASSERT_NE(substs.find(y), substs.end());
  ASSERT_EQ(substs.at(x), d_nm.mk_node(Kind::BV_CONCAT, {v1, v2}));
  ASSERT_EQ(substs.at(y), d_nm.mk_node(Kind::BV_CONCAT, {v3, v4}));
}

TEST_F(TestPassVariableSubstitution, extract_partial_coverage_three_of_four)
{
  // 16-bit var with 3 out of 4 quarter-slices covered. No substitution.
  Type bv16 = d_nm.mk_bv_type(16);
  Node x    = d_nm.mk_const(bv16, "x");
  Node v1   = d_nm.mk_value(BitVector::from_ui(4, 0xA));
  Node v2   = d_nm.mk_value(BitVector::from_ui(4, 0xB));
  Node v3   = d_nm.mk_value(BitVector::from_ui(4, 0xC));

  // Cover [15:12], [11:8], [7:4] but NOT [3:0]
  Node eq1 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {15, 12}), v1});
  Node eq2 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {11, 8}), v2});
  Node eq3 = d_nm.mk_node(Kind::EQUAL,
                          {d_nm.mk_node(Kind::BV_EXTRACT, {x}, {7, 4}), v3});

  d_as.push_back(eq1);
  d_as.push_back(eq2);
  d_as.push_back(eq3);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  // x should NOT be substituted (incomplete coverage — [3:0] only has
  // self-extract)
  const auto& substs = d_pass.substitutions();
  ASSERT_EQ(substs.find(x), substs.end());
}

}  // namespace bzla::test
