#include "bv/bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "rewrite/rewriter.h"
#include "rewrite/rewrites_bool.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBool : public TestRewriter
{
 protected:
  void test_elim_rule_bool(Kind kind)
  {
    test_elim_rule(kind, d_nm.mk_bool_type());
  }
};

/* and ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_and_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_EVAL;
  // applies
  Node and0 = d_nm.mk_node(Kind::AND, {d_true, d_true});
  ASSERT_EQ(d_true, d_rewriter.rewrite(and0));

  Node and1 = d_nm.mk_node(Kind::AND, {and0, d_false});
  ASSERT_EQ(d_false, d_rewriter.rewrite(and1));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(and1));
  // does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_const(d_nm.mk_bool_type()), d_false}));
}

/* equal -------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_equal_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_EVAL;
  // applies
  Node equal0 = d_nm.mk_node(Kind::EQUAL, {d_true, d_true});
  ASSERT_EQ(d_true, d_rewriter.rewrite(equal0));
  Node equal0_1 = d_nm.mk_node(Kind::EQUAL, {equal0, d_false});
  ASSERT_EQ(d_false, d_rewriter.rewrite(equal0_1));
  Node equal1 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(BitVector(2, "00")), d_nm.mk_value(BitVector(2, "00"))});
  ASSERT_EQ(d_true, d_rewriter.rewrite(equal1));
  Node equal1_1 = d_nm.mk_node(Kind::EQUAL, {equal1, d_false});
  ASSERT_EQ(d_false, d_rewriter.rewrite(equal1_1));
  Node equal2 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(BitVector(2, "10")), d_nm.mk_value(BitVector(2, "00"))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(equal2));
  Node equal3 =
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, false)),
                    d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, true))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(equal3));
  Node equal4 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(RoundingMode::RNA), d_nm.mk_value(RoundingMode::RNA)});
  ASSERT_EQ(d_true, d_rewriter.rewrite(equal4));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(equal0_1));
  // does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_const(d_nm.mk_bool_type()), d_false}));
}

TEST_F(TestRewriterBool, bool_equal_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_SPECIAL_CONST;
  Node b        = d_nm.mk_const(d_nm.mk_bool_type());
  Node bv4a                      = d_nm.mk_const(d_bv4_type);
  Node bv4b                      = d_nm.mk_const(d_bv4_type);
  ////// special const 0
  {
    //// applies
    Node bv4xor = d_nm.mk_node(Kind::BV_XOR, {bv4a, bv4b});
    Node bv4or =
        d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_AND, {bv4a, bv4b})});
    // lhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_false, b}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4xor}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4or}));
    // rhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {b, d_false}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xor, d_bv4_zero}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4or, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, d_nm.mk_const(d_bv1_type)}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {bv4a, bv4b}));
  }
  ////// special const ones
  {
    //// applies
    Node bv4and  = d_nm.mk_node(Kind::BV_AND, {bv4a, bv4b});
    Node bv4xnor =
        d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_XOR, {bv4a, bv4b})});
    // lhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_true, b}));
    // rhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {b, d_true}));
    // lhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4and}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4xnor}));
    // rhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4and, d_bv4_ones}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xnor, d_bv4_ones}));
  }
}

/* distinct ----------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_distinct_card)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::DISTINCT_CARD;
  Type bv2_type                  = d_nm.mk_bv_type(2);
  Node a                         = d_nm.mk_const(bv2_type);
  Node b                         = d_nm.mk_const(bv2_type);
  Node c                         = d_nm.mk_const(bv2_type);
  Node d                         = d_nm.mk_const(bv2_type);
  Node e                         = d_nm.mk_const(bv2_type);
  // applies
  test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, c, d, e}));
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, d, d}));
}

/* not ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_not_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NOT_EVAL;
  // applies
  Node not0 = d_nm.mk_node(Kind::NOT, {d_false});
  ASSERT_EQ(d_true, d_rewriter.rewrite(not0));

  Node not1 = d_nm.mk_node(Kind::NOT, {not0});
  ASSERT_EQ(d_false, d_rewriter.rewrite(not1));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(not1));
  // does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::NOT, {d_nm.mk_const(d_nm.mk_bool_type())}));
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterBool, bool_distinct_elim)
{
  test_elim_rule_bool(Kind::DISTINCT);
}

TEST_F(TestRewriterBool, bool_implies_elim)
{
  test_elim_rule_bool(Kind::IMPLIES);
}

TEST_F(TestRewriterBool, bool_or_elim) { test_elim_rule_bool(Kind::OR); }

TEST_F(TestRewriterBool, bool_xor_elim) { test_elim_rule_bool(Kind::XOR); }

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test

