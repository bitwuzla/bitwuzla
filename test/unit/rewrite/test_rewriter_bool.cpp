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
  void SetUp() override
  {
    TestRewriter::SetUp();
    d_b    = d_nm.mk_const(d_nm.mk_bool_type());
    d_bv1a = d_nm.mk_const(d_bv1_type);
    d_bv4a = d_nm.mk_const(d_bv4_type);
    d_bv4b = d_nm.mk_const(d_bv4_type);
  }
  void test_elim_rule_bool(Kind kind)
  {
    test_elim_rule(kind, d_nm.mk_bool_type());
  }
  Node d_b;
  Node d_bv1a;
  Node d_bv4a;
  Node d_bv4b;
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
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_b, d_false}));
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
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_false}));
}

TEST_F(TestRewriterBool, bool_equal_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    Node bv4xor = d_nm.mk_node(Kind::BV_XOR, {d_bv4a, d_bv4b});
    Node bv4or  = d_nm.mk_node(Kind::BV_NOT,
                              {d_nm.mk_node(Kind::BV_AND, {d_bv4a, d_bv4b})});
    // lhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_false, d_b}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4xor}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4or}));
    // rhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_false}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xor, d_bv4_zero}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4or, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, d_bv1a}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_bv4b}));
  }
  ////// special const ones
  {
    //// applies
    Node bv4and  = d_nm.mk_node(Kind::BV_AND, {d_bv4a, d_bv4b});
    Node bv4xnor = d_nm.mk_node(Kind::BV_XNOR, {d_bv4a, d_bv4b});
    // lhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_true, d_b}));
    // rhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_true}));
    // lhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4and}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4xnor}));
    test_rule<kind>(d_nm.mk_node(
        Kind::EQUAL,
        {d_bv4_ones,
         RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, bv4xnor)
             .first}));
    // rhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4and, d_bv4_ones}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xnor, d_bv4_ones}));
    test_rule<kind>(d_nm.mk_node(
        Kind::EQUAL,
        {RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, bv4xnor)
             .first,
         d_bv4_ones}));
  }
}

TEST_F(TestRewriterBool, bool_equal_true)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_TRUE;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_bv4a}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_bv4_zero}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_bv4b}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_bv4_one}));
}

TEST_F(TestRewriterBool, bool_equal_false)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_FALSE;
  //// applies
  // (= (bvnot a) a)
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4a), d_bv4a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4_zero), d_bv4_zero}));
  // (= a (bvnot a))
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_nm.invert_node(d_bv4a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_nm.invert_node(d_bv4_zero)}));
  // (= (bvadd a c) a) with c a non-zero value
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one}), d_bv4a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a}), d_bv4a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4a, d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4a, d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a})}));
  // (= (bvnot (bvadd a c)) (bvnot a)) with c a non-zero value
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one})),
       d_nm.invert_node(d_bv4a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a})),
       d_nm.invert_node(d_bv4a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a}))}));
  // (= (bvadd a c0) (bvadd a c1)) with c0,c1 values and c0 != c1
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a})}));
  // (= (bvnot (bvadd a c0)) (bvnot (bvadd a c1)))
  // with c0,c1 values and c0 != c1
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_bv4a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_zero}), d_bv4a}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4a, d_nm.invert_node(d_bv4b)}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4a), d_bv4b}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_zero})),
       d_nm.invert_node(d_bv4a)}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4a}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4b, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_one})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4b, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4a, d_bv4_ones}))}));
  Type fun_type = d_nm.mk_fun_type({d_bv4_type, d_bv4_type});
  Node funa     = d_nm.mk_const(fun_type);
  Node funb     = d_nm.mk_const(fun_type);
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {funa, funb}));
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
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::NOT, {d_b}));
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
