#include "bitvector.h"
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
  void SetUp() override
  {
    d_false = d_nm.mk_value(false);
    d_true  = d_nm.mk_value(true);
  }

 protected:
  void test_elim_rule_bool(Kind kind)
  {
    test_elim_rule(kind, d_nm.mk_bool_type());
  }

  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Node d_false;
  Node d_true;
};

/* and ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_and_eval)
{
  // applies
  Node and0 = d_nm.mk_node(Kind::AND, {d_true, d_true});
  ASSERT_EQ(d_true, d_rewriter.rewrite(and0));

  Node and1 = d_nm.mk_node(Kind::AND, {and0, d_false});
  ASSERT_EQ(d_false, d_rewriter.rewrite(and1));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(and1));
  // does not apply
  Node and2 =
      d_nm.mk_node(Kind::AND, {d_nm.mk_const(d_nm.mk_bool_type()), d_false});
  ASSERT_EQ(
      and2,
      RewriteRule<RewriteRuleKind::AND_EVAL>::apply(d_rewriter, and2).first);
}

/* equal -------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_equal_eval)
{
  Type fp_type = d_nm.mk_fp_type(3, 5);
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
                   {d_nm.mk_value(FloatingPoint::fpzero(fp_type, false)),
                    d_nm.mk_value(FloatingPoint::fpzero(fp_type, true))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(equal3));
  Node equal4 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(RoundingMode::RNA), d_nm.mk_value(RoundingMode::RNA)});
  ASSERT_EQ(d_true, d_rewriter.rewrite(equal4));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(equal0_1));
  // does not apply
  Node equal5 =
      d_nm.mk_node(Kind::EQUAL, {d_nm.mk_const(d_nm.mk_bool_type()), d_false});
  ASSERT_EQ(equal5,
            RewriteRule<RewriteRuleKind::EQUAL_EVAL>::apply(d_rewriter, equal5)
                .first);
}

TEST_F(TestRewriterBool, bool_equal_special_const)
{
  Type bv4_type = d_nm.mk_bv_type(4);
  Type bv1_type = d_nm.mk_bv_type(1);
  Node b        = d_nm.mk_const(d_nm.mk_bool_type());
  Node bv1_zero = d_nm.mk_value(BitVector::mk_zero(1));
  Node bv4_zero = d_nm.mk_value(BitVector::mk_zero(4));
  Node bv4a     = d_nm.mk_const(bv4_type);
  Node bv4b     = d_nm.mk_const(bv4_type);
  Node bv4xor   = d_nm.mk_node(Kind::BV_XOR, {bv4a, bv4b});
  Node bv4or    = d_nm.mk_node(Kind::BV_OR, {bv4a, bv4b});
  ////// special const 0
  {
    //// applies
    Node res_eq  = d_nm.mk_node(Kind::EQUAL, {bv4a, bv4b});
    Node res_and = d_nm.mk_node(
        Kind::AND,
        {d_nm.mk_node(Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_NOT, {bv4a}), bv4_zero}),
         d_nm.mk_node(Kind::EQUAL,
                      {d_nm.mk_node(Kind::BV_NOT, {bv4b}), bv4_zero})});
    // lhs 0
    Node equal0 = d_nm.mk_node(Kind::EQUAL, {d_false, b});
    ASSERT_EQ(d_nm.mk_node(Kind::NOT, {b}), d_rewriter.rewrite(equal0));
    Node equal1 = d_nm.mk_node(Kind::EQUAL, {bv4_zero, bv4xor});
    ASSERT_EQ(res_eq, d_rewriter.rewrite(equal1));
    Node equal2 = d_nm.mk_node(Kind::EQUAL, {bv4_zero, bv4or});
    ASSERT_EQ(res_and, d_rewriter.rewrite(equal2));
    // rhs 0
    Node equal3 = d_nm.mk_node(Kind::EQUAL, {b, d_false});
    ASSERT_EQ(d_nm.mk_node(Kind::NOT, {b}), d_rewriter.rewrite(equal3));
    Node equal4 = d_nm.mk_node(Kind::EQUAL, {bv4xor, bv4_zero});
    ASSERT_EQ(res_eq, d_rewriter.rewrite(equal4));
    Node equal5 = d_nm.mk_node(Kind::EQUAL, {bv4or, bv4_zero});
    ASSERT_EQ(res_and, d_rewriter.rewrite(equal5));
    //// empty cache
    ASSERT_EQ(res_and, Rewriter().rewrite(equal5));
    //// does not apply
    Node equal6 =
        d_nm.mk_node(Kind::EQUAL, {bv1_zero, d_nm.mk_const(bv1_type)});
    ASSERT_EQ(equal6, d_rewriter.rewrite(equal6));
    Node equal7 = d_nm.mk_node(
        Kind::EQUAL, {d_nm.mk_const(bv4_type), d_nm.mk_const(bv4_type)});
    ASSERT_EQ(equal7, d_rewriter.rewrite(equal7));
  }
}

/* not ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_not_eval)
{
  // applies
  Node not0 = d_nm.mk_node(Kind::NOT, {d_false});
  ASSERT_EQ(d_true, d_rewriter.rewrite(not0));

  Node not1 = d_nm.mk_node(Kind::NOT, {not0});
  ASSERT_EQ(d_false, d_rewriter.rewrite(not1));
  // empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(not1));
  // does not apply
  Node not2 = d_nm.mk_node(Kind::NOT, {d_nm.mk_const(d_nm.mk_bool_type())});
  ASSERT_EQ(
      not2,
      RewriteRule<RewriteRuleKind::NOT_EVAL>::apply(d_rewriter, not2).first);
}

/* or ----------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_or_elim) { test_elim_rule_bool(Kind::OR); }

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test

