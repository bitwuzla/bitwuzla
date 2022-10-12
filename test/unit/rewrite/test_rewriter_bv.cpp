#include "bv/bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "rewrite/rewriter.h"
#include "solver/fp/floating_point.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBv : public TestRewriter
{
 protected:
  void SetUp() override
  {
    TestRewriter::SetUp();
    d_a4 = d_nm.mk_const(d_bv4_type);
    d_b4 = d_nm.mk_const(d_bv4_type);
    d_a1 = d_nm.mk_const(d_bv1_type);
    d_b1 = d_nm.mk_const(d_bv1_type);
  }

  void test_elim_rule_bv(node::Kind kind,
                         const std::vector<uint64_t> indices = {})
  {
    for (uint64_t i = 0; i < d_bv_sizes.size(); ++i)
    {
      std::vector<uint64_t> idxs = {};
      if (!indices.empty()) idxs.push_back(indices[i]);
      test_elim_rule(kind, d_nm.mk_bv_type(d_bv_sizes[i]), idxs);
    }
  }

  std::vector<uint64_t> d_bv_sizes = {1, 2, 3, 4, 8};
  Node d_a1;
  Node d_b1;
  Node d_a4;
  Node d_b4;
};

/* bvadd -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_add_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_EVAL;
  //// applies
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0111")), d_rewriter.rewrite(bvadd0));
  Node bvadd1 =
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_value(BitVector(4, "1001")), bvadd0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvadd1));
  Node bvadd1_1 =
      d_nm.mk_node(Kind::BV_ADD, {bvadd1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvadd1_1));
  Node bvadd1_2 = d_nm.mk_node(Kind::BV_ADD, {bvadd1, bvadd1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvadd1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvadd1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_add_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_ADD, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_ADD, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
}

TEST_F(TestRewriterBv, bv_add_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_CONST;
  Node a_val                     = d_nm.mk_value(BitVector::from_ui(4, 5));
  Node b_val                     = d_nm.mk_value(BitVector::from_ui(4, 1));
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), b_val}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {b_val, d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), a_val}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), d_a4}));
}

TEST_F(TestRewriterBv, bv_add_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_BV1;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a1, d_a1}));
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a1, d_b1}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a4, d_b4}));
}

TEST_F(TestRewriterBv, bv_add_mul_two)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_MUL_TWO;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a4, d_a4}));
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a1, d_a1}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_ADD, {d_a4, d_b4}));
}

TEST_F(TestRewriterBv, bv_add_not)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_NOT;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_NOT, {d_a4})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_node(Kind::BV_NOT, {d_a4}), d_a4}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a1, d_nm.mk_node(Kind::BV_NOT, {d_a1})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_node(Kind::BV_NOT, {d_a1}), d_a1}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_NOT, {d_b4})}));
}

TEST_F(TestRewriterBv, bv_add_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_NEG, {d_a4})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_node(Kind::BV_NEG, {d_a4}), d_a4}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a1, d_nm.mk_node(Kind::BV_NEG, {d_a1})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_node(Kind::BV_NEG, {d_a1}), d_a1}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_a4,
                    RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
                        d_rewriter, d_nm.mk_node(Kind::BV_NEG, {d_a4}))
                        .first}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_NEG, {d_b4})}));
}

TEST_F(TestRewriterBv, bv_add_urem)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_UREM;
  //// applies
  // (bvadd a (bvneg (bvmul (bvudiv a b) b)))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(
                        Kind::BV_MUL,
                        {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(
                        Kind::BV_MUL,
                        {d_b4, d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})})})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_node(
           Kind::BV_NEG,
           {d_nm.mk_node(Kind::BV_MUL,
                         {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})}),
       d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_node(
           Kind::BV_NEG,
           {d_nm.mk_node(Kind::BV_MUL,
                         {d_b4, d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})})}),
       d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
           d_rewriter,
           d_nm.mk_node(
               Kind::BV_NEG,
               {d_nm.mk_node(
                   Kind::BV_MUL,
                   {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})}))
           .first}));
  // (bvadd a (bvmul (bvneg (bvudiv a b)) b)))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_NEG,
                                  {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})}),
                     d_b4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(
           Kind::BV_MUL,
           {d_b4,
            d_nm.mk_node(Kind::BV_NEG,
                         {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})})})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_NEG,
                                  {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})}),
                     d_b4}),
       d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_node(
           Kind::BV_MUL,
           {d_b4,
            d_nm.mk_node(Kind::BV_NEG,
                         {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})})}),
       d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(
           Kind::BV_MUL,
           {RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
                d_rewriter,
                d_nm.mk_node(Kind::BV_NEG,
                             {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})}))
                .first,
            d_b4})}));
  // (bvadd a (bvmul (bvudiv a b)) (bvneg b))))
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_a4,
                    d_nm.mk_node(Kind::BV_MUL,
                                 {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}),
                                  d_nm.mk_node(Kind::BV_NEG, {d_b4})})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_NEG, {d_b4}),
                     d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL,
                                 {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}),
                                  d_nm.mk_node(Kind::BV_NEG, {d_b4})}),
                    d_a4}));
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL,
                                 {d_nm.mk_node(Kind::BV_NEG, {d_b4}),
                                  d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})}),
                    d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}),
                     RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
                         d_rewriter, d_nm.mk_node(Kind::BV_NEG, {d_b4}))
                         .first})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(
                        Kind::BV_ADD,
                        {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_b4,
       d_nm.mk_node(Kind::BV_NEG,
                    {d_nm.mk_node(
                        Kind::BV_MUL,
                        {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_node(Kind::BV_NEG,
                                  {d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4})}),
                     d_nm.mk_node(Kind::BV_NEG, {d_b4})})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4,
       d_nm.mk_node(Kind::BV_MUL,
                    {

                        d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_b4}), d_b4})}));
}

TEST_F(TestRewriterBv, bv_add_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_MUL;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_MUL, {d_a4, d_b4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_MUL, {d_b4, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_MUL, {d_a4, d_b4}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_MUL, {d_b4, d_a4}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_MUL, {d_a4, d_a4})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_a4,
                    d_nm.mk_node(Kind::BV_MUL,
                                 {d_b4, d_nm.mk_node(Kind::BV_NOT, {d_a4})})}));
}

TEST_F(TestRewriterBv, bv_add_shl)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_SHL;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_SHL, {d_b4, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_SHL, {d_b4, d_a4}), d_a4}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::BV_SHL, {d_a4, d_b4})}));
}

TEST_F(TestRewriterBv, bv_add_ite)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ADD_ITE;
  Node cond                      = d_nm.mk_const(d_nm.mk_bool_type());
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_a4, d_bv4_zero})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_bv4_zero})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_a4}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::ITE, {cond, d_a4, d_bv4_zero}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_bv4_zero}), d_a4}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_one, d_a4})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_a4, d_b4})}));
}

/* bvand -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_and_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_AND_EVAL;
  //// applies
  Node bvand0 = d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand0));
  Node bvand1 =
      d_nm.mk_node(Kind::BV_AND, {d_nm.mk_value(BitVector(4, "1001")), bvand0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1));
  Node bvand1_1 =
      d_nm.mk_node(Kind::BV_AND, {bvand1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1_1));
  Node bvand1_2 = d_nm.mk_node(Kind::BV_AND, {bvand1, bvand1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), d_rewriter.rewrite(bvand1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1000")), Rewriter().rewrite(bvand1_2));
  //// does not apply
  Node bvand_x0 =
      d_nm.mk_node(Kind::BV_AND, {d_a4, d_nm.mk_value(BitVector(4, "1110"))});
  test_rule_does_not_apply<kind>(bvand_x0);
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_AND, {bvand_x0, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_and_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_AND_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_AND, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_AND, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_AND, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
  ////// special const 1
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_bv1_one, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_a1, d_bv1_one}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_AND, {d_bv4_one, d_a4}));
  }
  ////// special const ones
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_bv4_ones, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_AND, {d_a4, d_bv4_ones}));
  }
}

/* bvashr ------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_ashr_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ASHR_EVAL;
  //// applies
  Node bvashr0 = d_nm.mk_node(Kind::BV_ASHR,
                              {d_nm.mk_value(BitVector(4, "1101")),
                               d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvashr0));
  Node bvashr1 = d_nm.mk_node(Kind::BV_ASHR,
                              {d_nm.mk_value(BitVector(4, "0111")), bvashr0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1));
  Node bvashr1_1 = d_nm.mk_node(Kind::BV_ASHR,
                                {bvashr1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1_1));
  Node bvashr1_2 = d_nm.mk_node(Kind::BV_ASHR, {bvashr1, bvashr1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvashr1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvashr1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ASHR, {d_a4, d_nm.mk_value(BitVector(4, "0010"))}));
}

TEST_F(TestRewriterBv, bv_ashr_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ASHR_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_ASHR, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ASHR, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_ASHR, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_ASHR, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_ASHR, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
}

/* bvconcat ----------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_concat_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_CONCAT_EVAL;
  //// applies
  Node bvconcat0 = d_nm.mk_node(Kind::BV_CONCAT,
                                {d_nm.mk_value(BitVector(4, "1001")),
                                 d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(8, "10011110")),
            d_rewriter.rewrite(bvconcat0));
  Node bvconcat1 = d_nm.mk_node(
      Kind::BV_CONCAT, {d_nm.mk_value(BitVector(4, "1001")), bvconcat0});
  ASSERT_EQ(d_nm.mk_value(BitVector(12, "100110011110")),
            d_rewriter.rewrite(bvconcat1));
  Node bvconcat1_1 = d_nm.mk_node(
      Kind::BV_CONCAT, {bvconcat1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(16, "1001100111101110")),
            d_rewriter.rewrite(bvconcat1_1));
  Node bvconcat1_2 = d_nm.mk_node(Kind::BV_CONCAT, {bvconcat1, bvconcat1});
  ASSERT_EQ(d_nm.mk_value(BitVector(24, "100110011110100110011110")),
            d_rewriter.rewrite(bvconcat1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(24, "100110011110100110011110")),
            Rewriter().rewrite(bvconcat1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_CONCAT, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

/* bvmul -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_mul_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_EVAL;
  //// applies
  Node bvmul0 = d_nm.mk_node(Kind::BV_MUL,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvmul0));
  Node bvmul1 =
      d_nm.mk_node(Kind::BV_MUL, {d_nm.mk_value(BitVector(4, "1001")), bvmul0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1110")), d_rewriter.rewrite(bvmul1));
  Node bvmul1_1 =
      d_nm.mk_node(Kind::BV_MUL, {bvmul1, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), d_rewriter.rewrite(bvmul1_1));
  Node bvmul1_2 = d_nm.mk_node(Kind::BV_MUL, {bvmul1, bvmul1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), d_rewriter.rewrite(bvmul1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0100")), Rewriter().rewrite(bvmul1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_MUL, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_mul_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_MUL, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_MUL, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
  ////// special const 1
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_bv1_one, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_bv4_one, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a1, d_bv1_one}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_one}));
  }
  ////// special const ones
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_bv4_ones, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a4, d_bv4_ones}));
  }
}

TEST_F(TestRewriterBv, bv_mul_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_BV1;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a1, d_a1}));
  test_rule<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a1, d_b1}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_MUL, {d_a4, d_b4}));
}

TEST_F(TestRewriterBv, bv_mul_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_CONST;
  Node a_val                     = d_nm.mk_value(BitVector::from_ui(4, 5));
  Node b_val                     = d_nm.mk_value(BitVector::from_ui(4, 1));
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_MUL, {a_val, d_a4}), b_val}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {b_val, d_nm.mk_node(Kind::BV_MUL, {a_val, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_MUL, {a_val, d_a4}), a_val}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_MUL, {a_val, d_a4}), d_a4}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_UDIV, {a_val, d_a4}), d_a4}));
}

TEST_F(TestRewriterBv, bv_mul_const_add)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_CONST_ADD;
  Node a_val                     = d_nm.mk_value(BitVector::from_ui(4, 5));
  Node b_val                     = d_nm.mk_value(BitVector::from_ui(4, 1));
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), b_val}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {b_val, d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), a_val}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_ADD, {a_val, d_a4}), d_a4}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_UDIV, {a_val, d_a4}), d_a4}));
}

TEST_F(TestRewriterBv, bv_mul_ite)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_ITE;
  Node cond                      = d_nm.mk_const(d_nm.mk_bool_type());
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_a4})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_a4, d_bv4_zero})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL,
      {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_bv4_zero})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_a4}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::ITE, {cond, d_a4, d_bv4_zero}), d_a4}));
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL,
      {d_nm.mk_node(Kind::ITE, {cond, d_bv4_zero, d_bv4_zero}), d_a4}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_bv4_one, d_a4})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_a4, d_nm.mk_node(Kind::ITE, {cond, d_a4, d_b4})}));
}

TEST_F(TestRewriterBv, bv_mul_shl)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_MUL_SHL;
  Node c4                        = d_nm.mk_const(d_bv4_type);
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::BV_MUL,
                               {d_nm.mk_node(Kind::BV_SHL, {d_a4, d_b4}), c4}));
  test_rule<kind>(d_nm.mk_node(Kind::BV_MUL,
                               {c4, d_nm.mk_node(Kind::BV_SHL, {d_a4, d_b4})}));
  test_rule<kind>(d_nm.mk_node(Kind::BV_MUL,
                               {d_nm.mk_node(Kind::BV_SHL, {d_a4, d_b4}),
                                d_nm.mk_node(Kind::BV_SHL, {d_a4, c4})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_SHR, {d_a4, d_b4}), c4}));
}

/* bvnot -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_not_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_NOT_EVAL;
  //// applies
  Node bvnot0 =
      d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_value(BitVector(4, "1001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), d_rewriter.rewrite(bvnot0));
  Node bvnot1 = d_nm.mk_node(Kind::BV_NOT, {bvnot0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1001")), d_rewriter.rewrite(bvnot1));
  Node bvnot2 = d_nm.mk_node(Kind::BV_NOT, {bvnot1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), d_rewriter.rewrite(bvnot2));

  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0110")), Rewriter().rewrite(bvnot2));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_NOT, {d_a4}));
}

TEST_F(TestRewriterBv, bv_not_bv_not)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_NOT_BV_NOT;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_node(Kind::BV_NOT, {d_a4})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_NOT, {d_a4}));
}

/* bvshl -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_shl_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SHL_EVAL;
  //// applies
  Node bvshl0 = d_nm.mk_node(Kind::BV_SHL,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0010")), d_rewriter.rewrite(bvshl0));
  Node bvshl1 =
      d_nm.mk_node(Kind::BV_SHL, {d_nm.mk_value(BitVector(4, "1111")), bvshl0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1100")), d_rewriter.rewrite(bvshl1));
  Node bvshl1_1 =
      d_nm.mk_node(Kind::BV_SHL, {bvshl1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshl1_1));
  Node bvshl1_2 = d_nm.mk_node(Kind::BV_SHL, {bvshl1, bvshl1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshl1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvshl1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SHL, {d_a4, d_nm.mk_value(BitVector(4, "0010"))}));
}

TEST_F(TestRewriterBv, bv_shl_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SHL_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_SHL, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SHL, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_SHL, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_SHL, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_SHL, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
}

/* bvshr -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_shr_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SHR_EVAL;
  //// applies
  Node bvshr0 = d_nm.mk_node(Kind::BV_SHR,
                             {d_nm.mk_value(BitVector(4, "1101")),
                              d_nm.mk_value(BitVector(4, "0011"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvshr0));
  Node bvshr1 =
      d_nm.mk_node(Kind::BV_SHR, {d_nm.mk_value(BitVector(4, "1111")), bvshr0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0111")), d_rewriter.rewrite(bvshr1));
  Node bvshr1_1 =
      d_nm.mk_node(Kind::BV_SHR, {bvshr1, d_nm.mk_value(BitVector(4, "0010"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvshr1_1));
  Node bvshr1_2 = d_nm.mk_node(Kind::BV_SHR, {bvshr1, bvshr1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvshr1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvshr1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SHR, {d_a4, d_nm.mk_value(BitVector(4, "0010"))}));
}

TEST_F(TestRewriterBv, bv_shr_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SHR_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_SHR, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SHR, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_SHR, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_SHR, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_SHR, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
}

/* bvslt -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_slt_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SLT_EVAL;
  //// applies
  Node bvslt0 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_true, d_rewriter.rewrite(bvslt0));
  Node bvslt1 = d_nm.mk_node(Kind::BV_SLT,
                             {d_nm.mk_value(BitVector(4, "0001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(bvslt1));
  // with empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(bvslt1));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SLT, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_slt_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_SLT_SPECIAL_CONST;
  Node a2                        = d_nm.mk_const(d_nm.mk_bv_type(2));
  Node bv2_one                   = d_nm.mk_value(BitVector::mk_one(2));
  ////// special const 0
  {
    Node dis = d_nm.mk_node(Kind::NOT,
                            {d_nm.mk_node(Kind::EQUAL, {d_a1, d_bv1_zero})});
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_bv1_zero, d_a1}));
    // rhs 0
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a1, d_bv1_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a1, d_a1}));
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_SLT, {d_a4, d_bv4_zero}));
  }
  ////// special const 1
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_bv1_one, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {bv2_one, a2}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a1, d_bv1_one}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {a2, bv2_one}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_SLT, {d_bv4_one, d_a4}));
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_SLT, {d_a4, d_bv4_one}));
  }
  ////// special const ones
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_bv1_ones, d_a1}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_SLT, {d_bv4_ones, d_a4}));
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_SLT,
                     {d_nm.mk_value(BitVector::mk_ones(2)),
                      d_nm.mk_const(d_nm.mk_bv_type(2))}));
  }
  ////// special const min_signed
  {
    Node min1_s = d_nm.mk_value(BitVector::mk_min_signed(1));
    Node min4_s = d_nm.mk_value(BitVector::mk_min_signed(4));
    //// applies
    // lhs min_signed
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {min1_s, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {min4_s, d_a4}));
    // rhs min_signed
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a1, min1_s}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a4, min4_s}));
  }
  ////// special const max_signed
  {
    Node max1_s = d_nm.mk_value(BitVector::mk_max_signed(1));
    Node max4_s = d_nm.mk_value(BitVector::mk_max_signed(4));
    //// applies
    // lhs max_signed
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {max1_s, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {max4_s, d_a4}));
    // rhs max_signed
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a1, max1_s}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_SLT, {d_a4, max4_s}));
  }
}

/* bvudiv-------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_udiv_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_UDIV_EVAL;
  //// applies
  Node bvudiv0 = d_nm.mk_node(Kind::BV_UDIV,
                              {d_nm.mk_value(BitVector(4, "1001")),
                               d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvudiv0));
  Node bvudiv1 = d_nm.mk_node(Kind::BV_UDIV,
                              {d_nm.mk_value(BitVector(4, "1001")), bvudiv0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1111")), d_rewriter.rewrite(bvudiv1));
  Node bvudiv1_1 = d_nm.mk_node(Kind::BV_UDIV,
                                {bvudiv1, d_nm.mk_value(BitVector(4, "0110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0010")), d_rewriter.rewrite(bvudiv1_1));
  Node bvudiv1_2 = d_nm.mk_node(Kind::BV_UDIV, {bvudiv1, bvudiv1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), d_rewriter.rewrite(bvudiv1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0001")), Rewriter().rewrite(bvudiv1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_udiv_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_UDIV_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_UDIV, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_UDIV, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_UDIV, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
  ////// special const 1
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_UDIV, {d_a1, d_bv1_one}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_UDIV, {d_a4, d_bv4_one}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_UDIV, {d_bv1_one, d_a1}));
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_UDIV, {d_bv4_one, d_a4}));
  }
}

/* bvult -------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_ult_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ULT_EVAL;
  //// applies
  Node bvult0 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1001")),
                              d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_true, d_rewriter.rewrite(bvult0));
  Node bvult1 = d_nm.mk_node(Kind::BV_ULT,
                             {d_nm.mk_value(BitVector(4, "1110")),
                              d_nm.mk_value(BitVector(4, "0001"))});
  ASSERT_EQ(d_false, d_rewriter.rewrite(bvult1));
  // with empty cache
  ASSERT_EQ(d_false, Rewriter().rewrite(bvult1));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ULT, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_ult_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_ULT_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_bv1_zero, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a1, d_bv1_zero}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a1, d_a1}));
  }
  ////// special const 1
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_bv1_one, d_a1}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a1, d_bv1_one}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_one}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::BV_ULT, {d_bv4_one, d_a4}));
  }
  ////// special const ones
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_bv4_ones, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_ULT, {d_a4, d_bv4_ones}));
  }
}

/* bvurem ------------------------------------------------------------------- */

TEST_F(TestRewriterBv, bv_urem_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_UREM_EVAL;
  //// applies
  Node bvurem0 = d_nm.mk_node(Kind::BV_UREM,
                              {d_nm.mk_value(BitVector(4, "1001")),
                               d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "1001")), d_rewriter.rewrite(bvurem0));
  Node bvurem1 = d_nm.mk_node(Kind::BV_UREM,
                              {d_nm.mk_value(BitVector(4, "1001")), bvurem0});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1));
  Node bvurem1_1 = d_nm.mk_node(Kind::BV_UREM,
                                {bvurem1, d_nm.mk_value(BitVector(4, "0110"))});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1_1));
  Node bvurem1_2 = d_nm.mk_node(Kind::BV_UREM, {bvurem1, bvurem1});
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), d_rewriter.rewrite(bvurem1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(BitVector(4, "0000")), Rewriter().rewrite(bvurem1_2));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_UREM, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
}

TEST_F(TestRewriterBv, bv_urem_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::BV_UREM_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::BV_UREM, {d_bv4_zero, d_a4}));
    test_rule<kind>(d_nm.mk_node(Kind::BV_UREM, {d_a4, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::BV_UREM, {d_a4, d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_UREM, {d_nm.mk_value(BitVector(4, "1110")), d_a4}));
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::BV_UREM, {d_a4, d_nm.mk_value(BitVector(4, "1110"))}));
  }
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterBv, bv_nand_elim) { test_elim_rule_bv(Kind::BV_NAND); }

TEST_F(TestRewriterBv, bv_neg_elim) { test_elim_rule_bv(Kind::BV_NEG); }

TEST_F(TestRewriterBv, bv_nor_elim) { test_elim_rule_bv(Kind::BV_NOR); }

TEST_F(TestRewriterBv, bv_or_elim) { test_elim_rule_bv(Kind::BV_OR); }

TEST_F(TestRewriterBv, bv_redand_elim) { test_elim_rule_bv(Kind::BV_REDAND); }

TEST_F(TestRewriterBv, bv_redor_elim) { test_elim_rule_bv(Kind::BV_REDOR); }

// not supported by Bitwuzla main
// TEST_F(TestRewriterBv, bv_redxor_elim) { test_elim_rule_bv(Kind::BV_REDXOR);
// }

TEST_F(TestRewriterBv, bv_roli_elim)
{
  test_elim_rule_bv(Kind::BV_ROLI, {0, 1, 2, 3, 12});
}

TEST_F(TestRewriterBv, bv_rori_elim)
{
  test_elim_rule_bv(Kind::BV_RORI, {0, 1, 2, 3, 12});
}

TEST_F(TestRewriterBv, bv_repeat_elim)
{
  test_elim_rule_bv(Kind::BV_REPEAT, {1, 1, 2, 3, 4});
}

TEST_F(TestRewriterBv, bv_saddo_elim) { test_elim_rule_bv(Kind::BV_SADDO); }

TEST_F(TestRewriterBv, bv_sdiv_elim) { test_elim_rule_bv(Kind::BV_SDIV); }

TEST_F(TestRewriterBv, bv_sdivo_elim) { test_elim_rule_bv(Kind::BV_SDIVO); }

TEST_F(TestRewriterBv, bv_sge_elim) { test_elim_rule_bv(Kind::BV_SGE); }

TEST_F(TestRewriterBv, bv_sgt_elim) { test_elim_rule_bv(Kind::BV_SGT); }

TEST_F(TestRewriterBv, bv_sign_extend_elim)
{
  test_elim_rule_bv(Kind::BV_SIGN_EXTEND, {0, 1, 2, 3, 4});
}

TEST_F(TestRewriterBv, bv_sle_elim) { test_elim_rule_bv(Kind::BV_SLE); }

TEST_F(TestRewriterBv, bv_smod_elim) { test_elim_rule_bv(Kind::BV_SMOD); }

TEST_F(TestRewriterBv, bv_smulo_elim) { test_elim_rule_bv(Kind::BV_SMULO); }

TEST_F(TestRewriterBv, bv_srem_elim) { test_elim_rule_bv(Kind::BV_SREM); }

TEST_F(TestRewriterBv, bv_ssubo_elim) { test_elim_rule_bv(Kind::BV_SSUBO); }

TEST_F(TestRewriterBv, bv_sub_elim) { test_elim_rule_bv(Kind::BV_SUB); }

TEST_F(TestRewriterBv, bv_uaddo_elim) { test_elim_rule_bv(Kind::BV_UADDO); }

TEST_F(TestRewriterBv, bv_uge_elim) { test_elim_rule_bv(Kind::BV_UGE); }

TEST_F(TestRewriterBv, bv_ugt_elim) { test_elim_rule_bv(Kind::BV_UGT); }

TEST_F(TestRewriterBv, bv_ule_elim) { test_elim_rule_bv(Kind::BV_ULE); }

TEST_F(TestRewriterBv, bv_umulo_elim) { test_elim_rule_bv(Kind::BV_UMULO); }

TEST_F(TestRewriterBv, bv_usubo_elim) { test_elim_rule_bv(Kind::BV_USUBO); }

TEST_F(TestRewriterBv, bv_xnor_elim) { test_elim_rule_bv(Kind::BV_XNOR); }

TEST_F(TestRewriterBv, bv_zero_extend_elim)
{
  test_elim_rule_bv(Kind::BV_ZERO_EXTEND, {0, 1, 2, 3, 4});
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
