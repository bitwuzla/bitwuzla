#include "env.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewriter.h"

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
  TestNodeUtils() : d_rewriter(d_env.rewriter()) {}

  NodeManager& d_nm = NodeManager::get();
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

TEST_F(TestNodeUtils, is_or)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bor = d_nm.mk_node(Kind::OR, {d_a, d_b});
  ASSERT_TRUE(utils::is_or(bor, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::OR_ELIM>::apply(d_rewriter, bor);
  ASSERT_TRUE(utils::is_or(res, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  ASSERT_FALSE(
      utils::is_or(d_nm.mk_node(Kind::AND, {d_a, d_b}), child0, child1));
}

TEST_F(TestNodeUtils, is_xor)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bxor = d_nm.mk_node(Kind::XOR, {d_a, d_b});
  ASSERT_TRUE(utils::is_xor(bxor, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::XOR_ELIM>::apply(d_rewriter, bxor);
  ASSERT_TRUE(utils::is_xor(res, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  ASSERT_FALSE(
      utils::is_xor(d_nm.mk_node(Kind::AND, {d_a, d_b}), child0, child1));
  ASSERT_FALSE(utils::is_xor(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::OR, {d_a, d_b}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_c}))}),
      child0,
      child1));
}

TEST_F(TestNodeUtils, is_xnor)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bxor  = d_nm.mk_node(Kind::XOR, {d_a, d_b});
  Node bxnor = d_nm.invert_node(bxor);
  ASSERT_TRUE(utils::is_xnor(bxnor, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::XOR_ELIM>::apply(d_rewriter, bxor);
  bxnor = d_nm.invert_node(res);
  ASSERT_TRUE(utils::is_xnor(bxnor, child0, child1));
  ASSERT_EQ(child0, d_a);
  ASSERT_EQ(child1, d_b);
  ASSERT_FALSE(utils::is_xnor(bxor, child0, child1));
}

TEST_F(TestNodeUtils, is_bv_neg)
{
  Node res, child;
  RewriteRuleKind kind;
  Node bvneg = d_nm.mk_node(Kind::BV_NEG, {d_a4});
  ASSERT_TRUE(utils::is_bv_neg(bvneg, child));
  ASSERT_EQ(child, d_a4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(d_rewriter, bvneg);
  ASSERT_TRUE(utils::is_bv_neg(res, child));
  ASSERT_EQ(child, d_a4);
  ASSERT_FALSE(utils::is_bv_neg(d_nm.invert_node(d_a4), child));
}

TEST_F(TestNodeUtils, is_bv_or)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bvor = d_nm.mk_node(Kind::BV_OR, {d_a4, d_b4});
  ASSERT_TRUE(utils::is_bv_or(bvor, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_OR_ELIM>::apply(d_rewriter, bvor);
  ASSERT_TRUE(utils::is_bv_or(res, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  ASSERT_FALSE(utils::is_bv_or(
      d_nm.mk_node(Kind::BV_AND, {d_a4, d_b4}), child0, child1));
}

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

TEST_F(TestNodeUtils, is_bv_sub)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bvsub = d_nm.mk_node(Kind::BV_SUB, {d_a4, d_b4});
  ASSERT_TRUE(utils::is_bv_sub(bvsub, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_SUB_ELIM>::apply(d_rewriter, bvsub);
  ASSERT_TRUE(utils::is_bv_sub(res, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  ASSERT_FALSE(utils::is_bv_sub(
      d_nm.mk_node(Kind::BV_AND, {d_a4, d_b4}), child0, child1));
}

TEST_F(TestNodeUtils, is_bv_xnor)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node bvxnor = d_nm.mk_node(Kind::BV_XNOR, {d_a4, d_b4});
  ASSERT_TRUE(utils::is_bv_xnor(bvxnor, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, bvxnor);
  ASSERT_TRUE(utils::is_bv_xnor(res, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  ASSERT_FALSE(utils::is_bv_xnor(
      d_nm.mk_node(Kind::BV_XOR, {d_a4, d_b4}), child0, child1));
  ASSERT_FALSE(utils::is_bv_xnor(
      d_nm.invert_node(d_nm.mk_node(
          Kind::BV_AND,
          {d_nm.mk_node(Kind::BV_OR, {d_a4, d_b4}),
           d_nm.invert_node(d_nm.mk_node(Kind::BV_AND, {d_a4, d_c4}))})),
      child0,
      child1));
}

}  // namespace bzla::test
