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
    d_bv4_type = d_nm.mk_bv_type(4);
    d_a4       = d_nm.mk_const(d_bv4_type);
    d_b4       = d_nm.mk_const(d_bv4_type);
  }

 protected:
  NodeManager& d_nm = NodeManager::get();
  Rewriter d_rewriter;
  Type d_bv4_type;
  Node d_a4;
  Node d_b4;
};

TEST_F(TestNodeUtils, is_bv_neg)
{
  Node res, child;
  RewriteRuleKind kind;
  Node neg = d_nm.mk_node(Kind::BV_NEG, {d_a4});
  ASSERT_TRUE(utils::is_bv_neg(neg, child));
  ASSERT_EQ(child, d_a4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(d_rewriter, neg);
  ASSERT_TRUE(utils::is_bv_neg(res, child));
  ASSERT_EQ(child, d_a4);
  ASSERT_FALSE(utils::is_bv_neg(d_nm.mk_node(Kind::BV_NOT, {d_a4}), child));
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

TEST_F(TestNodeUtils, is_bv_xnor)
{
  Node res, child0, child1;
  RewriteRuleKind kind;
  Node xnor = d_nm.mk_node(Kind::BV_XNOR, {d_a4, d_b4});
  ASSERT_TRUE(utils::is_bv_xnor(xnor, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, xnor);
  ASSERT_TRUE(utils::is_bv_xnor(res, child0, child1));
  ASSERT_EQ(child0, d_a4);
  ASSERT_EQ(child1, d_b4);
  ASSERT_FALSE(utils::is_bv_xnor(
      d_nm.mk_node(Kind::BV_XOR, {d_a4, d_b4}), child0, child1));
}

}  // namespace bzla::test
