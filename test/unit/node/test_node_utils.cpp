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

TEST_F(TestNodeUtils, is_bv_xnor)
{
  Node res;
  RewriteRuleKind kind;
  Node xnor = d_nm.mk_node(Kind::BV_XNOR, {d_a4, d_b4});
  ASSERT_TRUE(utils::is_bv_xnor(xnor));
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, xnor);
  ASSERT_TRUE(utils::is_bv_xnor(res));
  ASSERT_FALSE(utils::is_bv_xnor(d_nm.mk_node(Kind::BV_XOR, {d_a4, d_b4})));
}
}  // namespace bzla::test
