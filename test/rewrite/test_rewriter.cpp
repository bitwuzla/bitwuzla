#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "rewrite/rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriter : public ::testing::Test
{
  void SetUp() override { d_bv_type = d_nm.mk_bv_type(4); }

 protected:
  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Type d_bv_type;
};

TEST_F(TestRewriter, bv_and_eval)
{
  // applies
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
  // does not apply
  Node bvand2 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_const(d_bv_type), d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand2, d_rewriter.rewrite(bvand2));
  Node bvand3 =
      d_nm.mk_node(Kind::BV_AND, {bvand2, d_nm.mk_value(BitVector(4, "1110"))});
  ASSERT_EQ(bvand3, d_rewriter.rewrite(bvand3));
}

}  // namespace bzla::test
