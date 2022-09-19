#include "gtest/gtest.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::test {

using namespace bzla::node;

class TestNode : public ::testing::Test
{
};

TEST_F(TestNode, node_ctor_dtor)
{
  Node n;
  ASSERT_TRUE(n.is_null());
  ASSERT_EQ(n.kind(), Kind::NULL_NODE);
  ASSERT_EQ(n.id(), 0);
  ASSERT_EQ(n.num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
}

TEST_F(TestNode, node_is_value)
{
  NodeManager& nm = NodeManager::get();
  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  ASSERT_FALSE(nm.mk_const(bool_type).is_value());
  ASSERT_FALSE(nm.mk_const(bv_type).is_value());
  ASSERT_FALSE(nm.mk_const(fp_type).is_value());
  ASSERT_FALSE(nm.mk_const(rm_type).is_value());
  ASSERT_FALSE(nm.mk_const(array_type).is_value());
  ASSERT_FALSE(nm.mk_const(fun_type).is_value());

  ASSERT_TRUE(nm.mk_value(true).is_value());
  ASSERT_TRUE(nm.mk_value(false).is_value());

  ASSERT_TRUE(nm.mk_value(BitVector(32, 1)).is_value());

  ASSERT_TRUE(nm.mk_value(RoundingMode::RNA).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RNE).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTN).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTP).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTZ).is_value());

  ASSERT_FALSE(
      nm.mk_node(Kind::AND, {nm.mk_const(bool_type), nm.mk_const(bool_type)})
          .is_value());
}

}  // namespace bzla::test
