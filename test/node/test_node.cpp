#include "node/node.h"
#include "test.h"

namespace bzla::test {

using namespace bzla::node;

class TestNode : public TestCommon
{
};

TEST_F(TestNode, ctor_dtor)
{
  Node n;
  ASSERT_TRUE(n.is_null());
  ASSERT_EQ(n.get_kind(), Kind::NULL_NODE);
  ASSERT_EQ(n.get_id(), 0);
  ASSERT_EQ(n.get_data(), nullptr);
  ASSERT_EQ(n.get_num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
}

TEST_F(TestNode, node_data)
{
  Node n(Kind::CONSTANT, {});
  ASSERT_EQ(n.get_kind(), Kind::CONSTANT);
  ASSERT_EQ(n.get_num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
}

TEST_F(TestNode, node_data_children)
{
  Node x(Kind::CONSTANT, {});
  Node y(Kind::CONSTANT, {});
  Node n(Kind::AND, {x, y});
  ASSERT_EQ(n.get_kind(), Kind::AND);
  ASSERT_EQ(n.get_num_children(), 2);
  ASSERT_NE(n.begin(), n.end());
  ASSERT_EQ(n[0], x);
  ASSERT_EQ(n[1], y);

  for (auto it = n.begin(); it != n.end(); ++it)
  {
    ASSERT_FALSE(it->is_null());
    ASSERT_TRUE(*it == x || *it == y);
  }
  for (const Node& c : n)
  {
    ASSERT_FALSE(c.is_null());
    ASSERT_TRUE(c == x || c == y);
  }
}

}  // namespace bzla::test
