#include "backtrack/assertion_stack.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"

namespace bzla::test {

using namespace backtrack;

class TestAssertionStack : public ::testing::Test
{
};

TEST_F(TestAssertionStack, ctor_dtor) { AssertionStack as; }

TEST_F(TestAssertionStack, push_back)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());

  as.push_back(f1);
  as.push_back(f2);
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f2);
}

TEST_F(TestAssertionStack, push_pop)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());
  Node f3 = nm.mk_const(nm.mk_bool_type());

  as.push_back(f1);
  as.push();
  as.push_back(f2);
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f2);

  as.pop();
  ASSERT_EQ(as.size(), 1);
  ASSERT_EQ(as[0], f1);

  as.push_back(f3);
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f3);
}

TEST_F(TestAssertionStack, replace1)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());
  Node f3 = nm.mk_const(nm.mk_bool_type());
  Node f4 = nm.mk_const(nm.mk_bool_type());
  Node f5 = nm.mk_const(nm.mk_bool_type());

  as.push_back(f1);
  as.push_back(f2);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 0);
  as.push();
  as.push_back(f3);
  ASSERT_EQ(as.level(2), 1);

  as.replace(1, {f4, f5});
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f4);
  ASSERT_EQ(as[2], f5);
  ASSERT_EQ(as[3], f3);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 0);
  ASSERT_EQ(as.level(2), 0);
  ASSERT_EQ(as.level(3), 1);
  as.pop();
  ASSERT_EQ(as.size(), 3);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f4);
  ASSERT_EQ(as[2], f5);
}

TEST_F(TestAssertionStack, replace2)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());
  Node f3 = nm.mk_const(nm.mk_bool_type());
  Node f4 = nm.mk_const(nm.mk_bool_type());
  Node f5 = nm.mk_const(nm.mk_bool_type());

  as.push_back(f1);
  as.push();
  as.push_back(f2);
  as.push_back(f3);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 1);
  ASSERT_EQ(as.level(2), 1);

  as.replace(1, {f4, f5});
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f4);
  ASSERT_EQ(as[2], f5);
  ASSERT_EQ(as[3], f3);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 1);
  ASSERT_EQ(as.level(2), 1);
  ASSERT_EQ(as.level(3), 1);
  as.pop();
  ASSERT_EQ(as.size(), 1);
  ASSERT_EQ(as[0], f1);
}

TEST_F(TestAssertionStack, view)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());
  Node f3 = nm.mk_const(nm.mk_bool_type());

  auto& view1 = as.create_view();
  auto& view2 = as.create_view();
  ASSERT_EQ(view1.size(), 0);
  ASSERT_EQ(view2.size(), 0);

  as.push_back(f1);
  as.push();
  as.push_back(f2);
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f2);

  ASSERT_EQ(view1.size(), 2);
  ASSERT_FALSE(view1.empty());
  ASSERT_EQ(view1.next(), f1);
  ASSERT_EQ(view1.next(), f2);
  ASSERT_TRUE(view1.empty());
  ASSERT_EQ(view1.size(), 0);
  ASSERT_EQ(view2.size(), 2);

  as.pop();
  ASSERT_EQ(as.size(), 1);
  ASSERT_EQ(as[0], f1);
  ASSERT_TRUE(view1.empty());
  ASSERT_EQ(view1.size(), 0);
  ASSERT_EQ(view2.size(), 1);

  as.push_back(f3);
  ASSERT_EQ(as.size(), 2);
  ASSERT_EQ(as[0], f1);
  ASSERT_EQ(as[1], f3);
  ASSERT_EQ(view1.size(), 1);
  ASSERT_FALSE(view1.empty());
  ASSERT_EQ(view1.next(), f3);
  ASSERT_TRUE(view1.empty());
  ASSERT_EQ(view1.size(), 0);
  ASSERT_EQ(view2.size(), 2);
  ASSERT_FALSE(view2.empty());
  ASSERT_EQ(view2.next(), f1);
  ASSERT_EQ(view2.next(), f3);
  ASSERT_TRUE(view2.empty());
}

}  // namespace bzla::test
