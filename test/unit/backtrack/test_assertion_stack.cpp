/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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

TEST_F(TestAssertionStack, insert_at_level)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node a1 = nm.mk_const(nm.mk_bool_type(), "a1");
  Node a2 = nm.mk_const(nm.mk_bool_type(), "a2");
  Node a3 = nm.mk_const(nm.mk_bool_type(), "a3");
  Node a4 = nm.mk_const(nm.mk_bool_type(), "a4");
  Node a5 = nm.mk_const(nm.mk_bool_type(), "a5");

  as.insert_at_level(0, a1);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as[0], a1);

  as.push_back(a2);
  ASSERT_EQ(as.level(1), 0);
  ASSERT_EQ(as[1], a2);

  as.push();

  as.push_back(a3);
  ASSERT_EQ(as.level(2), 1);
  ASSERT_EQ(as[2], a3);

  as.insert_at_level(0, a3);
  ASSERT_EQ(as.size(), 4);
  ASSERT_EQ(as[0], a1);
  ASSERT_EQ(as[1], a2);
  ASSERT_EQ(as[2], a3);
  ASSERT_EQ(as[3], a3);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 0);
  ASSERT_EQ(as.level(2), 0);
  ASSERT_EQ(as.level(3), 1);

  as.insert_at_level(0, a3);
  ASSERT_EQ(as.size(), 5);
  as.insert_at_level(1, a3);
  ASSERT_EQ(as.size(), 6);
  ASSERT_EQ(as[0], a1);
  ASSERT_EQ(as[1], a2);
  ASSERT_EQ(as[2], a3);
  ASSERT_EQ(as[3], a3);
  ASSERT_EQ(as[4], a3);

  as.insert_at_level(1, a4);
  ASSERT_EQ(as[0], a1);
  ASSERT_EQ(as[1], a2);
  ASSERT_EQ(as[2], a3);
  ASSERT_EQ(as[3], a3);
  ASSERT_EQ(as[4], a3);
  ASSERT_EQ(as[5], a3);
  ASSERT_EQ(as[6], a4);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 0);
  ASSERT_EQ(as.level(2), 0);
  ASSERT_EQ(as.level(3), 0);
  ASSERT_EQ(as.level(4), 1);
  ASSERT_EQ(as.level(5), 1);
  ASSERT_EQ(as.level(6), 1);

  as.pop();
  ASSERT_EQ(as.size(), 4);
  ASSERT_EQ(as[0], a1);
  ASSERT_EQ(as[1], a2);
  ASSERT_EQ(as[2], a3);
  ASSERT_EQ(as[3], a3);
  ASSERT_EQ(as.level(0), 0);
  ASSERT_EQ(as.level(1), 0);
  ASSERT_EQ(as.level(2), 0);
  ASSERT_EQ(as.level(3), 0);

  as.push();
  as.insert_at_level(1, a4);
  ASSERT_EQ(as.size(), 5);
  as.push_back(a4);
  ASSERT_EQ(as.size(), 6);

  as.push();
  as.push_back(a5);
  ASSERT_EQ(as.size(), 7);
  as.insert_at_level(2, a5);
  ASSERT_EQ(as.size(), 8);

  as.pop();
  as.insert_at_level(1, a5);
  ASSERT_EQ(as.size(), 7);
}

TEST_F(TestAssertionStack, view)
{
  AssertionStack as;
  NodeManager& nm = NodeManager::get();

  Node f1 = nm.mk_const(nm.mk_bool_type());
  Node f2 = nm.mk_const(nm.mk_bool_type());
  Node f3 = nm.mk_const(nm.mk_bool_type());

  auto& view1 = as.view();
  auto& view2 = as.view();
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
