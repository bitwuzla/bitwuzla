/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/unordered_set.h"
#include "gtest/gtest.h"
#include "test.h"

namespace bzla::test {

class TestUnorderedSet : public ::testing::Test
{
};

TEST_F(TestUnorderedSet, ctor_dtor)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_set<int> set(&mgr);
}

TEST_F(TestUnorderedSet, push_pop)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_set<int> set(&mgr);
  set.insert(0);
  set.insert(1);
  set.insert(2);
  mgr.push();
  ASSERT_EQ(set.size(), 3);
  ASSERT_FALSE(set.empty());
  set.insert(3);
  set.insert(4);
  set.insert(3);  // duplicate
  ASSERT_EQ(set.size(), 5);
  mgr.pop();
  ASSERT_EQ(set.size(), 3);
  ASSERT_EQ(set.find(3), set.end());
  ASSERT_EQ(set.find(4), set.end());
  ASSERT_NE(set.find(0), set.end());
  ASSERT_NE(set.find(1), set.end());
  ASSERT_NE(set.find(2), set.end());
  ASSERT_DEATH_DEBUG(mgr.pop(), "d_scope_levels > 0");
}

TEST_F(TestUnorderedSet, push_pop_mgr)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_set<int> set(&mgr);
  set.insert(0);
  set.insert(1);
  set.insert(2);
  mgr.push();
  ASSERT_EQ(set.size(), 3);
  ASSERT_FALSE(set.empty());
  set.insert(3);
  set.insert(4);
  set.insert(3);  // duplicate
  ASSERT_EQ(set.size(), 5);
  mgr.pop();
  ASSERT_EQ(set.size(), 3);
  ASSERT_EQ(set.find(3), set.end());
  ASSERT_EQ(set.find(4), set.end());
  ASSERT_NE(set.find(0), set.end());
  ASSERT_NE(set.find(1), set.end());
  ASSERT_NE(set.find(2), set.end());
  ASSERT_DEATH_DEBUG(mgr.pop(), "d_scope_levels > 0");
}

TEST_F(TestUnorderedSet, stress)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_set<size_t> set(&mgr);

  mgr.push();
  for (size_t i = 0; i < 10000000; ++i)
  {
    if (i % 100 == 0)
    {
      mgr.push();
    }
    set.insert(i);
    if (i % 100 == 0)
    {
      mgr.pop();
    }
  }
  mgr.pop();
}

}  // namespace bzla::test
