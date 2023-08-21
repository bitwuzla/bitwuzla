/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/unordered_map.h"
#include "gtest/gtest.h"
#include "test.h"

namespace bzla::test {

class TestUnorderedMap : public ::testing::Test
{
};

TEST_F(TestUnorderedMap, ctor_dtor)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_map<int, bool> map(&mgr);
}

TEST_F(TestUnorderedMap, push_pop)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_map<int, bool> map(&mgr);
  map.emplace(0, true);
  map.emplace(1, false);
  map.emplace(2, true);
  mgr.push();
  ASSERT_EQ(map.size(), 3);
  ASSERT_FALSE(map.empty());
  map.emplace(3, true);
  map.emplace(4, true);
  map.emplace(3, true);  // duplicate
  ASSERT_EQ(map.size(), 5);
  mgr.pop();
  ASSERT_EQ(map.size(), 3);
  ASSERT_EQ(map.find(3), map.end());
  ASSERT_EQ(map.find(4), map.end());
  ASSERT_NE(map.find(0), map.end());
  ASSERT_NE(map.find(1), map.end());
  ASSERT_NE(map.find(2), map.end());
  ASSERT_DEATH_DEBUG(mgr.pop(), "d_scope_levels > 0");
}

TEST_F(TestUnorderedMap, push_pop_mgr)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_map<int, bool> map(&mgr);
  backtrack::unordered_map<bool, int> map2(&mgr);
  map.emplace(0, true);
  map.emplace(1, false);
  map.emplace(2, true);
  mgr.push();
  ASSERT_EQ(map.size(), 3);
  ASSERT_FALSE(map.empty());
  map.emplace(3, true);
  map.emplace(4, true);
  map.emplace(3, true);  // duplicate
  ASSERT_EQ(map.size(), 5);
  mgr.pop();
  ASSERT_EQ(map.size(), 3);
  ASSERT_EQ(map.find(3), map.end());
  ASSERT_EQ(map.find(4), map.end());
  ASSERT_NE(map.find(0), map.end());
  ASSERT_NE(map.find(1), map.end());
  ASSERT_NE(map.find(2), map.end());
  ASSERT_DEATH_DEBUG(mgr.pop(), "d_scope_levels > 0");
}

TEST_F(TestUnorderedMap, stress)
{
  backtrack::BacktrackManager mgr;
  backtrack::unordered_map<size_t, size_t> map(&mgr);

  mgr.push();
  for (size_t i = 0; i < 10000000; ++i)
  {
    if (i % 100 == 0)
    {
      mgr.push();
    }
    map.emplace(i, i);
    if (i % 100 == 0)
    {
      mgr.pop();
    }
  }
  mgr.pop();
}

}  // namespace bzla::test
