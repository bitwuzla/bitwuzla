/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include <type_traits>

#include "backtrack/vector_map.h"
#include "test.h"

namespace bzla::test {

// Backtrackable objects register themselves with the BacktrackManager on
// construction. Copying or moving would not register the new object and
// silently desynchronize its control stack, so these operations are deleted.
static_assert(!std::is_copy_constructible_v<backtrack::vector_map<int, int>>);
static_assert(!std::is_copy_assignable_v<backtrack::vector_map<int, int>>);
static_assert(!std::is_move_constructible_v<backtrack::vector_map<int, int>>);
static_assert(!std::is_move_assignable_v<backtrack::vector_map<int, int>>);

class TestVectorMap : public ::testing::Test
{
};

TEST_F(TestVectorMap, ctor_dtor)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector_map<int, int> map(&mgr);
}

TEST_F(TestVectorMap, push_pop)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector_map<int, int> map(&mgr);

  // Base scope: append two values to key 0.
  map.add(0, 10);
  map.add(0, 11);
  ASSERT_EQ(map.size(), 1);
  ASSERT_EQ(map.find(0)->second.size(), 2);

  mgr.push();
  // Append to existing key 0 and to a fresh key 1.
  map.add(0, 12);
  map.add(1, 20);
  ASSERT_EQ(map.size(), 2);
  ASSERT_EQ(map.find(0)->second.size(), 3);
  ASSERT_EQ(map.find(1)->second.size(), 1);

  // Only the appends from the popped scope are undone; the base-scope vector
  // for key 0 is left intact and the now-empty key 1 is removed.
  mgr.pop();
  ASSERT_EQ(map.size(), 1);
  ASSERT_EQ(map.find(1), map.end());
  ASSERT_NE(map.find(0), map.end());
  ASSERT_EQ(map.find(0)->second.size(), 2);
  ASSERT_EQ(map.find(0)->second[0], 10);
  ASSERT_EQ(map.find(0)->second[1], 11);
}

TEST_F(TestVectorMap, reassert_no_duplicates)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector_map<int, int> map(&mgr);

  // Re-appending the same edge across push/pop cycles must not accumulate: the
  // size after each cycle is constant, mirroring re-asserted array equalities.
  for (int i = 0; i < 5; ++i)
  {
    mgr.push();
    map.add(0, 42);
    map.add(1, 43);
    ASSERT_EQ(map.find(0)->second.size(), 1);
    ASSERT_EQ(map.find(1)->second.size(), 1);
    mgr.pop();
    ASSERT_TRUE(map.empty());
  }
}

TEST_F(TestVectorMap, cross_scope_key)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector_map<int, int> map(&mgr);

  // A key first seen in an outer scope can grow again in an inner scope; only
  // the inner appends are rolled back.
  mgr.push();
  map.add(7, 1);
  mgr.push();
  map.add(7, 2);
  map.add(7, 3);
  ASSERT_EQ(map.find(7)->second.size(), 3);
  mgr.pop();
  ASSERT_EQ(map.find(7)->second.size(), 1);
  ASSERT_EQ(map.find(7)->second[0], 1);
  mgr.pop();
  ASSERT_TRUE(map.empty());
}

TEST_F(TestVectorMap, nested)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector_map<int, int> map(&mgr);

  map.add(0, 0);
  mgr.push();
  map.add(0, 1);
  mgr.push();
  map.add(0, 2);
  map.add(1, 100);
  ASSERT_EQ(map.find(0)->second.size(), 3);
  ASSERT_EQ(map.size(), 2);
  mgr.pop();
  ASSERT_EQ(map.find(0)->second.size(), 2);
  ASSERT_EQ(map.find(1), map.end());
  mgr.pop();
  ASSERT_EQ(map.find(0)->second.size(), 1);
  ASSERT_EQ(map.find(0)->second[0], 0);
}

}  // namespace bzla::test
