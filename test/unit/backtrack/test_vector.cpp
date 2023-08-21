/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/vector.h"
#include "gtest/gtest.h"
#include "test.h"

namespace bzla::test {

class TestVector : public ::testing::Test
{
};

TEST_F(TestVector, ctor_dtor)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<int> vec(&mgr);
}

TEST_F(TestVector, push_pop)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<int> vec(&mgr);
  vec.push_back(0);
  vec.push_back(1);
  vec.push_back(2);
  mgr.push();
  ASSERT_EQ(vec.size(), 3);
  vec.push_back(3);
  vec.push_back(4);
  ASSERT_EQ(vec.size(), 5);
  mgr.pop();
  ASSERT_EQ(vec.size(), 3);
  ASSERT_EQ(vec[0], 0);
  ASSERT_EQ(vec[1], 1);
  ASSERT_EQ(vec[2], 2);
  ASSERT_DEATH_DEBUG(vec.pop(), "d_control.empty");
}

TEST_F(TestVector, mgr_multi)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<int> vec1(&mgr);
  mgr.push();
  {
    mgr.pop();
    backtrack::vector<int> vec2(&mgr);
    mgr.push();
  }
  mgr.pop();
}

TEST_F(TestVector, push_pop_mgr)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<int> vec1(&mgr);
  backtrack::vector<int> vec2(&mgr);
  vec1.push_back(0);
  vec1.push_back(1);
  vec1.push_back(2);
  mgr.push();
  ASSERT_EQ(vec1.size(), 3);
  vec1.push_back(3);
  vec1.push_back(4);
  ASSERT_EQ(vec1.size(), 5);
  mgr.pop();
  ASSERT_EQ(vec1.size(), 3);
  ASSERT_EQ(vec1[0], 0);
  ASSERT_EQ(vec1[1], 1);
  ASSERT_EQ(vec1[2], 2);
  ASSERT_DEATH_DEBUG(mgr.pop(), "d_scope_levels > 0");
}

TEST_F(TestVector, insert_at_level)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<int> vec(&mgr);
  mgr.push();
  mgr.push();

  vec.insert_at_level(0, 0);
  vec.insert_at_level(1, 1);
  vec.insert_at_level(2, 2);

  ASSERT_EQ(vec.size(), 3);
  ASSERT_EQ(vec[0], 0);
  ASSERT_EQ(vec[1], 1);
  ASSERT_EQ(vec[2], 2);

  vec.insert_at_level(0, 0);
  vec.insert_at_level(1, 1);
  vec.insert_at_level(2, 2);
  ASSERT_EQ(vec.size(), 6);
  ASSERT_EQ(vec[0], 0);
  ASSERT_EQ(vec[1], 0);
  ASSERT_EQ(vec[2], 1);
  ASSERT_EQ(vec[3], 1);
  ASSERT_EQ(vec[4], 2);
  ASSERT_EQ(vec[5], 2);

  mgr.pop();
  ASSERT_EQ(vec.size(), 4);
  vec.insert_at_level(0, 0);
  vec.insert_at_level(0, 0);
  ASSERT_EQ(vec.size(), 6);
  ASSERT_EQ(vec[0], 0);
  ASSERT_EQ(vec[1], 0);
  ASSERT_EQ(vec[2], 0);
  ASSERT_EQ(vec[3], 0);
}

TEST_F(TestVector, stress)
{
  backtrack::BacktrackManager mgr;
  backtrack::vector<size_t> vec(&mgr);

  mgr.push();
  for (size_t i = 0; i < 1000000; ++i)
  {
    vec.push_back(i);
  }
  mgr.pop();
}

}  // namespace bzla::test
