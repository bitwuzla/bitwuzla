/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "preprocess/assertion_tracker.h"

namespace bzla::test {

using namespace preprocess;
using namespace node;

class TestAssertionTracker : public ::testing::Test
{
 public:
  TestAssertionTracker() : d_nm(NodeManager::get()) {};

 protected:
  NodeManager& d_nm;
};

TEST_F(TestAssertionTracker, track1)
{
  backtrack::BacktrackManager mgr;
  AssertionTracker tracker(&mgr);

  auto a = d_nm.mk_const(d_nm.mk_bool_type());
  auto b = d_nm.mk_const(d_nm.mk_bool_type());
  auto c = d_nm.mk_const(d_nm.mk_bool_type());
  auto d = d_nm.mk_const(d_nm.mk_bool_type());
  auto e = d_nm.mk_const(d_nm.mk_bool_type());

  tracker.track(b, a);
  tracker.track(c, b);
  tracker.track(d, c);
  tracker.track(e, d);

  {
    std::vector<Node> parents;
    tracker.find_original({e}, {a}, parents);
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }

  {
    std::vector<Node> parents;
    tracker.find_original({e, b}, {a}, parents);
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }

  {
    std::vector<Node> parents;
    tracker.find_original({e, b, a}, {a}, parents);
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }
}

TEST_F(TestAssertionTracker, inc1)
{
  backtrack::BacktrackManager mgr;
  AssertionTracker tracker(&mgr);

  auto a = d_nm.mk_const(d_nm.mk_bool_type());
  auto b = d_nm.mk_const(d_nm.mk_bool_type());
  auto c = d_nm.mk_const(d_nm.mk_bool_type());
  auto d = d_nm.mk_const(d_nm.mk_bool_type());
  auto e = d_nm.mk_const(d_nm.mk_bool_type());

  tracker.track(b, a);
  tracker.track(c, b);

  {
    mgr.push();
    tracker.track(e, d);
    std::vector<Node> parents;
    tracker.find_original({e}, {a, d}, parents);
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(d, parents[0]);
    mgr.pop();
  }

  {
    std::vector<Node> parents;
    tracker.find_original({e}, {e}, parents);
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(e, parents[0]);
  }
}

}  // namespace bzla::test
