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
    auto parents = tracker.parents({e});
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }

  {
    auto parents = tracker.parents({e, b});
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }

  {
    auto parents = tracker.parents({e, b, a});
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(a, parents[0]);
  }
}

TEST_F(TestAssertionTracker, track2)
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
  tracker.track(e, d, {c});

  {
    auto parents = tracker.parents({e});
    ASSERT_EQ(parents.size(), 2);
    ASSERT_EQ(d, parents[0]);
    ASSERT_EQ(a, parents[1]);
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
    tracker.track(e, d, {c});
    auto parents = tracker.parents({e});
    ASSERT_EQ(parents.size(), 2);
    ASSERT_EQ(d, parents[0]);
    ASSERT_EQ(a, parents[1]);
    mgr.pop();
  }

  {
    auto parents = tracker.parents({e});
    ASSERT_EQ(parents.size(), 1);
    ASSERT_EQ(e, parents[0]);
  }
}

}  // namespace bzla::test

