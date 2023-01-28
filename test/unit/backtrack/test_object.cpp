#include "backtrack/object.h"
#include "gtest/gtest.h"

namespace bzla::test {

class TestObject : public ::testing::Test
{
};

TEST_F(TestObject, ctor_dtor)
{
  backtrack::BacktrackManager bm;
  backtrack::object<int> o(&bm);
}

TEST_F(TestObject, push_pop)
{
  backtrack::BacktrackManager bm;
  backtrack::object<int> o(&bm);

  o = 1;
  bm.push();
  o = 2;
  bm.push();
  o = 3;
  bm.push();
  ASSERT_EQ(o.get(), 3);
  bm.pop();
  ASSERT_EQ(o.get(), 3);
  bm.pop();
  ASSERT_EQ(o.get(), 2);
  bm.pop();
  ASSERT_EQ(o.get(), 1);
}

}  // namespace bzla::test
