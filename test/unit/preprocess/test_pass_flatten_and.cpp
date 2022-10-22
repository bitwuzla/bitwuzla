#include "gtest/gtest.h"
#include "preprocess/pass/flatten_and.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassFlattenAnd : public TestPreprocessingPass
{
 public:
  TestPassFlattenAnd() : d_pass(d_rw){};

 protected:
  preprocess::pass::PassFlattenAnd d_pass;
};

TEST_F(TestPassFlattenAnd, and1)
{
  AssertionView& view = d_as.create_view();

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  d_as.push_back(d_nm.mk_node(Kind::AND, {a1, a2}));
  ASSERT_EQ(d_as.size(), 1);

  d_pass.apply(view);
  ASSERT_EQ(d_as.size(), 3);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
};

TEST_F(TestPassFlattenAnd, and2)
{
  AssertionView& view = d_as.create_view();

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");
  Node a3 = d_nm.mk_const(d_nm.mk_bool_type(), "a3");

  d_as.push_back(
      d_nm.mk_node(Kind::AND, {a1, d_nm.mk_node(Kind::AND, {a2, a3})}));
  ASSERT_EQ(d_as.size(), 1);

  d_pass.apply(view);
  ASSERT_EQ(d_as.size(), 4);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
  ASSERT_EQ(d_as[3], a3);
};

TEST_F(TestPassFlattenAnd, and3)
{
  AssertionView& view = d_as.create_view();

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  d_as.push_back(
      d_nm.mk_node(Kind::AND, {a2, d_nm.mk_node(Kind::AND, {a1, a2})}));
  ASSERT_EQ(d_as.size(), 1);

  d_pass.apply(view);
  ASSERT_EQ(d_as.size(), 3);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a2);
  ASSERT_EQ(d_as[2], a1);
};

TEST_F(TestPassFlattenAnd, and_push1)
{
  AssertionView& view = d_as.create_view();

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");
  Node a3 = d_nm.mk_const(d_nm.mk_bool_type(), "a3");
  Node a4 = d_nm.mk_const(d_nm.mk_bool_type(), "a4");

  d_as.push_back(d_nm.mk_node(Kind::AND, {a1, a2}));
  d_as.push();
  d_as.push_back(
      d_nm.mk_node(Kind::AND, {a1, d_nm.mk_node(Kind::AND, {a3, a4})}));
  ASSERT_EQ(d_as.size(), 2);

  d_pass.apply(view);
  ASSERT_EQ(d_as.size(), 6);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
  ASSERT_EQ(d_as[3], d_nm.mk_value(true));
  ASSERT_EQ(d_as[4], a3);
  ASSERT_EQ(d_as[5], a4);

  ASSERT_EQ(d_as.level(0), 0);
  ASSERT_EQ(d_as.level(1), 0);
  ASSERT_EQ(d_as.level(2), 0);
  ASSERT_EQ(d_as.level(3), 1);
  ASSERT_EQ(d_as.level(4), 1);
  ASSERT_EQ(d_as.level(5), 1);

  d_as.pop();
  ASSERT_EQ(d_as.size(), 3);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
  ASSERT_EQ(d_as.level(0), 0);
  ASSERT_EQ(d_as.level(1), 0);
  ASSERT_EQ(d_as.level(2), 0);
}

}  // namespace bzla::test
