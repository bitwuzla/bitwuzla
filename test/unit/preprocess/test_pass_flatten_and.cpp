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
  preprocess::AssertionVector assertions;

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  assertions.push_back(d_nm.mk_node(Kind::AND, {a1, a2}));
  ASSERT_EQ(assertions.size(), 1);

  d_pass.apply(assertions);
  ASSERT_EQ(assertions.size(), 3);
  ASSERT_EQ(assertions[0], d_nm.mk_value(true));
  ASSERT_EQ(assertions[1], a1);
  ASSERT_EQ(assertions[2], a2);
};

TEST_F(TestPassFlattenAnd, and2)
{
  preprocess::AssertionVector assertions;

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");
  Node a3 = d_nm.mk_const(d_nm.mk_bool_type(), "a3");

  assertions.push_back(
      d_nm.mk_node(Kind::AND, {a1, d_nm.mk_node(Kind::AND, {a2, a3})}));
  ASSERT_EQ(assertions.size(), 1);

  d_pass.apply(assertions);
  ASSERT_EQ(assertions.size(), 4);
  ASSERT_EQ(assertions[0], d_nm.mk_value(true));
  ASSERT_EQ(assertions[1], a1);
  ASSERT_EQ(assertions[2], a2);
  ASSERT_EQ(assertions[3], a3);
};

TEST_F(TestPassFlattenAnd, and3)
{
  preprocess::AssertionVector assertions;

  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  assertions.push_back(
      d_nm.mk_node(Kind::AND, {a2, d_nm.mk_node(Kind::AND, {a1, a2})}));
  ASSERT_EQ(assertions.size(), 1);

  d_pass.apply(assertions);
  ASSERT_EQ(assertions.size(), 3);
  ASSERT_EQ(assertions[0], d_nm.mk_value(true));
  ASSERT_EQ(assertions[1], a2);
  ASSERT_EQ(assertions[2], a1);
};

}  // namespace bzla::test
