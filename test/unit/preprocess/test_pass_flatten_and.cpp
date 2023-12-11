/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/backtrackable.h"
#include "gtest/gtest.h"
#include "preprocess/pass/flatten_and.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace backtrack;
using namespace node;

class TestPassFlattenAnd : public TestPreprocessingPass
{
 public:
  TestPassFlattenAnd() : d_pass(d_env, &d_bm){};

 protected:
  Env d_env;
  backtrack::BacktrackManager d_bm;
  preprocess::pass::PassFlattenAnd d_pass;
};

TEST_F(TestPassFlattenAnd, and1)
{
  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  d_as.push_back(d_nm.mk_node(Kind::AND, {a1, a2}));
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as.size(), 3);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
}

TEST_F(TestPassFlattenAnd, and2)
{
  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");
  Node a3 = d_nm.mk_const(d_nm.mk_bool_type(), "a3");

  d_as.push_back(
      d_nm.mk_node(Kind::AND, {a1, d_nm.mk_node(Kind::AND, {a2, a3})}));
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as.size(), 4);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a1);
  ASSERT_EQ(d_as[2], a2);
  ASSERT_EQ(d_as[3], a3);
}

TEST_F(TestPassFlattenAnd, and3)
{
  Node a1 = d_nm.mk_const(d_nm.mk_bool_type(), "a1");
  Node a2 = d_nm.mk_const(d_nm.mk_bool_type(), "a2");

  d_as.push_back(
      d_nm.mk_node(Kind::AND, {a2, d_nm.mk_node(Kind::AND, {a1, a2})}));
  ASSERT_EQ(d_as.size(), 1);

  preprocess::AssertionVector assertions(d_as.view());
  d_pass.apply(assertions);

  ASSERT_EQ(d_as.size(), 3);
  ASSERT_EQ(d_as[0], d_nm.mk_value(true));
  ASSERT_EQ(d_as[1], a2);
  ASSERT_EQ(d_as[2], a1);
}

}  // namespace bzla::test
