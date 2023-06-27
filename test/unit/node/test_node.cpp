/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "gtest/gtest.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::test {

using namespace bzla::node;

class TestNode : public ::testing::Test
{
};

TEST_F(TestNode, node_ctor_dtor)
{
  Node n;
  ASSERT_TRUE(n.is_null());
  ASSERT_EQ(n.kind(), Kind::NULL_NODE);
  ASSERT_EQ(n.id(), 0);
  ASSERT_EQ(n.num_children(), 0);
  ASSERT_EQ(n.begin(), n.end());
}

TEST_F(TestNode, node_is_value)
{
  NodeManager& nm = NodeManager::get();
  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  ASSERT_FALSE(nm.mk_const(bool_type).is_value());
  ASSERT_FALSE(nm.mk_const(bv_type).is_value());
  ASSERT_FALSE(nm.mk_const(fp_type).is_value());
  ASSERT_FALSE(nm.mk_const(rm_type).is_value());
  ASSERT_FALSE(nm.mk_const(array_type).is_value());
  ASSERT_FALSE(nm.mk_const(fun_type).is_value());

  ASSERT_TRUE(nm.mk_value(true).is_value());
  ASSERT_TRUE(nm.mk_value(false).is_value());

  ASSERT_TRUE(nm.mk_value(BitVector::from_ui(32, 1)).is_value());
  ASSERT_TRUE(nm.mk_value(FloatingPoint::fpzero(fp_type, true)).is_value());

  ASSERT_TRUE(nm.mk_value(RoundingMode::RNA).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RNE).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTN).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTP).is_value());
  ASSERT_TRUE(nm.mk_value(RoundingMode::RTZ).is_value());

  ASSERT_FALSE(
      nm.mk_node(Kind::AND, {nm.mk_const(bool_type), nm.mk_const(bool_type)})
          .is_value());
}

TEST_F(TestNode, rbegin_rend)
{
  NodeManager& nm = NodeManager::get();
  Type bool_type  = nm.mk_bool_type();
  Node a          = nm.mk_const(bool_type, "a");
  Node b          = nm.mk_const(bool_type, "b");
  Node c          = nm.mk_const(bool_type, "c");
  Node d          = nm.mk_const(bool_type, "d");

  std::vector<Node> children = {a, b};
  Node a_and_b               = nm.mk_node(Kind::AND, children);
  auto itv                   = children.rbegin();
  auto itn                   = a_and_b.rbegin();
  for (; itv != children.rend(); ++itv, ++itn)
  {
    std::cout << *itv << " == " << *itn << std::endl;
    ASSERT_EQ(*itv, *itn);
  }

  Type fun_type =
      nm.mk_fun_type({bool_type, bool_type, bool_type, bool_type, bool_type});
  Node fun                   = nm.mk_const(fun_type);
  std::vector<Node> expected = {fun, a, b, c, d};
  Node app                   = nm.mk_node(Kind::APPLY, expected);
  itv                        = expected.rbegin();
  itn                        = app.rbegin();
  for (; itv != expected.rend(); ++itv, ++itn)
  {
    ASSERT_EQ(*itv, *itn);
  }
}

TEST_F(TestNode, operator_out)
{
  NodeManager& nm = NodeManager::get();
  Type bool_type  = nm.mk_bool_type();
  Type bv_type    = nm.mk_bv_type(32);
  Type fp_type    = nm.mk_fp_type(5, 11);
  Type rm_type    = nm.mk_rm_type();
  Type array_type = nm.mk_array_type(bv_type, fp_type);
  Type fun_type   = nm.mk_fun_type({bool_type, rm_type, array_type});

  std::cout << nm.mk_const(bool_type) << std::endl;
  std::cout << nm.mk_const(bv_type) << std::endl;
  std::cout << nm.mk_const(fp_type) << std::endl;
  std::cout << nm.mk_const(rm_type) << std::endl;
  std::cout << nm.mk_const(array_type) << std::endl;
  std::cout << nm.mk_const(fun_type) << std::endl;

  std::cout << nm.mk_value(RoundingMode::RNA) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RNE) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTN) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTP) << std::endl;
  std::cout << nm.mk_value(RoundingMode::RTZ) << std::endl;

  std::cout << nm.mk_value(true) << std::endl;
  std::cout << nm.mk_value(false) << std::endl;

  std::cout << nm.mk_value(BitVector::from_ui(32, 1)) << std::endl;
  std::cout << nm.mk_value(FloatingPoint::fpzero(fp_type, true)) << std::endl;

  std::cout << nm.mk_node(Kind::AND,
                          {nm.mk_const(bool_type), nm.mk_const(bool_type)})
            << std::endl;
  std::cout << nm.mk_node(Kind::APPLY,
                          {nm.mk_const(fun_type, "fun"),
                           nm.mk_const(bool_type, "x"),
                           nm.mk_const(rm_type, "y")})
            << std::endl;
}

}  // namespace bzla::test
