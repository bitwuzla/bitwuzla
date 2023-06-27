/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "env.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestNodeUtils : public ::testing::Test
{
  void SetUp() override
  {
    d_a        = d_nm.mk_const(d_nm.mk_bool_type());
    d_b        = d_nm.mk_const(d_nm.mk_bool_type());
    d_c        = d_nm.mk_const(d_nm.mk_bool_type());
    d_bv4_type = d_nm.mk_bv_type(4);
    d_a4       = d_nm.mk_const(d_bv4_type);
    d_b4       = d_nm.mk_const(d_bv4_type);
    d_c4       = d_nm.mk_const(d_bv4_type);
  }

 protected:
  TestNodeUtils() : d_rewriter(d_env.rewriter()) {}

  NodeManager& d_nm = NodeManager::get();
  Env d_env;
  Rewriter& d_rewriter;
  Type d_bv4_type;
  Node d_a;
  Node d_b;
  Node d_c;
  Node d_a4;
  Node d_b4;
  Node d_c4;
};

TEST_F(TestNodeUtils, is_bv_sext)
{
  Node res, child;
  RewriteRuleKind kind;
  Node bvsext = d_nm.mk_node(Kind::BV_SIGN_EXTEND, {d_a4}, {3});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  std::tie(res, kind) =
      RewriteRule<RewriteRuleKind::BV_SIGN_EXTEND_ELIM>::apply(d_rewriter,
                                                               bvsext);
  assert(utils::is_bv_sext(res, child));
  ASSERT_TRUE(utils::is_bv_sext(res, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3}),
                          d_nm.mk_value(BitVector::mk_one(1))}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_one(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3}),
                          d_nm.mk_value(BitVector::mk_zero(1))}),
            d_nm.mk_value(BitVector::mk_zero(3)),
            d_nm.mk_value(BitVector::mk_ones(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_zero(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_zero(3)),
            d_nm.mk_value(BitVector::mk_ones(3))}),
       d_a4});
  ASSERT_TRUE(utils::is_bv_sext(bvsext, child));
  ASSERT_EQ(child, d_a4);
  bvsext = d_nm.mk_node(
      Kind::BV_CONCAT,
      {d_nm.mk_node(
           Kind::ITE,
           {d_nm.mk_node(Kind::EQUAL,
                         {d_nm.mk_value(BitVector::mk_zero(1)),
                          d_nm.mk_node(Kind::BV_EXTRACT, {d_a4}, {3, 3})}),
            d_nm.mk_value(BitVector::mk_ones(3)),
            d_nm.mk_value(BitVector::mk_zero(3))}),
       d_a4});
  ASSERT_FALSE(utils::is_bv_sext(bvsext, child));
  ASSERT_FALSE(utils::is_bv_sext(
      d_nm.mk_node(Kind::BV_ZERO_EXTEND, {d_a4}, {3}), child));
}

}  // namespace bzla::test
