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
#include "option/option.h"
#include "preprocess/pass/contradicting_ands.h"
#include "test/unit/preprocess/test_preprocess_pass.h"

namespace bzla::test {

using namespace node;

/* -------------------------------------------------------------------------- */

class TestPassContradictingAnds : public TestPreprocessingPass
{
 protected:
  TestPassContradictingAnds()
  {
    d_options.rewrite_level.set(0);
    d_env.reset(new Env(d_options));
    d_pass.reset(new preprocess::pass::PassContradictingAnds(*d_env, &d_bm));
  }

  void test_and(const Node& node,
                const unordered_node_ref_set& expected_leafs = {},
                bool applies                                 = true)
  {
    unordered_node_ref_set visited{node};
    auto [leafs, is_contradicting] =
        d_pass->is_contradicting_and(node, visited);
    ASSERT_EQ(leafs, expected_leafs);
    ASSERT_EQ(is_contradicting, applies);
    Node a = d_nm.mk_node(Kind::EQUAL, {d_a, node});
    test_assertion(a, applies ? d_nm.mk_node(Kind::EQUAL, {d_a, d_zero}) : a);
  }

  void test_assertion(const Node& node, const Node& expected)
  {
    AssertionStack as;
    as.push_back(node);
    ASSERT_EQ(as.size(), 1);

    preprocess::AssertionVector assertions(as.view());
    d_pass->apply(assertions);

    ASSERT_EQ(as.size(), 1);
    ASSERT_EQ(as[0], expected);
  }

  Type d_bv8  = d_nm.mk_bv_type(8);
  Node d_a    = d_nm.mk_const(d_bv8, "a");
  Node d_b    = d_nm.mk_const(d_bv8, "b");
  Node d_c    = d_nm.mk_const(d_bv8, "c");
  Node d_d    = d_nm.mk_const(d_bv8, "d");
  Node d_e    = d_nm.mk_const(d_bv8, "d");
  Node d_a_inv = d_nm.invert_node(d_a);
  Node d_b_inv = d_nm.invert_node(d_b);
  Node d_c_inv = d_nm.invert_node(d_c);
  Node d_zero = d_nm.mk_value(BitVector::mk_zero(8));

  std::unique_ptr<preprocess::pass::PassContradictingAnds> d_pass;
  std::unique_ptr<Env> d_env;
};

/* -------------------------------------------------------------------------- */

TEST_F(TestPassContradictingAnds, bvand_does_not_apply1)
{
  test_and(d_nm.mk_node(Kind::BV_AND, {d_a, d_b}), {d_a, d_b}, false);
}

TEST_F(TestPassContradictingAnds, bvand_does_not_apply2)
{
  test_and(d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}), {d_a, d_b_inv}, false);
}

TEST_F(TestPassContradictingAnds, bvand_does_not_apply3)
{
  test_and(d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}), d_a}),
           {d_a, d_b_inv},
           false);
}

TEST_F(TestPassContradictingAnds, bvand1)
{
  test_and(d_nm.mk_node(Kind::BV_AND, {d_a, d_a_inv}));
}

TEST_F(TestPassContradictingAnds, bvand2)
{
  test_and(d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}), d_b}));
}

TEST_F(TestPassContradictingAnds, bvand3)
{
  test_and(d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}), d_nm.invert_node(d_a)}));
}

TEST_F(TestPassContradictingAnds, bvand4)
{
  test_and(d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}),
                         d_nm.mk_node(Kind::BV_AND, {d_c, d_a_inv})}));
}

TEST_F(TestPassContradictingAnds, bvand5)
{
  test_and(d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_node(Kind::BV_AND,
                    {d_a, d_nm.mk_node(Kind::BV_AND, {d_c, d_b_inv})}),
       d_nm.mk_node(Kind::BV_AND, {d_c_inv, d_a})}));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestPassContradictingAnds, assertion1)
{
  Node and1 = d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv});
  Node and2 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_node(Kind::BV_AND,
                    {d_a, d_nm.mk_node(Kind::BV_AND, {d_c, d_b_inv})}),
       d_nm.mk_node(Kind::BV_AND, {d_c_inv, d_a})});
  test_assertion(
      d_nm.mk_node(
          Kind::EQUAL,
          {d_a,
           d_nm.mk_node(Kind::BV_ADD,
                        {and1, d_nm.mk_node(Kind::BV_MUL, {d_d, and2})})}),
      d_nm.mk_node(
          Kind::EQUAL,
          {d_a,
           d_nm.mk_node(Kind::BV_ADD,
                        {and1, d_nm.mk_node(Kind::BV_MUL, {d_d, d_zero})})}));
}

TEST_F(TestPassContradictingAnds, assertion2)
{
  Node and1_0 = d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}),
                              d_nm.mk_node(Kind::BV_AND, {d_c, d_a_inv})});
  Node and1_1 = d_nm.mk_node(Kind::BV_AND,
                             {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}), d_b});
  test_and(and1_0);
  test_and(and1_1);

  Node and1 = d_nm.mk_node(Kind::BV_AND,
                           {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}),
                            d_nm.mk_node(Kind::BV_SHL, {and1_0, and1_1})});
  Node and1_subst =
      d_nm.mk_node(Kind::BV_AND,
                   {d_nm.mk_node(Kind::BV_AND, {d_a, d_b_inv}),
                    d_nm.mk_node(Kind::BV_SHL, {d_zero, d_zero})});
  test_assertion(d_nm.mk_node(Kind::EQUAL, {d_e, and1}),
                 d_nm.mk_node(Kind::EQUAL, {d_e, and1_subst}));

  Node and2 = d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.mk_node(Kind::BV_AND,
                    {d_a, d_nm.mk_node(Kind::BV_AND, {d_c, d_b_inv})}),
       d_nm.mk_node(Kind::BV_AND, {d_c_inv, d_a})});
  test_and(and2);

  test_assertion(
      d_nm.mk_node(Kind::EQUAL,
                   {d_a,
                    d_nm.mk_node(Kind::BV_AND,
                                 {d_nm.mk_node(Kind::BV_ADD, {d_d, and1}),
                                  d_nm.mk_node(Kind::BV_UDIV, {and2, d_e})})}),
      d_nm.mk_node(
          Kind::EQUAL,
          {d_a,
           d_nm.mk_node(Kind::BV_AND,
                        {d_nm.mk_node(Kind::BV_ADD, {d_d, and1_subst}),
                         d_nm.mk_node(Kind::BV_UDIV, {d_zero, d_e})})}));
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
