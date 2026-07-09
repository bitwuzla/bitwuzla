/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <gtest/gtest.h>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "node/node_utils.h"
#include "rewrite/rewrites_core.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;
using namespace bzla::node::utils;

class TestRewriterCore : public TestRewriter
{
 protected:
  void test_elim_rule_core(Kind kind, const Type& type)
  {
    test_elim_rule(kind, type);
  }
};

/* equal -------------------------------------------------------------------- */

TEST_F(TestRewriterCore, core_equal_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    Node bv4xor = d_nm.mk_node(Kind::BV_XOR, {d_bv4_a, d_bv4_b});
    Node bv4or = d_nm.mk_node(Kind::BV_NOT,
                              {d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b})});
    // lhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_false, d_b}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4xor}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, bv4or}));
    // rhs 0
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_false}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xor, d_bv4_zero}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4or, d_bv4_zero}));
    //// does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, d_bv1_a}));
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_b}));
  }
  ////// special const ones
  {
    //// applies
    Node bv4and  = d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b});
    Node bv4xnor = d_nm.mk_node(Kind::BV_XNOR, {d_bv4_a, d_bv4_b});
    // lhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_true, d_b}));
    // rhs true
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_true}));
    // lhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4and}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_ones, bv4xnor}));
    test_rule<kind>(d_nm.mk_node(
        Kind::EQUAL,
        {d_bv4_ones,
         RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, bv4xnor)
             .first}));
    // rhs ones
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4and, d_bv4_ones}));
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bv4xnor, d_bv4_ones}));
    test_rule<kind>(d_nm.mk_node(
        Kind::EQUAL,
        {RewriteRule<RewriteRuleKind::BV_XNOR_ELIM>::apply(d_rewriter, bv4xnor)
             .first,
         d_bv4_ones}));
    //// does not apply
    // ones vs neither bvand nor xnor
    test_rule_does_not_apply<kind>(d_nm.mk_node(
        Kind::EQUAL,
        {d_bv4_ones, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b})}));
    // value that is neither zero nor ones
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::EQUAL,
                     {d_nm.mk_value(BitVector(4, "0101")),
                      d_nm.mk_node(Kind::BV_XOR, {d_bv4_a, d_bv4_b})}));
  }
}

TEST_F(TestRewriterCore, core_equal_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_CONST;
  //// applies
  for (uint64_t i = 1; i < (1u << 4) - 1; ++i)
  {
    test_rule<kind>(
        d_nm.mk_node(Kind::EQUAL,
                     {d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}),
                      d_nm.mk_value(BitVector::from_ui(4, i))}));
  }
  for (uint64_t i = 1; i < (1u << 4) - 1; ++i)
  {
    test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                                 {d_nm.mk_node(Kind::BV_OR, {d_bv4_a, d_bv4_b}),
                                  d_nm.mk_value(BitVector::from_ui(4, i))}));
  }
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}), d_bv4_zero}));
  // all-ones constant (neither zero nor ones guard)
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}), d_bv4_ones}));
  // value vs neither bvand nor bvor (no slicing)
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_value(BitVector::from_ui(4, 5)), d_bv4_a}));
}

TEST_F(TestRewriterCore, core_equal_equal_const_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_EQUAL_CONST_BV1;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}), d_b}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a}), d_b}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_b, d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_b, d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a})}));
  // #b0 value exercises the e_value = mk_true() branch
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_zero}), d_b}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_zero}), d_b}));
  // bv1 equality but neither operand is a value
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_b}), d_b}));
}

TEST_F(TestRewriterCore, core_equal_true)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_TRUE;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_bv4_zero}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_b}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_bv4_one}));
}

TEST_F(TestRewriterCore, core_equal_false)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_FALSE;
  //// applies
  // (= (bvnot a) a)
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {invert_node(d_nm, d_bv4_a), d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {invert_node(d_nm, d_bv4_zero), d_bv4_zero}));
  // (= a (bvnot a))
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, invert_node(d_nm, d_bv4_zero)}));
  // (= (bvadd a c) a) with c a non-zero value
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a, d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a})}));
  // (= (bvnot (bvadd a c)) (bvnot a)) with c a non-zero value
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a}))}));
  // (= (bvadd a c0) (bvadd a c1)) with c0,c1 values and c0 != c1
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a})}));
  // (= (bvnot (bvadd a c0)) (bvnot (bvadd a c1)))
  // with c0,c1 values and c0 != c1
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_zero}), d_bv4_a}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, invert_node(d_nm, d_bv4_b)}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {invert_node(d_nm, d_bv4_a), d_bv4_b}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_zero})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_a})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  Type fun_type = d_nm.mk_fun_type({d_bv4_type, d_bv4_type});
  Node funa     = d_nm.mk_const(fun_type);
  Node funb     = d_nm.mk_const(fun_type);
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {funa, funb}));
}

TEST_F(TestRewriterCore, core_equal_ite)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_c}));
  // two ITEs with different conditions
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::ITE, {d_c, d_bv4_a, d_bv4_b})}));
}

TEST_F(TestRewriterCore, core_equal_const_bv_add)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_CONST_BV_ADD;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}), d_bv4_one}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_ones, d_bv4_a}), d_bv4_one}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_one, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_one, d_nm.mk_node(Kind::BV_ADD, {d_bv4_ones, d_bv4_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}), d_bv4_one}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}), d_bv4_b}));
}

TEST_F(TestRewriterCore, core_equal_const_bv_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_CONST_BV_MUL;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_ones}), d_bv4_one}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_bv4_a, d_nm.mk_value(BitVector::from_ui(4, 3))}),
       d_nm.mk_value(BitVector::from_ui(4, 2))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL, {d_bv4_ones, d_bv4_a}), d_bv4_one}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_value(BitVector::from_ui(4, 3)), d_bv4_a}),
       d_bv4_zero}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_one, d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_ones})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(BitVector::from_ui(4, 2)),
       d_nm.mk_node(Kind::BV_MUL,
                    {d_bv4_a, d_nm.mk_value(BitVector::from_ui(4, 3))})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_one, d_nm.mk_node(Kind::BV_MUL, {d_bv4_ones, d_bv4_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_value(BitVector::from_ui(4, 5)), d_bv4_a}),
       d_nm.mk_value(BitVector::from_ui(4, 3))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_value(BitVector::from_ui(4, 4)), d_bv4_a}),
       d_nm.mk_value(BitVector::from_ui(4, 3))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_value(BitVector::from_ui(4, 5)), d_bv4_a}),
       d_bv4_b}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_b,
       d_nm.mk_node(Kind::BV_MUL,
                    {d_nm.mk_value(BitVector::from_ui(4, 5)), d_bv4_a})}));
}

TEST_F(TestRewriterCore, core_equal_bv_add)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_ADD;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4_a, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4_a, d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_a}), d_bv4_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {invert_node(d_nm, d_bv4_a), d_bv4_b}),
       d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_SUB, {d_bv4_a, d_bv4_b}), d_bv4_a}));
}

TEST_F(TestRewriterCore, core_equal_bv_add_add)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_ADD_ADD;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SUB, {d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}), d_bv4_a}));
}

TEST_F(TestRewriterCore, core_equal_bv_sub)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_SUB;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_SUB, {d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_SUB, {d_bv4_b, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4_a, d_nm.mk_node(Kind::BV_SUB, {d_bv4_a, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_bv4_a, d_nm.mk_node(Kind::BV_SUB, {d_bv4_b, d_bv4_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_SUB, {d_bv4_a, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_SUB, {invert_node(d_nm, d_bv4_a), d_bv4_b}),
       d_bv4_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}), d_bv4_a}));
}

TEST_F(TestRewriterCore, core_equal_bv_concat)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_CONCAT;
  Node c                         = d_nm.mk_const(d_nm.mk_bv_type(8));
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_zero, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_zero, d_bv4_c}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}), c}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}), d_bv4_c}));
}

TEST_F(TestRewriterCore, core_equal_ite_same)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE_SAME;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_a, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_c, d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_fp35_a, d_nm.mk_node(Kind::ITE, {d_c, d_fp35_a, d_fp35_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_fp35_a, d_nm.mk_node(Kind::ITE, {d_c, d_fp35_b, d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_a, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
}

TEST_F(TestRewriterCore, core_equal_ite_inverted)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE_INVERTED;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_a, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})), d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_b, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})), d_b}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_bv4_b, d_bv4_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_c, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_a, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_b, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
}

TEST_F(TestRewriterCore, core_equal_ite_dis_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE_DIS_BV1;
  //// applies
  // (= (not a) a)
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_a), d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_b), d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  // (= a (not a))
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_a, d_nm.mk_node(Kind::ITE, {d_c, invert_node(d_nm, d_a), d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_b, d_nm.mk_node(Kind::ITE, {d_c, d_a, invert_node(d_nm, d_b)})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_a, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_b, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {invert_node(d_nm, d_b),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
}

TEST_F(TestRewriterCore, core_equal_inv)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_INV;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {invert_node(d_nm, d_a), invert_node(d_nm, d_b)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {invert_node(d_nm, d_bv4_a), invert_node(d_nm, d_bv4_b)}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                               {d_nm.mk_node(Kind::BV_NEG, {d_bv4_a}),
                                d_nm.mk_node(Kind::BV_NEG, {d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_b})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {invert_node(d_nm, d_a), d_b}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, invert_node(d_nm, d_bv4_b)}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_NEG, {d_bv4_a}),
                    d_nm.mk_node(Kind::BV_NOT, {d_bv4_b})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                    d_nm.mk_node(Kind::FP_ABS, {d_fp35_b})}));
}

TEST_F(TestRewriterCore, core_equal_const_bv_not)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_CONST_BV_NOT;
  Node val                       = d_nm.mk_value(BitVector(4, "0101"));
  Node bvnot                     = d_nm.mk_node(Kind::BV_NOT, {d_bv4_a});
  //// applies
  // (= value (bvnot a))  (idx 0)
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {val, bvnot}));
  // (= (bvnot a) value)  (idx 1)
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {bvnot, val}));
  //// does not apply
  // value vs non-bvnot
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {val, d_bv4_a}));
  // neither operand is a value
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {bvnot, d_nm.mk_node(Kind::BV_NOT, {d_bv4_b})}));
}

TEST_F(TestRewriterCore, core_equal_bv_comp_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_COMP_BV1;
  Node comp = d_nm.mk_node(Kind::BV_COMP, {d_bv4_a, d_bv4_b});
  //// applies
  // is_true -> EQUAL, both operand orders
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv1_one, comp}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {comp, d_bv1_one}));
  // else -> DISTINCT, both operand orders
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv1_zero, comp}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {comp, d_bv1_zero}));
  //// does not apply
  // non-value vs bvcomp
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv1_a, comp}));
  // value vs non-bvcomp
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a}));
}

TEST_F(TestRewriterCore, core_equal_bv_mul_udiv_zero)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_MUL_UDIV_ZERO;
  Node udiv = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_b});
  Node mul0 = d_nm.mk_node(Kind::BV_MUL, {udiv, d_bv4_b});  // udiv at mul[0]
  Node mul1 = d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, udiv});  // udiv at mul[1]
  //// applies (mul-side x udiv-side positions)
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {mul0, d_bv4_zero}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {mul1, d_bv4_zero}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, mul0}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, mul1}));
  //// does not apply
  // value is not zero
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {mul0, d_bv4_one}));
  // udiv[1] != t
  Node mul_bad = d_nm.mk_node(Kind::BV_MUL, {udiv, d_bv4_c});
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {mul_bad, d_bv4_zero}));
}

TEST_F(TestRewriterCore, core_equal_ite_lift_cond)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE_LIFT_COND;
  //// applies
  // bv1: (= v (ite c v w)) -> c
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv1_one, d_nm.mk_node(Kind::ITE, {d_c, d_bv1_one, d_bv1_zero})}));
  // bv1: (= v (ite c w v)) -> !c
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv1_one, d_nm.mk_node(Kind::ITE, {d_c, d_bv1_zero, d_bv1_one})}));
  // value on rhs (exercises idx1)
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_c, d_bv1_one, d_bv1_zero}), d_bv1_one}));
  // bool: (= v (ite c v w)) -> c
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_true, d_nm.mk_node(Kind::ITE, {d_c, d_true, d_false})}));
  // bool: (= v (ite c w v)) -> !c
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_true, d_nm.mk_node(Kind::ITE, {d_c, d_false, d_true})}));
  //// does not apply
  // node[idx0] is not a value
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv1_a, d_nm.mk_node(Kind::ITE, {d_c, d_bv1_one, d_bv1_zero})}));
  // ite branches are not both values
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv1_one, d_nm.mk_node(Kind::ITE, {d_c, d_bv1_a, d_bv1_zero})}));
  // value matches neither branch
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_value(BitVector(4, "0101")),
                    d_nm.mk_node(Kind::ITE, {d_c, d_bv4_zero, d_bv4_ones})}));
}

TEST_F(TestRewriterCore, core_equal_bv_udiv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_BV_UDIV1;
  Node udiv = d_nm.mk_node(Kind::BV_UDIV, {d_bv4_ones, d_bv4_a});
  //// applies
  // (= 0 (bvudiv ~0 t))
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, udiv}));
  // (= (bvudiv ~0 t) 0)
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL, {udiv, d_bv4_zero}));
  //// does not apply
  // not a bit-vector equality
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_a, d_b}));
  // value is not zero
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_one, udiv}));
  // udiv numerator is not ones
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_zero, d_nm.mk_node(Kind::BV_UDIV, {d_bv4_one, d_bv4_a})}));
}

/* distinct ----------------------------------------------------------------- */

TEST_F(TestRewriterCore, core_distinct_card)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::DISTINCT_CARD;

  {
    Type t = d_nm.mk_bool_type();
    Node a = d_nm.mk_const(t);
    Node b = d_nm.mk_const(t);
    Node c = d_nm.mk_const(t);
    // applies
    test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, c}));
    // does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b}));
  }

  {
    Type t = d_nm.mk_bv_type(2);
    Node a = d_nm.mk_const(t);
    Node b = d_nm.mk_const(t);
    Node c = d_nm.mk_const(t);
    Node d = d_nm.mk_const(t);
    Node e = d_nm.mk_const(t);
    // applies
    test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, c, d, e}));
    // does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, d, d}));
  }

  {
    Type t = d_nm.mk_rm_type();
    Node a = d_nm.mk_const(t);
    Node b = d_nm.mk_const(t);
    Node c = d_nm.mk_const(t);
    Node d = d_nm.mk_const(t);
    Node e = d_nm.mk_const(t);
    Node f = d_nm.mk_const(t);
    // applies
    test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, c, d, e, f}));
    // does not apply
    test_rule_does_not_apply<kind>(
        d_nm.mk_node(Kind::DISTINCT, {a, b, c, d, e}));
  }

  // Only run this test with external solver binary, not with internal
  // solving context. We disable rewriting and preprocessing in the internal
  // solving context and thus this test is too slow.
  if (s_solver_binary == nullptr)
  {
    GTEST_SKIP();
  }
  {
    Type t = d_nm.mk_fp_type(3, 8);
    // |fp(3, 8)| = 3 + 2^8 * (2^3 - 1) = 1795
    const uint64_t card = 1795;
    std::vector<Node> nodes;
    for (uint64_t i = 0; i <= card; ++i)
    {
      nodes.push_back(d_nm.mk_const(t));
    }

    // applies
    test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, nodes));
    // does not apply
    nodes.pop_back();
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, nodes));
  }
}

/* distinct_n --------------------------------------------------------------- */

TEST_F(TestRewriterCore, core_distinct_n_false)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::DISTINCT_N_FALSE;
  Node n3                        = d_nm.mk_value(BitVector::from_ui(4, 3));
  Node n2                        = d_nm.mk_value(BitVector::from_ui(4, 2));
  //// applies: (num_children - 1) < N  -->  false
  // DISTINCT_N(3, a, b): 2 elements < 3
  test_rule<kind>(d_nm.mk_node(Kind::DISTINCT_N, {n3, d_bv4_a, d_bv4_b}));
  //// does not apply: (num_children - 1) >= N
  // DISTINCT_N(2, a, b): 2 elements, not < 2
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::DISTINCT_N, {n2, d_bv4_a, d_bv4_b}));
}

/* ite ---------------------------------------------------------------------- */

TEST_F(TestRewriterCore, core_ite_same)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_SAME;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}));
}

TEST_F(TestRewriterCore, core_ite_then_ite1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_THEN_ITE1;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_c}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE, {d_b, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b}), d_c}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_bv4_c}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b})), d_c}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_c}));
}

TEST_F(TestRewriterCore, core_ite_then_ite2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_THEN_ITE2;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_b, invert_node(d_nm, d_bv4_a), d_bv4_b})),
       d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_a, invert_node(d_nm, d_bv4_a), d_bv4_b})),
       d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE, {d_b, invert_node(d_nm, d_a), d_b})),
       d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b})),
                    invert_node(d_nm, d_a)}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_bv4_a}));
}

TEST_F(TestRewriterCore, core_ite_then_ite3)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_THEN_ITE3;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a}), d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, invert_node(d_nm, d_bv4_a)})),
       d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, invert_node(d_nm, d_bv4_a)})),
       d_bv4_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE, {d_b, d_b, invert_node(d_nm, d_a)})),
       d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a})),
       invert_node(d_nm, d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_b, d_a})),
                    invert_node(d_nm, d_a)}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE, {d_b, d_b, invert_node(d_nm, d_a)})),
       invert_node(d_nm, d_a)}));
}

TEST_F(TestRewriterCore, core_ite_else_ite1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_ELSE_ITE1;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, d_bv4_c, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE, {d_b, d_c, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b,
       d_bv4_c,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, d_c, invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_c}));
}

TEST_F(TestRewriterCore, core_ite_else_ite2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_ELSE_ITE2;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE,
                                {d_b, invert_node(d_nm, d_bv4_a), d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE,
                                {d_a, invert_node(d_nm, d_bv4_a), d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_b, invert_node(d_nm, d_a), d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
}

TEST_F(TestRewriterCore, core_ite_else_ite3)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_ELSE_ITE3;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE,
                                {d_b, d_bv4_b, invert_node(d_nm, d_bv4_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::ITE,
                                {d_a, d_bv4_b, invert_node(d_nm, d_bv4_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_a,
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_b, d_b, invert_node(d_nm, d_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_bv4_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_a),
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_b, d_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       invert_node(d_nm, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       invert_node(d_nm, d_a),
       invert_node(
           d_nm,
           d_nm.mk_node(Kind::ITE, {d_b, d_b, invert_node(d_nm, d_a)}))}));
}

TEST_F(TestRewriterCore, core_ite_bool)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_BOOL;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE, {d_c, d_bv4_a, d_bv4_b}));
}

TEST_F(TestRewriterCore, core_ite_concat)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_BV_CONCAT;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {invert_node(d_nm, d_bv4_a), d_bv4_c})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, invert_node(d_nm, d_bv4_b)})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.mk_node(Kind::BV_CONCAT, {invert_node(d_nm, d_bv4_a), d_bv4_b}),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, invert_node(d_nm, d_bv4_b)}),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::BV_CONCAT,
                                {invert_node(d_nm, d_bv4_a), d_bv4_b})),
       invert_node(d_nm,
                   d_nm.mk_node(Kind::BV_CONCAT,
                                {invert_node(d_nm, d_bv4_a), d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm,
                   d_nm.mk_node(Kind::BV_CONCAT,
                                {d_bv4_a, invert_node(d_nm, d_bv4_b)})),
       invert_node(d_nm,
                   d_nm.mk_node(Kind::BV_CONCAT,
                                {d_bv4_c, invert_node(d_nm, d_bv4_b)}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       invert_node(d_nm,
                   d_nm.mk_node(Kind::BV_CONCAT,
                                {d_bv4_c, invert_node(d_nm, d_bv4_b)}))}));
}

TEST_F(TestRewriterCore, core_ite_bv_op)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_BV_OP;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_c, d_bv4_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_c, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_b, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_c, d_bv4_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_c, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_c, d_bv4_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UREM, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UREM, {d_bv4_a, d_bv4_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UREM, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UREM, {d_bv4_c, d_bv4_b})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_AND, {d_bv4_a, d_bv4_c})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       invert_node(d_nm, d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_b, d_bv4_c})}));
}

TEST_F(TestRewriterCore, core_ite_cond_equal)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_COND_EQUAL;
  //// applies
  // value on the rhs of the condition (idx 1)
  // bv1: (ite (= t #b1) #b1 (bvnot #b1)) -> t
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}),
                                d_bv1_one,
                                d_bv1_zero}));
  // bv1: (ite (= t #b0) #b0 (bvnot #b0)) -> t
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_zero}),
                    d_bv1_zero,
                    d_bv1_one}));
  // bool: (ite (= t true) true (not true)) -> t
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE, {d_nm.mk_node(Kind::EQUAL, {d_a, d_true}), d_true, d_false}));
  // value on the lhs of the condition (idx 0)
  // bv1: (ite (= #b1 t) #b1 (bvnot #b1)) -> t
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a}),
                                d_bv1_one,
                                d_bv1_zero}));
  //// does not apply
  // node type is neither bv1 nor bool
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL,
                    {d_bv4_a, d_nm.mk_value(BitVector(4, "0101"))}),
       d_nm.mk_value(BitVector(4, "0101")),
       d_nm.mk_node(Kind::BV_NOT, {d_nm.mk_value(BitVector(4, "0101"))})}));
  // condition operands are not values
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_b}), d_bv1_a, d_bv1_b}));
  // else branch is not the inverse of the value
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}), d_bv1_one, d_bv1_one}));
}

TEST_F(TestRewriterCore, core_ite_bool_to_bv1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_BOOL_TO_BV1;
  //// applies
  // node[0][0] value, == then -> t
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a}),
                                d_bv1_one,
                                d_bv1_zero}));
  // node[0][0] value, == else -> (bvnot t)
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_one, d_bv1_a}),
                                d_bv1_zero,
                                d_bv1_one}));
  // node[0][1] value, == then -> t
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}),
                                d_bv1_one,
                                d_bv1_zero}));
  // node[0][1] value, == else -> (bvnot t)
  test_rule<kind>(d_nm.mk_node(Kind::ITE,
                               {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}),
                                d_bv1_zero,
                                d_bv1_one}));
  //// does not apply
  // condition is not an equality
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE, {d_c, d_bv1_one, d_bv1_zero}));
  // branches are not values
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL, {d_bv1_a, d_bv1_one}), d_bv1_b, d_bv1_zero}));
  // equality operand is not bv1
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL,
                    {d_bv4_a, d_nm.mk_value(BitVector(4, "0101"))}),
       d_bv1_one,
       d_bv1_zero}));
}

/* --- Evaluation (Constant Folding) Rules----------------------------------- */

TEST_F(TestRewriterCore, core_equal_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_EVAL;
  // applies
  Node equal0 = d_nm.mk_node(Kind::EQUAL, {d_true, d_true});
  test_rewrite(equal0, d_true);
  test_rewrite(d_nm.mk_node(Kind::EQUAL, {equal0, d_false}), d_false);

  Node equal1 = d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_value(BitVector(2, "00")), d_nm.mk_value(BitVector(2, "00"))});
  test_rewrite(equal1, d_true);
  test_rewrite(d_nm.mk_node(Kind::EQUAL, {equal1, d_false}), d_false);

  test_rewrite(d_nm.mk_node(Kind::EQUAL,
                            {d_nm.mk_value(BitVector(2, "10")),
                             d_nm.mk_value(BitVector(2, "00"))}),
               d_false);
  test_rewrite(
      d_nm.mk_node(
          Kind::EQUAL,
          {d_nm.mk_value(FloatingPoint::fpzero(
               d_fp35_type.fp_exp_size(), d_fp35_type.fp_sig_size(), false)),
           d_nm.mk_value(FloatingPoint::fpzero(
               d_fp35_type.fp_exp_size(), d_fp35_type.fp_sig_size(), true))}),
      d_false);
  test_rewrite(d_nm.mk_node(Kind::EQUAL,
                            {d_nm.mk_value(RoundingMode::RNA),
                             d_nm.mk_value(RoundingMode::RNA)}),
               d_true);
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_false}));
}

TEST_F(TestRewriterCore, core_distinct_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::DISTINCT_EVAL;
  // applies
  Node dist0 = d_nm.mk_node(Kind::DISTINCT, {d_true, d_true});
  test_rewrite(dist0, d_false);
  Node dist1 = d_nm.mk_node(Kind::DISTINCT, {d_true, d_false});
  test_rewrite(dist1, d_true);
  test_rewrite(d_nm.mk_node(Kind::DISTINCT, {dist0, d_false}), d_false);
  test_rewrite(d_nm.mk_node(Kind::DISTINCT, {dist1, d_false}), d_true);

  Node dist2 = d_nm.mk_node(
      Kind::DISTINCT,
      {d_nm.mk_value(BitVector(2, "01")), d_nm.mk_value(BitVector(2, "00"))});
  test_rewrite(dist2, d_true);
  test_rewrite(d_nm.mk_node(Kind::DISTINCT, {dist2, d_false}), d_true);

  test_rewrite(d_nm.mk_node(Kind::DISTINCT,
                            {d_nm.mk_value(BitVector(2, "00")),
                             d_nm.mk_value(BitVector(2, "00"))}),
               d_false);
  test_rewrite(
      d_nm.mk_node(
          Kind::DISTINCT,
          {d_nm.mk_value(FloatingPoint::fpzero(
               d_fp35_type.fp_exp_size(), d_fp35_type.fp_sig_size(), false)),
           d_nm.mk_value(FloatingPoint::fpzero(
               d_fp35_type.fp_exp_size(), d_fp35_type.fp_sig_size(), true))}),
      d_true);
  test_rewrite(d_nm.mk_node(Kind::DISTINCT,
                            {d_nm.mk_value(RoundingMode::RNA),
                             d_nm.mk_value(RoundingMode::RNA)}),
               d_false);
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, {d_b, d_false}));
}

TEST_F(TestRewriterCore, core_ite_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::ITE_EVAL;
  //// applies
  test_rewrite(
      d_rewriter.rewrite(d_nm.mk_node(Kind::ITE, {d_true, d_bv4_a, d_bv4_b})),
      d_bv4_a);
  test_rewrite(
      d_rewriter.rewrite(d_nm.mk_node(Kind::ITE, {d_false, d_bv4_a, d_bv4_b})),
      d_bv4_b);
  test_rewrite(
      d_rewriter.rewrite(d_nm.mk_node(
          Kind::ITE,
          {d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_a}), d_bv4_a, d_bv4_b})),
      d_bv4_a);
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_b}), d_bv4_a, d_bv4_b}));
}

/* -------------------------------------------------------------------------- */

TEST_F(TestRewriterCore, rewrite_cache_growth)
{
  // Rewriting a large nested expression grows the rewrite cache, triggering
  // rehashes of the underlying unordered_map during the recursive _rewrite()
  // call. This exercises the path where rewrite() must re-fetch its cache
  // iterator before assigning the result (writing through a stale iterator is
  // UB; see rewriter.cpp). Verify the cached result is correct.
  const uint64_t n = 1000;
  Node one         = d_nm.mk_value(BitVector::mk_one(4));
  Node acc         = d_nm.mk_value(BitVector::mk_zero(4));
  for (uint64_t i = 0; i < n; ++i)
  {
    acc = d_nm.mk_node(Kind::BV_ADD, {one, acc});
  }
  Node res = d_rewriter.rewrite(acc);
  ASSERT_TRUE(res.is_value());
  ASSERT_EQ(res.value<BitVector>(), BitVector::from_ui(4, n % 16));
  // Re-rewriting the cached value is stable.
  ASSERT_EQ(d_rewriter.rewrite(res), res);
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterCore, core_distinct_elim)
{
  test_elim_rule_core(Kind::DISTINCT, d_bool_type);
}

/* --- Commutative Operator Normalization ----------------------------------- */

TEST_F(TestRewriterCore, core_normalize_comm)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORMALIZE_COMM;
  Node cnt                       = d_nm.mk_value(BitVector::from_ui(4, 2));
  //// applies
  // commutative 2-ary: swap when node[0].id() > node[1].id()
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_a}));
  // commutative n-ary (>= 3): sort children (DISTINCT)
  test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {d_bv4_c, d_bv4_b, d_bv4_a}));
  // DISTINCT_N: sort children (skipping cardinality operand at index 0)
  test_rule<kind>(
      d_nm.mk_node(Kind::DISTINCT_N, {cnt, d_bv4_c, d_bv4_b, d_bv4_a}));
  // FP_ADD: swap operands when node[1].id() > node[2].id()
  test_rule<kind>(d_nm.mk_node(Kind::FP_ADD, {d_rm, d_fp35_b, d_fp35_a}));
  // FP_MUL: swap operands when node[1].id() > node[2].id()
  test_rule<kind>(d_nm.mk_node(Kind::FP_MUL, {d_rm, d_fp35_b, d_fp35_a}));
  // FP_FMA: swap first two operands when node[1].id() > node[2].id()
  Node fp_c = d_nm.mk_const(d_fp35_type, "c_fp35");
  test_rule<kind>(d_nm.mk_node(Kind::FP_FMA, {d_rm, d_fp35_b, d_fp35_a, fp_c}));
  //// does not apply
  // non-commutative, non-FP operator
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SUB, {d_bv4_a, d_bv4_b}));
  // commutative 2-ary already ordered (node[0].id() < node[1].id())
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b}));
  // FP_ADD already ordered
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_ADD, {d_rm, d_fp35_a, d_fp35_b}));
}

/* --- Quantifiers ---------------------------------------------------------- */

TEST_F(TestRewriterCore, core_exists_elim)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EXISTS_ELIM;
  Node x                         = d_nm.mk_var(d_bv4_type);
  Node body                      = d_nm.mk_node(Kind::EQUAL, {x, d_bv4_zero});
  Node ex                        = d_nm.mk_node(Kind::EXISTS, {x, body});
  //// applies: exists x. P  -->  not (forall x. not P)
  test_rule<kind>(ex);
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
