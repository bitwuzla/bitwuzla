/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "bv/bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "rewrite/rewrites_core.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"
#include "test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterCore : public TestRewriter
{
 protected:
  void test_elim_rule_core(Kind kind, const Type& type)
  {
    test_elim_rule(kind, type);
  }
};

/* equal -------------------------------------------------------------------- */

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
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, false)),
                    d_nm.mk_value(FloatingPoint::fpzero(d_fp35_type, true))}),
      d_false);
  test_rewrite(d_nm.mk_node(Kind::EQUAL,
                            {d_nm.mk_value(RoundingMode::RNA),
                             d_nm.mk_value(RoundingMode::RNA)}),
               d_true);
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_b, d_false}));
}

TEST_F(TestRewriterCore, core_equal_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_SPECIAL_CONST;
  ////// special const 0
  {
    //// applies
    Node bv4xor = d_nm.mk_node(Kind::BV_XOR, {d_bv4_a, d_bv4_b});
    Node bv4or  = d_nm.mk_node(Kind::BV_NOT,
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
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_zero}), d_b}));
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
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4_a), d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4_zero), d_bv4_zero}));
  // (= a (bvnot a))
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_zero, d_nm.invert_node(d_bv4_zero)}));
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
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a}))}));
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
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_one, d_bv4_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_zero}), d_bv4_a}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_nm.invert_node(d_bv4_b)}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_bv4_a), d_bv4_b}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_zero})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_zero, d_bv4_a}))}));
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
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_one})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_b, d_bv4_ones}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_a})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_ones}))}));
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
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_d}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::ITE, {d_b, d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_c}));
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
      {d_nm.mk_node(Kind::BV_ADD, {d_nm.invert_node(d_bv4_a), d_bv4_b}),
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
      {d_nm.mk_node(Kind::BV_SUB, {d_nm.invert_node(d_bv4_a), d_bv4_b}),
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
      {d_a, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
}

TEST_F(TestRewriterCore, core_equal_ite_inverted)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_ITE_INVERTED;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_a, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})), d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_b, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})), d_b}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_bv4_b, d_bv4_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_c, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
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
      {d_nm.invert_node(d_a), d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_b), d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  // (= a (not a))
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_a, d_nm.mk_node(Kind::ITE, {d_c, d_nm.invert_node(d_a), d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_b, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_nm.invert_node(d_b)})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_a, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_b, d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::EQUAL,
      {d_nm.invert_node(d_b),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_c, d_a, d_b}))}));
}

TEST_F(TestRewriterCore, core_equal_inv)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::EQUAL_INV;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                               {d_nm.invert_node(d_a), d_nm.invert_node(d_b)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::EQUAL, {d_nm.invert_node(d_bv4_a), d_nm.invert_node(d_bv4_b)}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                               {d_nm.mk_node(Kind::BV_NEG, {d_bv4_a}),
                                d_nm.mk_node(Kind::BV_NEG, {d_bv4_b})}));
  test_rule<kind>(d_nm.mk_node(Kind::EQUAL,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_b})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_nm.invert_node(d_a), d_b}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL, {d_bv4_a, d_nm.invert_node(d_bv4_b)}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::BV_NEG, {d_bv4_a}),
                    d_nm.mk_node(Kind::BV_NOT, {d_bv4_b})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::EQUAL,
                   {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                    d_nm.mk_node(Kind::FP_ABS, {d_fp35_b})}));
}

/* distinct ----------------------------------------------------------------- */

TEST_F(TestRewriterCore, core_distinct_card)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::DISTINCT_CARD;
  Type bv2_type                  = d_nm.mk_bv_type(2);
  Node a                         = d_nm.mk_const(bv2_type);
  Node b                         = d_nm.mk_const(bv2_type);
  Node c                         = d_nm.mk_const(bv2_type);
  Node d                         = d_nm.mk_const(bv2_type);
  Node e                         = d_nm.mk_const(bv2_type);
  // applies
  test_rule<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, c, d, e}));
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::DISTINCT, {a, b, d, d}));
}

/* ite ---------------------------------------------------------------------- */

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
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_bv4_c}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b})), d_c}));
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
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_nm.invert_node(d_bv4_a), d_bv4_b})),
                    d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_a, d_nm.invert_node(d_bv4_a), d_bv4_b})),
                    d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_nm.invert_node(d_a), d_b})),
                    d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b})),
                    d_nm.invert_node(d_a)}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
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
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_bv4_b, d_nm.invert_node(d_bv4_a)})),
                    d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_a, d_bv4_b, d_nm.invert_node(d_bv4_a)})),
                    d_bv4_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_b, d_nm.invert_node(d_a)})),
                    d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a})),
       d_nm.invert_node(d_bv4_a)}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_b, d_a})),
                    d_nm.invert_node(d_a)}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}), d_bv4_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})),
       d_bv4_a}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_b, d_nm.invert_node(d_a)})),
                    d_nm.invert_node(d_a)}));
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
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_b, d_c, d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b}))}));
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
       d_nm.invert_node(d_nm.mk_node(
           Kind::ITE, {d_b, d_nm.invert_node(d_bv4_a), d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::ITE, {d_a, d_nm.invert_node(d_bv4_a), d_bv4_b}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_nm.invert_node(d_a), d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_a, d_bv4_a, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_a, d_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
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
       d_nm.invert_node(d_nm.mk_node(
           Kind::ITE, {d_b, d_bv4_b, d_nm.invert_node(d_bv4_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::ITE, {d_a, d_bv4_b, d_nm.invert_node(d_bv4_a)}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_a,
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_b, d_nm.invert_node(d_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_b, d_bv4_a}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_a, d_bv4_b, d_bv4_a}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_nm.invert_node(d_a),
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_b, d_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a, d_bv4_a, d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_a,
       d_bv4_a,
       d_nm.invert_node(d_nm.mk_node(Kind::ITE, {d_b, d_bv4_a, d_bv4_b}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_a,
                    d_nm.invert_node(d_a),
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::ITE, {d_b, d_b, d_nm.invert_node(d_a)}))}));
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
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {d_nm.invert_node(d_bv4_a), d_bv4_c})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_nm.invert_node(d_bv4_b)})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.mk_node(Kind::BV_CONCAT, {d_nm.invert_node(d_bv4_a), d_bv4_b}),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_nm.invert_node(d_bv4_b)}),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(
           d_nm.mk_node(Kind::BV_CONCAT, {d_nm.invert_node(d_bv4_a), d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT,
                                     {d_nm.invert_node(d_bv4_a), d_bv4_c}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(
           d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_nm.invert_node(d_bv4_b)})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT,
                                     {d_bv4_c, d_nm.invert_node(d_bv4_b)}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_c, d_bv4_d})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_c})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::ITE,
      {d_c,
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_CONCAT,
                                     {d_bv4_c, d_nm.invert_node(d_bv4_b)}))}));
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
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_ADD, {d_bv4_a, d_bv4_c})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::ITE,
                   {d_c,
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_UDIV, {d_bv4_b, d_bv4_c})}));
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterCore, core_distinct_elim)
{
  test_elim_rule_core(Kind::DISTINCT, d_bool_type);
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
