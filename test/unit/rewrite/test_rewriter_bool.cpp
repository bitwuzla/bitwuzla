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
#include "node/node_manager.h"
#include "rewrite/rewriter.h"
#include "rewrite/rewrites_bool.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBool : public TestRewriter
{
 protected:
  void test_elim_rule_bool(Kind kind) { test_elim_rule(kind, d_bool_type); }
};

/* and ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_and_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_EVAL;
  // applies
  Node and0 = d_nm.mk_node(Kind::AND, {d_true, d_true});
  test_rewrite(and0, d_true);
  test_rewrite(d_nm.mk_node(Kind::AND, {and0, d_false}), d_false);
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_b, d_false}));
}

TEST_F(TestRewriterBool, bool_and_special_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_SPECIAL_CONST;
  ////// special const false
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::AND, {d_false, d_a}));
    test_rule<kind>(d_nm.mk_node(Kind::AND, {d_a, d_false}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_a, d_a}));
  }
  ////// special const true
  {
    //// applies
    test_rule<kind>(d_nm.mk_node(Kind::AND, {d_true, d_a}));
    test_rule<kind>(d_nm.mk_node(Kind::AND, {d_a, d_true}));
    //// does not apply
    test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_b, d_a}));
  }
}

TEST_F(TestRewriterBool, bool_and_const)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_CONST;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_false, d_nm.mk_node(Kind::AND, {d_true, d_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_false, d_nm.mk_node(Kind::AND, {d_a, d_true})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.mk_node(Kind::AND, {d_false, d_a}), d_true}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.mk_node(Kind::AND, {d_a, d_true}), d_false}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND, {d_false, d_nm.mk_node(Kind::OR, {d_true, d_a})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND, {d_false, d_nm.mk_node(Kind::AND, {d_b, d_a})}));
}

TEST_F(TestRewriterBool, bool_and_idem1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_IDEM1;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::AND, {d_a, d_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_a, d_b}));
}

TEST_F(TestRewriterBool, bool_and_idem2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_IDEM2;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                                d_nm.mk_node(Kind::AND, {d_a, d_c})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                                d_nm.mk_node(Kind::AND, {d_c, d_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                                d_nm.mk_node(Kind::AND, {d_a, d_c})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                                d_nm.mk_node(Kind::AND, {d_c, d_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_a, d_b}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})),
                    d_nm.mk_node(Kind::AND, {d_a, d_c})}));
}

TEST_F(TestRewriterBool, bool_and_contra1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_CONTRA1;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_a}));
  test_rule<kind>(d_nm.mk_node(Kind::AND, {d_a, d_nm.invert_node(d_a)}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::AND, {d_a, d_a}));
}

TEST_F(TestRewriterBool, bool_and_contra2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_CONTRA2;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_b}),
                    d_nm.mk_node(Kind::AND, {d_a, d_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.mk_node(Kind::AND, {d_c, d_nm.invert_node(d_a)})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_b}),
                    d_nm.mk_node(Kind::AND, {d_c, d_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                    d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_nm.invert_node(d_a)}),
                    d_nm.mk_node(Kind::AND, {d_a, d_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                    d_nm.mk_node(Kind::AND, {d_c, d_nm.invert_node(d_a)})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_nm.invert_node(d_a)}),
                    d_nm.mk_node(Kind::AND, {d_c, d_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.mk_node(Kind::AND, {d_a, d_c})}));
}

TEST_F(TestRewriterBool, bool_and_contra3)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_CONTRA3;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_a, d_nm.mk_node(Kind::AND, {d_nm.invert_node(d_a), d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_a, d_nm.mk_node(Kind::AND, {d_b, d_nm.invert_node(d_a)})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.invert_node(d_a), d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.invert_node(d_a), d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND, {d_a, d_nm.mk_node(Kind::AND, {d_a, d_b})}));
}

TEST_F(TestRewriterBool, bool_and_subsum1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_SUBSUM1;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_a, d_b}),
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_a), d_nm.invert_node(d_c)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_a), d_nm.invert_node(d_c)})),
       d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                                d_nm.mk_node(Kind::OR, {d_a, d_c})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::OR, {d_a, d_c}),
                                d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_a, d_b}),
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_a)})),
       d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                                d_nm.mk_node(Kind::OR, {d_c, d_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::OR, {d_c, d_a}),
                                d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_b, d_a}),
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_a), d_nm.invert_node(d_c)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_a), d_nm.invert_node(d_c)})),
       d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                                d_nm.mk_node(Kind::OR, {d_a, d_c})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::OR, {d_a, d_c}),
                                d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_b, d_a}),
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_a)}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_a)})),
       d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                                d_nm.mk_node(Kind::OR, {d_c, d_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::AND,
                               {d_nm.mk_node(Kind::OR, {d_c, d_a}),
                                d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_a, d_b}),
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_d)}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::AND, {d_a, d_b}),
       d_nm.mk_node(Kind::AND,
                    {d_nm.invert_node(d_a), d_nm.invert_node(d_c)})}));
}

TEST_F(TestRewriterBool, bool_and_subsum2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_SUBSUM2;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_a), d_nm.invert_node(d_b)}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::OR, {d_a, d_b}), d_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_a, d_nm.mk_node(Kind::OR, {d_a, d_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::OR, {d_a, d_b}), d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_b), d_nm.invert_node(d_a)}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::OR, {d_b, d_a}), d_a}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_a, d_nm.mk_node(Kind::OR, {d_b, d_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::OR, {d_b, d_a}), d_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_b), d_nm.invert_node(d_c)}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_a,
       d_nm.invert_node(d_nm.mk_node(
           Kind::AND, {d_nm.invert_node(d_c), d_nm.invert_node(d_d)}))}));
}

TEST_F(TestRewriterBool, bool_and_not_and1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_NOT_AND1;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_c}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_c, d_a}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_c}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_b, d_a}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_c, d_a}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_c})),
                    d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_c, d_a})),
                    d_nm.mk_node(Kind::AND, {d_a, d_b})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_c})),
                    d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_c, d_a})),
                    d_nm.mk_node(Kind::AND, {d_b, d_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_c, d_d}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.invert_node(d_nm.mk_node(
                        Kind::AND, {d_nm.invert_node(d_a), d_c}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.mk_node(Kind::AND, {d_a, d_c})}));
}

TEST_F(TestRewriterBool, bool_and_not_and2)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_NOT_AND2;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_a, d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_b, d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})), d_a}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})), d_b}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND, {d_a, d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_b, d_c}))}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND, {d_a, d_nm.mk_node(Kind::AND, {d_a, d_b})}));
}

TEST_F(TestRewriterBool, bool_and_idem3)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_IDEM3;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_a, d_nm.mk_node(Kind::AND, {d_a, d_c})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND, {d_nm.mk_node(Kind::AND, {d_a, d_c}), d_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND, {d_nm.invert_node(d_a), d_nm.mk_node(Kind::AND, {d_a, d_c})}));
}

TEST_F(TestRewriterBool, and_bv_lt_false)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_BV_LT_FALSE;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_SLT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_c})}));
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::BV_SLT, {d_bv4_a, d_bv4_c}),
                    d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a})}));
}

TEST_F(TestRewriterBool, and_bv_lt)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_BV_LT;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_a}))}));
  test_rule<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b}),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_a}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b})),
       d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_a})}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_a, d_bv4_b})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_ULT, {d_bv4_b, d_bv4_c}))}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_a, d_bv4_c})),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_SLT, {d_bv4_b, d_bv4_a}))}));
}

TEST_F(TestRewriterBool, bool_and_resol1)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::AND_RESOL1;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})),

                    d_nm.invert_node(d_nm.mk_node(
                        Kind::AND, {d_a, d_nm.invert_node(d_b)}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {

                       d_nm.invert_node(d_nm.mk_node(
                           Kind::AND, {d_a, d_nm.invert_node(d_b)})),
                       d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})),

                    d_nm.invert_node(d_nm.mk_node(
                        Kind::AND, {d_nm.invert_node(d_b), d_a}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {

                       d_nm.invert_node(d_nm.mk_node(
                           Kind::AND, {d_nm.invert_node(d_b), d_a})),
                       d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})),

                    d_nm.invert_node(d_nm.mk_node(
                        Kind::AND, {d_b, d_nm.invert_node(d_a)}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {

                       d_nm.invert_node(d_nm.mk_node(
                           Kind::AND, {d_b, d_nm.invert_node(d_a)})),
                       d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b})),

                    d_nm.invert_node(d_nm.mk_node(
                        Kind::AND, {d_nm.invert_node(d_a), d_b}))}));
  test_rule<kind>(
      d_nm.mk_node(Kind::AND,
                   {

                       d_nm.invert_node(d_nm.mk_node(
                           Kind::AND, {d_nm.invert_node(d_a), d_b})),
                       d_nm.invert_node(d_nm.mk_node(Kind::AND, {d_a, d_b}))}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::AND,
                   {d_nm.mk_node(Kind::AND, {d_a, d_b}),
                    d_nm.mk_node(Kind::AND, {d_a, d_nm.invert_node(d_b)})}));
}

/* not ---------------------------------------------------------------------- */

TEST_F(TestRewriterBool, bool_not_eval)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NOT_EVAL;
  // applies
  Node not0 = d_nm.mk_node(Kind::NOT, {d_false});
  test_rewrite(not0, d_true);
  test_rewrite(d_nm.mk_node(Kind::NOT, {not0}), d_false);
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::NOT, {d_b}));
}

TEST_F(TestRewriterBool, bool_not_not)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NOT_NOT;
  // applies
  Node not0 = d_nm.mk_node(Kind::NOT, {d_nm.mk_node(Kind::NOT, {d_b})});
  test_rewrite(not0, d_b);
  test_rewrite(d_nm.mk_node(Kind::NOT, {not0}), d_nm.mk_node(Kind::NOT, {d_b}));
  // does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::NOT, {d_b}));
}

TEST_F(TestRewriterBool, bool_not_xor)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NOT_XOR;
  //// applies
  test_rule<kind>(d_nm.invert_node(d_nm.mk_node(Kind::XOR, {d_a, d_b})));
  test_rule<kind>(
      d_nm.invert_node(d_nm.mk_node(Kind::XOR, {d_nm.invert_node(d_a), d_b})));
  test_rule<kind>(d_nm.invert_node(
      d_nm.mk_node(Kind::XOR, {d_nm.invert_node(d_a), d_nm.invert_node(d_b)})));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.invert_node(d_nm.mk_node(Kind::OR, {d_a, d_b})));
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterBool, bool_implies_elim)
{
  test_elim_rule_bool(Kind::IMPLIES);
}

TEST_F(TestRewriterBool, bool_or_elim) { test_elim_rule_bool(Kind::OR); }

TEST_F(TestRewriterBool, bool_xor_elim) { test_elim_rule_bool(Kind::XOR); }

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
