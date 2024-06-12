/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterBvNorm : public TestRewriter
{
};

TEST_F(TestRewriterBvNorm, norm_bv_add_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_ADD_MUL;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.invert_node(d_nm.mk_node(
                        Kind::BV_MUL, {d_bv4_a, d_nm.invert_node(d_bv4_b)})),
                    d_bv4_one}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
          d_rewriter,
          d_nm.mk_node(Kind::BV_NEG,
                       {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b})}))
          .first);
}

TEST_F(TestRewriterBvNorm, norm_bv_not_or_shl)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_NOT_OR_SHL;
  //// applies
  test_rule<kind>(d_nm.invert_node(d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.invert_node(d_bv4_a),
       d_nm.invert_node(d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a}))})));
  test_rule<kind>(d_nm.invert_node(d_nm.mk_node(
      Kind::BV_AND,
      {d_nm.invert_node(d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a})),
       d_nm.invert_node(d_bv4_a)})));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.invert_node(
      d_nm.mk_node(Kind::BV_AND,
                   {d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a}),
                    d_nm.invert_node(d_bv4_a)})));
}

TEST_F(TestRewriterBvNorm, norm_bv_shl_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_SHL_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_SHL,
                   {RewriteRule<RewriteRuleKind::BV_NEG_ELIM>::apply(
                        d_rewriter, d_nm.mk_node(Kind::BV_NEG, {d_bv4_a}))
                        .first,
                    d_bv4_b}));
}

}  // namespace bzla::test
