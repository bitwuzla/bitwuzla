/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_utils.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;
using namespace bzla::node::utils;

class TestRewriterBvNorm : public TestRewriter
{
 protected:
  /**
   * Like test_rule(), but applies the rule with a LEVEL_ARITHMETIC rewriter.
   *
   * The reverse normalization rules (NORM_BV_EXTRACT_ADD_MUL_REV*,
   * NORM_BV_MUL_POW2_REV) only fire at Rewriter::LEVEL_ARITHMETIC, which is the
   * level the normalize preprocessing pass uses. At the default LEVEL_MAX
   * their forward counterpart (BV_EXTRACT_ADD_MUL, BV_MUL_POW2) is enabled and,
   * since the rule builds its result via rewriter.mk_node(), immediately
   * rewrites the result back to the input node. The dispatch gating on
   * d_arithmetic (see Rewriter::rewrite_bv_*) disables the forward rules at
   * LEVEL_ARITHMETIC so the reverse result survives.
   */
  template <RewriteRuleKind K>
  void test_rule_arith(const Node& node)
  {
    Env env(d_nm, d_sat_factory);
    Rewriter rewriter(env, Rewriter::LEVEL_ARITHMETIC);
    Node res = RewriteRule<K>::apply(rewriter, node).first;
    ASSERT_NE(node, res);
    d_options.preprocess.set(false);
    d_options.rewrite_level.set(0);
    sat::SatSolverFactory sat_factory(d_options);
    SolvingContext ctx(d_nm, d_options, sat_factory);
    ctx.assert_formula(d_nm.mk_node(Kind::DISTINCT, {node, res}));
    ASSERT_EQ(ctx.solve(), Result::UNSAT);
  }
};

TEST_F(TestRewriterBvNorm, norm_bv_add_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_ADD_MUL;
  //// applies
  // BV_NOT is the second operand of the bvmul (idx = 0 path).
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {invert_node(
           d_nm,
           d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, invert_node(d_nm, d_bv4_b)})),
       d_bv4_one}));
  // BV_NOT is the first operand of the bvmul (idx = 1 path).
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD,
      {invert_node(
           d_nm,
           d_nm.mk_node(Kind::BV_MUL, {invert_node(d_nm, d_bv4_b), d_bv4_a})),
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
  test_rule<kind>(invert_node(
      d_nm,
      d_nm.mk_node(
          Kind::BV_AND,
          {invert_node(d_nm, d_bv4_a),
           invert_node(d_nm,
                       d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a}))})));
  test_rule<kind>(invert_node(
      d_nm,
      d_nm.mk_node(
          Kind::BV_AND,
          {invert_node(d_nm, d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a})),
           invert_node(d_nm, d_bv4_a)})));
  //// does not apply
  test_rule_does_not_apply<kind>(
      invert_node(d_nm,
                  d_nm.mk_node(Kind::BV_AND,
                               {d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_a}),
                                invert_node(d_nm, d_bv4_a)})));
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
  //// does not apply (node[0] is not a bvneg)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b}));
}

TEST_F(TestRewriterBvNorm, norm_bv_concat_bv_not)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_CONCAT_BV_NOT;
  //// applies
  // (concat (bvnot a) (bvnot b)) ==> (bvnot (concat a b))
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_CONCAT,
                   {invert_node(d_nm, d_bv4_a), invert_node(d_nm, d_bv4_b)}));
  //// does not apply (second operand is not a bvnot)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_CONCAT, {invert_node(d_nm, d_bv4_a), d_bv4_b}));
}

TEST_F(TestRewriterBvNorm, norm_bv_add_concat)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_ADD_CONCAT;
  Type bv2_type                  = d_nm.mk_bv_type(2);
  Node bv2_zero                  = d_nm.mk_value(BitVector::mk_zero(2));
  Node x                         = d_nm.mk_const(bv2_type, "x_bv2");
  Node y                         = d_nm.mk_const(bv2_type, "y_bv2");
  //// applies
  // (concat 0 a) + (concat b 0) ==> (concat b a)
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD,
                               {d_nm.mk_node(Kind::BV_CONCAT, {bv2_zero, x}),
                                d_nm.mk_node(Kind::BV_CONCAT, {y, bv2_zero})}));
  // (concat a 0) + (concat 0 b) ==> (concat a b)
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD,
                               {d_nm.mk_node(Kind::BV_CONCAT, {x, bv2_zero}),
                                d_nm.mk_node(Kind::BV_CONCAT, {bv2_zero, y})}));
  // commutative order: (concat b 0) + (concat 0 a)
  test_rule<kind>(d_nm.mk_node(Kind::BV_ADD,
                               {d_nm.mk_node(Kind::BV_CONCAT, {y, bv2_zero}),
                                d_nm.mk_node(Kind::BV_CONCAT, {bv2_zero, x})}));
  //// does not apply (both zero halves are in the upper part)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_CONCAT, {bv2_zero, x}),
                    d_nm.mk_node(Kind::BV_CONCAT, {bv2_zero, y})}));
}

TEST_F(TestRewriterBvNorm, norm_fact_bv_add_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_FACT_BV_ADD_MUL;
  //// applies
  // (bvmul a b) + (bvmul a c): common factor at positions (0, 0)
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_c})}));
  // (bvmul a b) + (bvmul c a): common factor at positions (0, 1)
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_c, d_bv4_a})}));
  // (bvmul b a) + (bvmul a c): common factor at positions (1, 0)
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_c})}));
  // (bvmul b a) + (bvmul c a): common factor at positions (1, 1)
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_a}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_c, d_bv4_a})}));
  // (bvmul a b) + a ==> (bvmul a (bvadd 1 b))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}), d_bv4_a}));
  // commutative order: a + (bvmul a b)
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_bv4_a, d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b})}));
  //// does not apply (no common factor)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_MUL, {d_bv4_c, d_bv4_d})}));
}

TEST_F(TestRewriterBvNorm, norm_fact_bv_add_shl)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_FACT_BV_ADD_SHL;
  //// applies
  // (bvshl a b) + (bvshl a c) ==> (bvmul a (bvadd (bvshl 1 b) (bvshl 1 c)))
  test_rule<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_c})}));
  // (bvshl a b) + a ==> (bvmul a (bvadd (bvshl 1 b) 1))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b}), d_bv4_a}));
  // commutative order: a + (bvshl a b)
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_ADD, {d_bv4_a, d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b})}));
  //// does not apply (no shared base)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b}),
                    d_nm.mk_node(Kind::BV_SHL, {d_bv4_c, d_bv4_d})}));
}

TEST_F(TestRewriterBvNorm, norm_bv_extract_add_mul_rev1)
{
  constexpr RewriteRuleKind kind =
      RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV1;
  //// applies
  // (bvnot ((_ extract 2 0) a)) ==> ((_ extract 2 0) (bvnot a))
  test_rule<kind>(
      invert_node(d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {2, 0})));
  //// does not apply (lower index of extract is not 0)
  test_rule_does_not_apply<kind>(
      invert_node(d_nm, d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {3, 1})));
}

TEST_F(TestRewriterBvNorm, norm_bv_extract_add_mul_rev2)
{
  constexpr RewriteRuleKind kind =
      RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV2;
  // Note: This rule only fires at LEVEL_ARITHMETIC (see test_rule_arith); at
  // LEVEL_MAX the inverse rule BV_EXTRACT_ADD_MUL immediately undoes it.
  Type bv8  = d_nm.mk_bv_type(8);
  Node x8   = d_nm.mk_const(bv8);
  Node y8   = d_nm.mk_const(bv8);
  Node ex8x = d_nm.mk_node(Kind::BV_EXTRACT, {x8}, {3, 0});
  Node ex8y = d_nm.mk_node(Kind::BV_EXTRACT, {y8}, {3, 0});
  //// applies
  // extract + extract: (bvadd x[3:0] y[3:0]) -> (bvadd x y)[3:0]
  test_rule_arith<kind>(d_nm.mk_node(Kind::BV_ADD, {ex8x, ex8y}));
  // value + extract:   (bvadd v x[3:0])       -> (bvadd zext(v) x)[3:0]
  test_rule_arith<kind>(
      d_nm.mk_node(Kind::BV_ADD, {d_nm.mk_value(BitVector(4, "0011")), ex8y}));
  // extract + value:   (bvadd x[3:0] v)       -> (bvadd x zext(v))[3:0]
  test_rule_arith<kind>(
      d_nm.mk_node(Kind::BV_ADD, {ex8x, d_nm.mk_value(BitVector(4, "0011"))}));
  //// does not apply (lower index of extracts is not 0)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_ADD,
                   {d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {3, 1}),
                    d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_b}, {3, 1})}));
}

TEST_F(TestRewriterBvNorm, norm_bv_extract_add_mul_rev3)
{
  constexpr RewriteRuleKind kind =
      RewriteRuleKind::NORM_BV_EXTRACT_ADD_MUL_REV3;
  // Note: This rule only fires at LEVEL_ARITHMETIC (see test_rule_arith); at
  // LEVEL_MAX the inverse rule BV_EXTRACT_ADD_MUL immediately undoes it.
  Type bv8  = d_nm.mk_bv_type(8);
  Node x8   = d_nm.mk_const(bv8);
  Node y8   = d_nm.mk_const(bv8);
  Node ex8x = d_nm.mk_node(Kind::BV_EXTRACT, {x8}, {3, 0});
  Node ex8y = d_nm.mk_node(Kind::BV_EXTRACT, {y8}, {3, 0});
  //// applies
  // extract * extract: (bvmul x[3:0] y[3:0]) -> (bvmul x y)[3:0]
  test_rule_arith<kind>(d_nm.mk_node(Kind::BV_MUL, {ex8x, ex8y}));
  // value * extract:   (bvmul v x[3:0])       -> (bvmul zext(v) x)[3:0]
  test_rule_arith<kind>(
      d_nm.mk_node(Kind::BV_MUL, {d_nm.mk_value(BitVector(4, "0011")), ex8y}));
  // extract * value:   (bvmul x[3:0] v)       -> (bvmul x zext(v))[3:0]
  test_rule_arith<kind>(
      d_nm.mk_node(Kind::BV_MUL, {ex8x, d_nm.mk_value(BitVector(4, "0011"))}));
  //// does not apply (lower index of extracts is not 0)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_MUL,
                   {d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {3, 1}),
                    d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_b}, {3, 1})}));
}

TEST_F(TestRewriterBvNorm, norm_bv_mul_pow2_rev)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_BV_MUL_POW2_REV;
  // Note: This rule only fires at LEVEL_ARITHMETIC (see test_rule_arith); at
  // LEVEL_MAX the inverse rule BV_MUL_POW2 immediately undoes it.
  //// applies
  // (concat a[1:0] #b00) -> (bvmul #b0100 a)
  test_rule_arith<kind>(
      d_nm.mk_node(Kind::BV_CONCAT,
                   {d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {1, 0}),
                    d_nm.mk_value(BitVector(2, "00"))}));
  //// does not apply (lower part is not zero)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_CONCAT,
                   {d_nm.mk_node(Kind::BV_EXTRACT, {d_bv4_a}, {1, 0}),
                    d_nm.mk_value(BitVector(2, "01"))}));
}

TEST_F(TestRewriterBvNorm, norm_fact_bv_shl_mul)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_FACT_BV_SHL_MUL;
  //// applies
  // (bvshl (bvmul a b) c) with a < b ==> (bvmul a (bvshl b c))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_SHL, {d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}), d_bv4_c}));
  // (bvshl (bvmul b a) c): reversed factor order (b > a) ==> same result
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_SHL, {d_nm.mk_node(Kind::BV_MUL, {d_bv4_b, d_bv4_a}), d_bv4_c}));
  //// does not apply (node[0] is not a bvmul)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_b}));
}

TEST_F(TestRewriterBvNorm, norm_fact_bv_mul_shl)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::NORM_FACT_BV_MUL_SHL;
  //// applies
  // (bvmul (bvshl a c) b) with a < b ==> (bvmul a (bvshl b c))
  test_rule<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_SHL, {d_bv4_a, d_bv4_c}), d_bv4_b}));
  //// does not apply (no bvshl operand)
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::BV_MUL, {d_bv4_a, d_bv4_b}));
  //// does not apply (bvshl base is not < the other operand)
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::BV_MUL, {d_nm.mk_node(Kind::BV_SHL, {d_bv4_b, d_bv4_c}), d_bv4_a}));
}

}  // namespace bzla::test
