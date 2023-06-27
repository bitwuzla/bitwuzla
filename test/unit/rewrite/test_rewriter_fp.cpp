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
#include "printer/printer.h"
#include "test/unit/rewrite/test_rewriter.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriterFp : public TestRewriter
{
};

/* fpabs -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_abs_eval)
{
  //// applies
  Node fpabs0 = d_nm.mk_node(
      Kind::FP_ABS,
      {d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "10011011")))});
  test_rewrite(
      fpabs0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00011011"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_ABS, {fpabs0}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00011011"))));
  //// does not apply
  Node fpabs2 = d_nm.mk_node(Kind::FP_ABS, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpabs2, d_rewriter.rewrite(fpabs2));
}

TEST_F(TestRewriterFp, fp_abs_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_ABS_ABS_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_ABS, {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_ABS, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_ABS, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_ABS, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fpadd -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_add_eval)
{
  //// applies
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  test_rewrite(
      fpadd0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000"))));
  Node fpadd1 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00000010"))),
       fpadd0});
  test_rewrite(
      fpadd1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100001"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_ADD,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpadd1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false))}),
      d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false)));
  test_rewrite(
      d_nm.mk_node(Kind::FP_ADD,
                   {d_nm.mk_value(RoundingMode::RTN), fpadd1, fpadd1}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110001"))));
  //// does not apply
  Node fpadd2 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_const(d_rm_type),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpadd2, d_rewriter.rewrite(fpadd2));
  Node fpadd3 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000"))),
       d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpadd3, d_rewriter.rewrite(fpadd3));
  Node fpadd4 = d_nm.mk_node(Kind::FP_ADD,
                             {d_nm.mk_value(RoundingMode::RNE),
                              d_fp35_pzero,
                              d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpadd4, d_rewriter.rewrite(fpadd4));
}

/* fpdiv -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_div_eval)
{
  //// applies
  Node fpdiv0 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  test_rewrite(
      fpdiv0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "01000101"))));
  Node fpdiv1 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       fpdiv0});
  test_rewrite(
      fpdiv1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00001110"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_DIV,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpdiv1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false))}),
      d_fp35_pzero);
  test_rewrite(
      d_nm.mk_node(Kind::FP_DIV,
                   {d_nm.mk_value(RoundingMode::RTN), fpdiv1, fpdiv1}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110000"))));
  //// does not apply
  Node fpdiv2 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_const(d_rm_type),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv2, d_rewriter.rewrite(fpdiv2));
  Node fpdiv3 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv3, d_rewriter.rewrite(fpdiv3));
  Node fpdiv4 = d_nm.mk_node(Kind::FP_DIV,
                             {d_nm.mk_value(RoundingMode::RNE),
                              d_fp35_pzero,
                              d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpdiv4, d_rewriter.rewrite(fpdiv4));
}

/* fpfma -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_fma_eval)
{
  //// applies
  Node fpfma0 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  test_rewrite(
      fpfma0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110010"))));
  Node fpfma1 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000"))),
       fpfma0});
  test_rewrite(
      fpfma1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110111"))));
  test_rewrite(
      d_nm.mk_node(
          Kind::FP_FMA,
          {d_nm.mk_value(RoundingMode::RNA),
           fpfma1,
           d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101"))),
           d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false))}),
      d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false)));
  test_rewrite(
      d_nm.mk_node(Kind::FP_FMA,
                   {d_nm.mk_value(RoundingMode::RTN), fpfma1, fpfma1, fpfma1}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "01001100"))));
  //// does not apply
  Node fpfma2 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_const(d_rm_type),
       d_fp35_pzero,
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpfma2, d_rewriter.rewrite(fpfma2));
  Node fpfma3 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpfma3, d_rewriter.rewrite(fpfma3));
  Node fpfma4 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpfma4, d_rewriter.rewrite(fpfma4));
  Node fpfma5 = d_nm.mk_node(
      Kind::FP_FMA,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010")))});
  ASSERT_EQ(fpfma5, d_rewriter.rewrite(fpfma5));
}

/* fpisinf ------------------------------------------------------------------ */

TEST_F(TestRewriterFp, fp_is_inf_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_INF,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10011011")))}),
               d_false);
  test_rewrite(
      d_nm.mk_node(Kind::FP_IS_INF,
                   {d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, true))}),
      d_true);
  // does not apply
  Node fpisinf2 = d_nm.mk_node(Kind::FP_IS_INF, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpisinf2, d_rewriter.rewrite(fpisinf2));
}

TEST_F(TestRewriterFp, fp_is_inf_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_IS_INF_ABS_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_INF, {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_INF, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_IS_INF, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_IS_INF, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fpisnan ------------------------------------------------------------------ */

TEST_F(TestRewriterFp, fp_is_nan_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NAN,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10011011")))}),
               d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NAN,
                            {d_nm.mk_value(FloatingPoint::fpnan(d_fp35_type))}),
               d_true);
  //// does not apply
  Node fpisnan2 = d_nm.mk_node(Kind::FP_IS_NAN, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpisnan2, d_rewriter.rewrite(fpisnan2));
}

TEST_F(TestRewriterFp, fp_is_nan_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_IS_NAN_ABS_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_NAN, {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_NAN, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_IS_NAN, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_IS_NAN, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fpisneg ------------------------------------------------------------------ */

TEST_F(TestRewriterFp, fp_is_neg_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NEG,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "00011011")))}),
               d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NEG,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10011011")))}),
               d_true);
  //// does not apply
  Node fpisneg2 = d_nm.mk_node(Kind::FP_IS_NEG, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpisneg2, d_rewriter.rewrite(fpisneg2));
}

/* fpisnorm ----------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_is_norm_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NORMAL,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "00011011")))}),
               d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_NORMAL,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "11111011")))}),
               d_false);
  //// does not apply
  Node fpisnorm2 =
      d_nm.mk_node(Kind::FP_IS_NORMAL, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpisnorm2, d_rewriter.rewrite(fpisnorm2));
}

TEST_F(TestRewriterFp, fp_is_norm_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_IS_NORM_ABS_NEG;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_IS_NORMAL,
                               {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_IS_NORMAL,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_IS_NORMAL, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_IS_NORMAL, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fpispos ------------------------------------------------------------------ */

TEST_F(TestRewriterFp, fp_is_pos_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_POS,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "00011011")))}),
               d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_POS,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10011011")))}),
               d_false);
  //// does not apply
  Node fpispos2 = d_nm.mk_node(Kind::FP_IS_POS, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpispos2, d_rewriter.rewrite(fpispos2));
}

/* fpissubnorm -------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_is_subnorm_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_SUBNORMAL,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "00011011")))}),
               d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_SUBNORMAL,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "11111011")))}),
               d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_SUBNORMAL,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10001111")))}),
               d_true);
  //// does not apply
  Node fpissubnorm2 =
      d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpissubnorm2, d_rewriter.rewrite(fpissubnorm2));
}

TEST_F(TestRewriterFp, fp_is_subnorm_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_IS_SUBNORM_ABS_NEG;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_IS_SUBNORMAL,
                               {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_IS_SUBNORMAL,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_IS_SUBNORMAL, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_IS_SUBNORMAL, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fpiszero ----------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_is_zero_eval)
{
  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp35_pzero}), d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp35_nzero}), d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_IS_ZERO,
                            {d_nm.mk_value(FloatingPoint(
                                d_fp35_type, BitVector(8, "10001111")))}),
               d_false);
  //// does not apply
  Node fpiszero2 = d_nm.mk_node(Kind::FP_IS_ZERO, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpiszero2, d_rewriter.rewrite(fpiszero2));
}

TEST_F(TestRewriterFp, fp_is_zero_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_IS_ZERO_ABS_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_ZERO, {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a})}));
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_IS_ZERO, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp35_a}));
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_IS_ZERO, {d_nm.mk_node(Kind::FP_SQRT, {d_rm, d_fp35_a})}));
}

/* fple --------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_leq_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});

  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_LEQ,
                            {d_fp35_pzero,
                             d_nm.mk_value(FloatingPoint(
                                 d_fp35_type, BitVector(8, "00100000")))}),
               d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_LEQ, {fpadd0, d_fp35_pzero}), d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_LEQ, {fpadd0, fpadd0}), d_true);
  //// does not apply
  Node fple2 = d_nm.mk_node(
      Kind::FP_LEQ,
      {d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fple2, d_rewriter.rewrite(fple2));
  Node fple3 =
      d_nm.mk_node(Kind::FP_LEQ, {d_fp35_pzero, d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fple3, d_rewriter.rewrite(fple3));
}

TEST_F(TestRewriterFp, fp_leq_eq)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_LEQ_EQ;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_LEQ, {d_fp35_a, d_fp35_a}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_LEQ,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_LEQ, {d_fp35_a, d_fp35_b}));
}

/* fplt --------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_lt_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});

  //// applies
  test_rewrite(d_nm.mk_node(Kind::FP_LT,
                            {d_fp35_pzero,
                             d_nm.mk_value(FloatingPoint(
                                 d_fp35_type, BitVector(8, "00100000")))}),
               d_true);
  test_rewrite(d_nm.mk_node(Kind::FP_LT, {fpadd0, d_fp35_pzero}), d_false);
  test_rewrite(d_nm.mk_node(Kind::FP_LT, {fpadd0, fpadd0}), d_false);
  //// does not apply
  Node fplt2 = d_nm.mk_node(
      Kind::FP_LT,
      {d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fplt2, d_rewriter.rewrite(fplt2));
  Node fplt3 =
      d_nm.mk_node(Kind::FP_LT, {d_fp35_pzero, d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fplt3, d_rewriter.rewrite(fplt3));
}

TEST_F(TestRewriterFp, fp_lt_eq)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_LT_EQ;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_LT, {d_fp35_a, d_fp35_a}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_LT,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_LT, {d_fp35_a, d_fp35_b}));
}

/* fpmin -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_min_eq)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_MIN_EQ;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_MIN, {d_fp35_a, d_fp35_a}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_MIN,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_MIN, {d_fp35_a, d_fp35_b}));
}

/* fpmax -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_max_eq)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_MAX_EQ;
  //// applies
  test_rule<kind>(d_nm.mk_node(Kind::FP_MAX, {d_fp35_a, d_fp35_a}));
  test_rule<kind>(d_nm.mk_node(Kind::FP_MAX,
                               {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}),
                                d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_MAX, {d_fp35_a, d_fp35_b}));
}

/* fpmul -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_mul_eval)
{
  //// applies
  Node fpmul0 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  test_rewrite(
      fpmul0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100101"))));
  Node fpmul1 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       fpmul0});
  test_rewrite(
      fpmul1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00011000"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_MUL,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpmul1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false))}),
      d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false)));
  test_rewrite(
      d_nm.mk_node(Kind::FP_MUL,
                   {d_nm.mk_value(RoundingMode::RTN), fpmul1, fpmul1}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00001001"))));
  //// does not apply
  Node fpmul2 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_const(d_rm_type),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpmul2, d_rewriter.rewrite(fpmul2));
  Node fpmul3 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000"))),
       d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpmul3, d_rewriter.rewrite(fpmul3));
  Node fpmul4 = d_nm.mk_node(Kind::FP_MUL,
                             {d_nm.mk_value(RoundingMode::RNE),
                              d_fp35_pzero,
                              d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpmul4, d_rewriter.rewrite(fpmul4));
}

/* fpneg -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_neg_eval)
{
  //// applies
  Node fpneg0 = d_nm.mk_node(
      Kind::FP_NEG,
      {d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "10011011")))});
  test_rewrite(
      fpneg0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00011011"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_NEG, {fpneg0}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "10011011"))));
  //// does not apply
  Node fpneg2 = d_nm.mk_node(Kind::FP_NEG, {d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fpneg2, d_rewriter.rewrite(fpneg2));
}

TEST_F(TestRewriterFp, fp_neg_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_NEG_NEG;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_NEG, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}));
}

/* fprem -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_rem_eval)
{
  //// applies
  Node fprem0 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  test_rewrite(
      fprem0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "10001100"))));
  Node fprem1 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100010"))),
       fprem0});
  test_rewrite(fprem1, d_fp35_pzero);
  test_rewrite(
      d_nm.mk_node(
          Kind::FP_REM,
          {fprem1, d_nm.mk_value(FloatingPoint::fpinf(d_fp35_type, false))}),
      d_fp35_pzero);
  test_rewrite(d_nm.mk_node(Kind::FP_REM, {fprem1, fprem0}), d_fp35_pzero);
  //// does not apply
  Node fprem2 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_const(d_fp35_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fprem2, d_rewriter.rewrite(fprem2));
  Node fprem3 =
      d_nm.mk_node(Kind::FP_REM, {d_fp35_pzero, d_nm.mk_const(d_fp35_type)});
  ASSERT_EQ(fprem3, d_rewriter.rewrite(fprem3));
}

TEST_F(TestRewriterFp, fp_rem_same_div)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_REM_SAME_DIV;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_node(Kind::FP_REM, {d_fp35_a, d_fp35_b}), d_fp35_b}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_node(Kind::FP_REM, {d_fp35_b, d_fp35_a}), d_fp35_b}));
}

TEST_F(TestRewriterFp, fp_rem_abs_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_REM_ABS_NEG;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::FP_REM, {d_fp35_a, d_nm.mk_node(Kind::FP_ABS, {d_fp35_b})}));
  test_rule<kind>(d_nm.mk_node(
      Kind::FP_REM, {d_fp35_a, d_nm.mk_node(Kind::FP_NEG, {d_fp35_b})}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_REM, {d_fp35_a, d_nm.mk_node(Kind::FP_RTI, {d_rm, d_fp35_b})}));
}

TEST_F(TestRewriterFp, fp_rem_neg)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_REM_NEG;
  //// applies
  test_rule<kind>(d_nm.mk_node(
      Kind::FP_REM, {d_nm.mk_node(Kind::FP_NEG, {d_fp35_a}), d_fp35_a}));
  //// does not apply
  test_rule_does_not_apply<kind>(d_nm.mk_node(
      Kind::FP_REM, {d_nm.mk_node(Kind::FP_ABS, {d_fp35_a}), d_fp35_a}));
}

/* fprti -------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_rti_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  //// applies
  Node fprti0 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101")))});
  test_rewrite(
      fprti0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110000"))));
  Node fprti1 =
      d_nm.mk_node(Kind::FP_RTI, {d_nm.mk_value(RoundingMode::RNA), fprti0});
  test_rewrite(
      fprti1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110000"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_RTI, {d_nm.mk_value(RoundingMode::RNA), fpadd0}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110000"))));
  //// does not apply
  Node fprti2 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fprti2, d_rewriter.rewrite(fprti2));
  Node fprti3 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp35_type)});
}

/* fpsqrt ------------------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_sqrt_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  //// applies
  Node fpsqrt0 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110101")))});
  test_rewrite(
      fpsqrt0,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110010"))));
  Node fpsqrt1 =
      d_nm.mk_node(Kind::FP_SQRT, {d_nm.mk_value(RoundingMode::RNA), fpsqrt0});
  test_rewrite(
      fpsqrt1,
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00110001"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_SQRT, {d_nm.mk_value(RoundingMode::RNA), fpadd0}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100111"))));
  //// does not apply
  Node fpsqrt2 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpsqrt2, d_rewriter.rewrite(fpsqrt2));
  Node fpsqrt3 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp35_type)});
}

/* to_fp: from_bv ----------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_to_fp_from_bv_eval)
{
  // evaluates to #b00010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "00001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  //// applies
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_BV,
                   {d_nm.mk_value(BitVector(8, "10101100"))},
                   {3, 5}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "10101100"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_BV, {bvadd0}, {3, 5}),
      d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00010111"))));
  //// does not apply
  Node tofpfrombv2 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_BV, {d_nm.mk_const(d_nm.mk_bv_type(8))}, {3, 5});
  ASSERT_EQ(tofpfrombv2, d_rewriter.rewrite(tofpfrombv2));
}

/* to_fp: from_fp ----------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_to_fp_from_fp_eval)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp35_pzero,
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00100000")))});
  //// applies
  test_rewrite(
      d_nm.mk_node(
          Kind::FP_TO_FP_FROM_FP,
          {d_nm.mk_value(RoundingMode::RNA),
           d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00101100")))},
          {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0011101100000000"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_FP,
                   {d_nm.mk_value(RoundingMode::RTP), fpadd0},
                   {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0011100000000000"))));
  // does not apply
  Node tofpfromfp3 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_FP,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp35_type, BitVector(8, "00010000")))},
      {3, 5});
  ASSERT_EQ(tofpfromfp3, d_rewriter.rewrite(tofpfromfp3));
  Node tofpfromfp4 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_FP,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp35_type)},
      {3, 5});
  ASSERT_EQ(tofpfromfp4, d_rewriter.rewrite(tofpfromfp4));
}

/* to_fp: from_sbv ---------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_to_fp_from_sbv_eval)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to #b10010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "10001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  //// applies
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV,
                   {d_nm.mk_value(RoundingMode::RNA),
                    d_nm.mk_value(BitVector(8, "00101100"))},
                   {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101000110000000"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV,
                   {d_nm.mk_value(RoundingMode::RTP), bvadd0},
                   {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "1101011010010000"))));
  // does not apply
  Node tofpfromsbv3 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_SBV,
      {d_nm.mk_const(d_rm_type), d_nm.mk_value(BitVector(8, "00010000"))},
      {3, 5});
  ASSERT_EQ(tofpfromsbv3, d_rewriter.rewrite(tofpfromsbv3));
  Node tofpfromsbv4 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_SBV,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_nm.mk_bv_type(8))},
      {3, 5});
  ASSERT_EQ(tofpfromsbv4, d_rewriter.rewrite(tofpfromsbv4));
}

TEST_F(TestRewriterFp, fp_to_fp_from_sbv_bv1_elim)
{
  constexpr RewriteRuleKind kind = RewriteRuleKind::FP_TO_FP_FROM_SBV_BV1_ELIM;
  //// applies
  test_rule<kind>(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV, {d_rm, d_bv1_a}, {5, 11}));
  //// does not apply
  test_rule_does_not_apply<kind>(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV, {d_rm, d_bv4_a}, {5, 11}));
}

/* to_fp: from_ubv ---------------------------------------------------------- */

TEST_F(TestRewriterFp, fp_to_fp_from_ubv_eval)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to #b10010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "10001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  //// applies
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_UBV,
                   {d_nm.mk_value(RoundingMode::RNA),
                    d_nm.mk_value(BitVector(8, "00101100"))},
                   {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101000110000000"))));
  test_rewrite(
      d_nm.mk_node(Kind::FP_TO_FP_FROM_UBV,
                   {d_nm.mk_value(RoundingMode::RTP), bvadd0},
                   {5, 11}),
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101100010111000"))));
  // does not apply
  Node tofpfromubv3 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_UBV,
      {d_nm.mk_const(d_rm_type), d_nm.mk_value(BitVector(8, "00010000"))},
      {3, 5});
  ASSERT_EQ(tofpfromubv3, d_rewriter.rewrite(tofpfromubv3));
  Node tofpfromubv4 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_UBV,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_nm.mk_bv_type(8))},
      {3, 5});
  ASSERT_EQ(tofpfromubv4, d_rewriter.rewrite(tofpfromubv4));
}

/* --- Elimination Rules ---------------------------------------------------- */

TEST_F(TestRewriterFp, fp_equal_elim)
{
  test_elim_rule(Kind::FP_EQUAL, d_fp35_type);
}

TEST_F(TestRewriterFp, fp_fp_elim) { test_elim_rule(Kind::FP_FP, d_fp35_type); }

TEST_F(TestRewriterFp, fp_ge_elim)
{
  test_elim_rule(Kind::FP_GEQ, d_fp35_type);
}

TEST_F(TestRewriterFp, fp_gt_elim) { test_elim_rule(Kind::FP_GT, d_fp35_type); }

TEST_F(TestRewriterFp, fp_sub_elim)
{
  test_elim_rule(Kind::FP_SUB, d_fp35_type);
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
