#include "bitvector.h"
#include "gtest/gtest.h"
#include "node/node_manager.h"
#include "printer/printer.h"
#include "rewrite/rewriter.h"
#include "solver/fp/floating_point.h"

namespace bzla::test {

using namespace bzla::node;

class TestRewriter : public ::testing::Test
{
  void SetUp() override
  {
    d_fp_type = d_nm.mk_fp_type(3, 5);
    d_rm_type = d_nm.mk_rm_type();
  }

 protected:
  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Type d_fp_type;
  Type d_rm_type;
};

/* fpabs -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_abs_eval)
{
  // applies
  Node fpabs0 = d_nm.mk_node(
      Kind::FP_ABS,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011"))),
            d_rewriter.rewrite(fpabs0));
  Node fpabs1 = d_nm.mk_node(Kind::FP_ABS, {fpabs0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011"))),
            d_rewriter.rewrite(fpabs1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011"))),
            Rewriter().rewrite(fpabs1));
  // does not apply
  Node fpabs2 = d_nm.mk_node(Kind::FP_ABS, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpabs2, d_rewriter.rewrite(fpabs2));
}

/* fpadd -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_add_eval)
{
  // applies
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000"))),
            d_rewriter.rewrite(fpadd0));
  Node fpadd1 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00000010"))),
       fpadd0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100001"))),
            d_rewriter.rewrite(fpadd1));
  Node fpadd1_1 =
      d_nm.mk_node(Kind::FP_ADD,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpadd1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false)),
            d_rewriter.rewrite(fpadd1_1));
  Node fpadd1_2 = d_nm.mk_node(
      Kind::FP_ADD, {d_nm.mk_value(RoundingMode::RTN), fpadd1, fpadd1});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110001"))),
            d_rewriter.rewrite(fpadd1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110001"))),
            Rewriter().rewrite(fpadd1_2));
  // does not apply
  Node fpadd2 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpadd2, d_rewriter.rewrite(fpadd2));
  Node fpadd3 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpadd3, d_rewriter.rewrite(fpadd3));
  Node fpadd4 =
      d_nm.mk_node(Kind::FP_ADD,
                   {d_nm.mk_value(RoundingMode::RNE),
                    d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
                    d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpadd4, d_rewriter.rewrite(fpadd4));
}

/* fpdiv -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_div_eval)
{
  // applies
  Node fpdiv0 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "01000101"))),
            d_rewriter.rewrite(fpdiv0));
  Node fpdiv1 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100010"))),
       fpdiv0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00001110"))),
            d_rewriter.rewrite(fpdiv1));
  Node fpdiv1_1 =
      d_nm.mk_node(Kind::FP_DIV,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpdiv1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
            d_rewriter.rewrite(fpdiv1_1));
  Node fpdiv1_2 = d_nm.mk_node(
      Kind::FP_DIV, {d_nm.mk_value(RoundingMode::RTN), fpdiv1, fpdiv1});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            d_rewriter.rewrite(fpdiv1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            Rewriter().rewrite(fpdiv1_2));
  // does not apply
  Node fpdiv2 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv2, d_rewriter.rewrite(fpdiv2));
  Node fpdiv3 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv3, d_rewriter.rewrite(fpdiv3));
  Node fpdiv4 =
      d_nm.mk_node(Kind::FP_DIV,
                   {d_nm.mk_value(RoundingMode::RNE),
                    d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false)),
                    d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpdiv4, d_rewriter.rewrite(fpdiv4));
}

/* fpisinf ------------------------------------------------------------------ */

TEST_F(TestRewriter, fp_is_inf_eval)
{
  // applies
  Node fpisinf0 = d_nm.mk_node(
      Kind::FP_IS_INF,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpisinf0));
  Node fpisinf1 = d_nm.mk_node(
      Kind::FP_IS_INF, {d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, true))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpisinf1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(true), Rewriter().rewrite(fpisinf1));
  // does not apply
  Node fpisinf2 = d_nm.mk_node(Kind::FP_IS_INF, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpisinf2, d_rewriter.rewrite(fpisinf2));
}

/* fpisnan ------------------------------------------------------------------ */

TEST_F(TestRewriter, fp_is_nan_eval)
{
  // applies
  Node fpisnan0 = d_nm.mk_node(
      Kind::FP_IS_NAN,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpisnan0));
  Node fpisnan1 = d_nm.mk_node(
      Kind::FP_IS_NAN, {d_nm.mk_value(FloatingPoint::fpnan(d_fp_type))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpisnan1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(true), Rewriter().rewrite(fpisnan1));
  // does not apply
  Node fpisnan2 = d_nm.mk_node(Kind::FP_IS_NAN, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpisnan2, d_rewriter.rewrite(fpisnan2));
}

/* fpisneg ------------------------------------------------------------------ */

TEST_F(TestRewriter, fp_is_neg_eval)
{
  // applies
  Node fpisneg0 = d_nm.mk_node(
      Kind::FP_IS_NEG,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpisneg0));
  Node fpisneg1 = d_nm.mk_node(
      Kind::FP_IS_NEG,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpisneg1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(true), Rewriter().rewrite(fpisneg1));
  // does not apply
  Node fpisneg2 = d_nm.mk_node(Kind::FP_IS_NEG, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpisneg2, d_rewriter.rewrite(fpisneg2));
}

/* fpisnorm ----------------------------------------------------------------- */

TEST_F(TestRewriter, fp_is_norm_eval)
{
  // applies
  Node fpisnorm0 = d_nm.mk_node(
      Kind::FP_IS_NORM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpisnorm0));
  Node fpisnorm1 = d_nm.mk_node(
      Kind::FP_IS_NORM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "11111011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpisnorm1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(fpisnorm1));
  // does not apply
  Node fpisnorm2 = d_nm.mk_node(Kind::FP_IS_NORM, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpisnorm2, d_rewriter.rewrite(fpisnorm2));
}

/* fpispos ------------------------------------------------------------------ */

TEST_F(TestRewriter, fp_is_pos_eval)
{
  // applies
  Node fpispos0 = d_nm.mk_node(
      Kind::FP_IS_POS,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpispos0));
  Node fpispos1 = d_nm.mk_node(
      Kind::FP_IS_POS,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpispos1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(fpispos1));
  // does not apply
  Node fpispos2 = d_nm.mk_node(Kind::FP_IS_POS, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpispos2, d_rewriter.rewrite(fpispos2));
}

/* fpissubnorm -------------------------------------------------------------- */

TEST_F(TestRewriter, fp_is_subnorm_eval)
{
  // applies
  Node fpissubnorm0 = d_nm.mk_node(
      Kind::FP_IS_SUBNORM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpissubnorm0));
  Node fpissubnorm0_1 = d_nm.mk_node(
      Kind::FP_IS_SUBNORM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "11111011")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpissubnorm0_1));
  Node fpissubnorm1 = d_nm.mk_node(
      Kind::FP_IS_SUBNORM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10001111")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpissubnorm1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(true), Rewriter().rewrite(fpissubnorm1));
  // does not apply
  Node fpissubnorm2 =
      d_nm.mk_node(Kind::FP_IS_SUBNORM, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpissubnorm2, d_rewriter.rewrite(fpissubnorm2));
}

/* fpissubnorm -------------------------------------------------------------- */

TEST_F(TestRewriter, fp_is_zero_eval)
{
  // applies
  Node fpiszero0 =
      d_nm.mk_node(Kind::FP_IS_ZERO,
                   {d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpiszero0));
  Node fpiszero0_1 =
      d_nm.mk_node(Kind::FP_IS_ZERO,
                   {d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, true))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpiszero0_1));
  Node fpiszero1 = d_nm.mk_node(
      Kind::FP_IS_ZERO,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10001111")))});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fpiszero1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(fpiszero1));
  // does not apply
  Node fpiszero2 = d_nm.mk_node(Kind::FP_IS_ZERO, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpiszero2, d_rewriter.rewrite(fpiszero2));
}

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
