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
    d_fp_type  = d_nm.mk_fp_type(3, 5);
    d_rm_type  = d_nm.mk_rm_type();
    d_fp_pzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, false));
    d_fp_nzero = d_nm.mk_value(FloatingPoint::fpzero(d_fp_type, true));
  }

 protected:
  Rewriter d_rewriter;
  NodeManager& d_nm = NodeManager::get();
  Type d_fp_type;
  Type d_rm_type;
  Node d_fp_pzero;
  Node d_fp_nzero;
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
       d_fp_pzero,
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
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpadd2, d_rewriter.rewrite(fpadd2));
  Node fpadd3 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpadd3, d_rewriter.rewrite(fpadd3));
  Node fpadd4 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE), d_fp_pzero, d_nm.mk_const(d_fp_type)});
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
  ASSERT_EQ(d_fp_pzero, d_rewriter.rewrite(fpdiv1_1));
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
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv2, d_rewriter.rewrite(fpdiv2));
  Node fpdiv3 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpdiv3, d_rewriter.rewrite(fpdiv3));
  Node fpdiv4 = d_nm.mk_node(
      Kind::FP_DIV,
      {d_nm.mk_value(RoundingMode::RNE), d_fp_pzero, d_nm.mk_const(d_fp_type)});
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

/* fpiszero ----------------------------------------------------------------- */

TEST_F(TestRewriter, fp_is_zero_eval)
{
  // applies
  Node fpiszero0 = d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp_pzero});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fpiszero0));
  Node fpiszero0_1 = d_nm.mk_node(Kind::FP_IS_ZERO, {d_fp_nzero});
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

/* fple --------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_le_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});

  // applies
  Node fple0 = d_nm.mk_node(
      Kind::FP_LE,
      {d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fple0));
  Node fple1 = d_nm.mk_node(Kind::FP_LE, {fpadd0, d_fp_pzero});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fple1));
  Node fple1_1 = d_nm.mk_node(Kind::FP_LE, {fpadd0, fpadd0});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fple1_1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(true), Rewriter().rewrite(fple1_1));
  // does not apply
  Node fple2 = d_nm.mk_node(
      Kind::FP_LE,
      {d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fple2, d_rewriter.rewrite(fple2));
  Node fple3 =
      d_nm.mk_node(Kind::FP_LE, {d_fp_pzero, d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fple3, d_rewriter.rewrite(fple3));
}

/* fplt --------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_lt_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});

  // applies
  Node fplt0 = d_nm.mk_node(
      Kind::FP_LT,
      {d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(true), d_rewriter.rewrite(fplt0));
  Node fplt1 = d_nm.mk_node(Kind::FP_LT, {fpadd0, d_fp_pzero});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fplt1));
  Node fplt1_1 = d_nm.mk_node(Kind::FP_LT, {fpadd0, fpadd0});
  ASSERT_EQ(d_nm.mk_value(false), d_rewriter.rewrite(fplt1_1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(false), Rewriter().rewrite(fplt1_1));
  // does not apply
  Node fplt2 = d_nm.mk_node(
      Kind::FP_LT,
      {d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fplt2, d_rewriter.rewrite(fplt2));
  Node fplt3 =
      d_nm.mk_node(Kind::FP_LT, {d_fp_pzero, d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fplt3, d_rewriter.rewrite(fplt3));
}

/* fpmul -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_mul_eval)
{
  // applies
  Node fpmul0 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100101"))),
            d_rewriter.rewrite(fpmul0));
  Node fpmul1 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100010"))),
       fpmul0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011000"))),
            d_rewriter.rewrite(fpmul1));
  Node fpmul1_1 =
      d_nm.mk_node(Kind::FP_MUL,
                   {d_nm.mk_value(RoundingMode::RNA),
                    fpmul1,
                    d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false)),
            d_rewriter.rewrite(fpmul1_1));
  Node fpmul1_2 = d_nm.mk_node(
      Kind::FP_MUL, {d_nm.mk_value(RoundingMode::RTN), fpmul1, fpmul1});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00001001"))),
            d_rewriter.rewrite(fpmul1_2));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00001001"))),
            Rewriter().rewrite(fpmul1_2));
  // does not apply
  Node fpmul2 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_const(d_rm_type),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpmul2, d_rewriter.rewrite(fpmul2));
  Node fpmul3 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpmul3, d_rewriter.rewrite(fpmul3));
  Node fpmul4 = d_nm.mk_node(
      Kind::FP_MUL,
      {d_nm.mk_value(RoundingMode::RNE), d_fp_pzero, d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpmul4, d_rewriter.rewrite(fpmul4));
}

/* fpneg -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_neg_eval)
{
  // applies
  Node fpneg0 = d_nm.mk_node(
      Kind::FP_NEG,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00011011"))),
            d_rewriter.rewrite(fpneg0));
  Node fpneg1 = d_nm.mk_node(Kind::FP_NEG, {fpneg0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011"))),
            d_rewriter.rewrite(fpneg1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10011011"))),
            Rewriter().rewrite(fpneg1));
  // does not apply
  Node fpneg2 = d_nm.mk_node(Kind::FP_NEG, {d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fpneg2, d_rewriter.rewrite(fpneg2));
}

/* fprem -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_rem_eval)
{
  // applies
  Node fprem0 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110101"))),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10001100"))),
            d_rewriter.rewrite(fprem0));
  Node fprem1 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100010"))),
       fprem0});
  ASSERT_EQ(d_fp_pzero, d_rewriter.rewrite(fprem1));
  Node fprem1_1 = d_nm.mk_node(
      Kind::FP_REM,
      {fprem1, d_nm.mk_value(FloatingPoint::fpinf(d_fp_type, false))});
  ASSERT_EQ(d_fp_pzero, d_rewriter.rewrite(fprem1_1));
  Node fprem1_2 = d_nm.mk_node(Kind::FP_REM, {fprem1, fprem0});
  ASSERT_EQ(d_fp_pzero, d_rewriter.rewrite(fprem1_2));
  // with empty cache
  ASSERT_EQ(d_fp_pzero, Rewriter().rewrite(fprem1_2));
  // does not apply
  Node fprem2 = d_nm.mk_node(
      Kind::FP_REM,
      {d_nm.mk_const(d_fp_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fprem2, d_rewriter.rewrite(fprem2));
  Node fprem3 =
      d_nm.mk_node(Kind::FP_REM, {d_fp_pzero, d_nm.mk_const(d_fp_type)});
  ASSERT_EQ(fprem3, d_rewriter.rewrite(fprem3));
}

/* fprti -------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_rti_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  // applies
  Node fprti0 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110101")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            d_rewriter.rewrite(fprti0));
  Node fprti1 =
      d_nm.mk_node(Kind::FP_RTI, {d_nm.mk_value(RoundingMode::RNA), fprti0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            d_rewriter.rewrite(fprti1));
  Node fprti1_1 =
      d_nm.mk_node(Kind::FP_RTI, {d_nm.mk_value(RoundingMode::RNA), fpadd0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            d_rewriter.rewrite(fprti1_1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110000"))),
            Rewriter().rewrite(fprti1_1));
  // does not apply
  Node fprti2 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fprti2, d_rewriter.rewrite(fprti2));
  Node fprti3 = d_nm.mk_node(
      Kind::FP_RTI,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp_type)});
}

/* fpsqrt ------------------------------------------------------------------- */

TEST_F(TestRewriter, fp_sqrt_eval)
{
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  // applies
  Node fpsqrt0 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_value(RoundingMode::RNE),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110101")))});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110010"))),
            d_rewriter.rewrite(fpsqrt0));
  Node fpsqrt1 =
      d_nm.mk_node(Kind::FP_SQRT, {d_nm.mk_value(RoundingMode::RNA), fpsqrt0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00110001"))),
            d_rewriter.rewrite(fpsqrt1));
  Node fpsqrt1_1 =
      d_nm.mk_node(Kind::FP_SQRT, {d_nm.mk_value(RoundingMode::RNA), fpadd0});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100111"))),
            d_rewriter.rewrite(fpsqrt1_1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100111"))),
            Rewriter().rewrite(fpsqrt1_1));
  // does not apply
  Node fpsqrt2 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  ASSERT_EQ(fpsqrt2, d_rewriter.rewrite(fpsqrt2));
  Node fpsqrt3 = d_nm.mk_node(
      Kind::FP_SQRT,
      {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp_type)});
}

/* to_fp: from_bv ----------------------------------------------------------- */

TEST_F(TestRewriter, fp_to_fp_from_bv)
{
  // evaluates to #b00010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "00001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  // applies
  Node tofpfrombv0 = d_nm.mk_node(Kind::FP_TO_FP_FROM_BV,
                                  {d_nm.mk_value(BitVector(8, "10101100"))},
                                  {3, 5});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "10101100"))),
            d_rewriter.rewrite(tofpfrombv0));
  Node tofpfrombv1 = d_nm.mk_node(Kind::FP_TO_FP_FROM_BV, {bvadd0}, {3, 5});
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00010111"))),
            d_rewriter.rewrite(tofpfrombv1));
  // with empty cache
  ASSERT_EQ(d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00010111"))),
            Rewriter().rewrite(tofpfrombv1));
  // does not apply
  Node tofpfrombv2 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_BV, {d_nm.mk_const(d_nm.mk_bv_type(8))}, {3, 5});
  ASSERT_EQ(tofpfrombv2, d_rewriter.rewrite(tofpfrombv2));
}

/* to_fp: from_fp ----------------------------------------------------------- */

TEST_F(TestRewriter, fp_to_fp_from_fp)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to (fp #b0 #b010 #b0000")
  Node fpadd0 = d_nm.mk_node(
      Kind::FP_ADD,
      {d_nm.mk_value(RoundingMode::RNE),
       d_fp_pzero,
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00100000")))});
  // applies
  Node tofpfromfp0 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_FP,
      {d_nm.mk_value(RoundingMode::RNA),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00101100")))},
      {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0011101100000000"))),
      d_rewriter.rewrite(tofpfromfp0));
  Node tofpfromfp1 = d_nm.mk_node(Kind::FP_TO_FP_FROM_FP,
                                  {d_nm.mk_value(RoundingMode::RTP), fpadd0},
                                  {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0011100000000000"))),
      d_rewriter.rewrite(tofpfromfp1));
  // with empty cache
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0011100000000000"))),
      Rewriter().rewrite(tofpfromfp1));
  // does not apply
  Node tofpfromfp3 = d_nm.mk_node(
      Kind::FP_TO_FP_FROM_FP,
      {d_nm.mk_const(d_rm_type),
       d_nm.mk_value(FloatingPoint(d_fp_type, BitVector(8, "00010000")))},
      {3, 5});
  ASSERT_EQ(tofpfromfp3, d_rewriter.rewrite(tofpfromfp3));
  Node tofpfromfp4 =
      d_nm.mk_node(Kind::FP_TO_FP_FROM_FP,
                   {d_nm.mk_value(RoundingMode::RNE), d_nm.mk_const(d_fp_type)},
                   {3, 5});
  ASSERT_EQ(tofpfromfp4, d_rewriter.rewrite(tofpfromfp4));
}

/* to_fp: from_sbv ---------------------------------------------------------- */

TEST_F(TestRewriter, fp_to_fp_from_sbv)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to #b10010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "10001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  // applies
  Node tofpfromsbv0 = d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV,
                                   {d_nm.mk_value(RoundingMode::RNA),
                                    d_nm.mk_value(BitVector(8, "00101100"))},
                                   {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101000110000000"))),
      d_rewriter.rewrite(tofpfromsbv0));
  Node tofpfromsbv1 = d_nm.mk_node(Kind::FP_TO_FP_FROM_SBV,
                                   {d_nm.mk_value(RoundingMode::RTP), bvadd0},
                                   {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "1101011010010000"))),
      d_rewriter.rewrite(tofpfromsbv1));
  // with empty cache
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "1101011010010000"))),
      Rewriter().rewrite(tofpfromsbv1));
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

/* to_fp: from_ubv ---------------------------------------------------------- */

TEST_F(TestRewriter, fp_to_fp_from_ubv)
{
  Type float16 = d_nm.mk_fp_type(5, 11);
  // evaluates to #b10010111
  Node bvadd0 = d_nm.mk_node(Kind::BV_ADD,
                             {d_nm.mk_value(BitVector(8, "10001001")),
                              d_nm.mk_value(BitVector(8, "00001110"))});
  // applies
  Node tofpfromubv0 = d_nm.mk_node(Kind::FP_TO_FP_FROM_UBV,
                                   {d_nm.mk_value(RoundingMode::RNA),
                                    d_nm.mk_value(BitVector(8, "00101100"))},
                                   {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101000110000000"))),
      d_rewriter.rewrite(tofpfromubv0));
  Node tofpfromubv1 = d_nm.mk_node(Kind::FP_TO_FP_FROM_UBV,
                                   {d_nm.mk_value(RoundingMode::RTP), bvadd0},
                                   {5, 11});
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101100010111000"))),
      d_rewriter.rewrite(tofpfromubv1));
  // with empty cache
  ASSERT_EQ(
      d_nm.mk_value(FloatingPoint(float16, BitVector(16, "0101100010111000"))),
      Rewriter().rewrite(tofpfromubv1));
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

/* -------------------------------------------------------------------------- */
}  // namespace bzla::test
