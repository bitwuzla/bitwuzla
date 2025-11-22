/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2019 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "test/unit/fp/test_fp.h"

namespace bzla::test {

/* -------------------------------------------------------------------------- */

#define TEST_INEQ(FUN)                                                  \
  do                                                                    \
  {                                                                     \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) { \
      BitVector bv1;                                                    \
      if (d_rng->flip_coin())                                           \
      {                                                                 \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);   \
      }                                                                 \
      else                                                              \
      {                                                                 \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);    \
      }                                                                 \
      BitVector bv2 = BitVector(16, *d_rng);                            \
      FloatingPoint fp1(d_fp16.first, d_fp16.second, bv1);              \
      FloatingPoint fp2(d_fp16.first, d_fp16.second, bv2);              \
      FloatingPointSymFPU fp_symfpu1(d_typefp16, bv1);                  \
      FloatingPointSymFPU fp_symfpu2(d_typefp16, bv2);                  \
      ASSERT_EQ(fp1.fp##FUN(fp1), fp_symfpu1.fp##FUN(fp_symfpu1));      \
      ASSERT_EQ(fp1.fp##FUN(fp2), fp_symfpu1.fp##FUN(fp_symfpu2));      \
      ASSERT_EQ(fp1.fp##FUN(fp2), fp_symfpu1.fp##FUN(fp_symfpu2));      \
    };                                                                  \
    test_for_float16(fun);                                              \
                                                                        \
    for (const auto& f : d_formats_32_128)                              \
    {                                                                   \
      uint64_t bv_size = f.first + f.second;                            \
      for (uint32_t i = 0; i < N_TESTS; ++i)                            \
      {                                                                 \
        BitVector bv1 = BitVector(bv_size, *d_rng);                     \
        BitVector bv2 = BitVector(bv_size, *d_rng);                     \
        Type type     = d_nm.mk_fp_type(f.first, f.second);             \
        FloatingPoint fp1(f.first, f.second, bv1);                      \
        FloatingPoint fp2(f.first, f.second, bv2);                      \
        FloatingPointSymFPU fp_symfpu1(type, bv1);                      \
        FloatingPointSymFPU fp_symfpu2(type, bv2);                      \
        ASSERT_EQ(fp1.fp##FUN(fp2), fp_symfpu1.fp##FUN(fp_symfpu2));    \
      }                                                                 \
    }                                                                   \
  } while (0)

/* -------------------------------------------------------------------------- */

class TestFpEqIneq : public TestFp
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestFpEqIneq, eq)
{
  //// format different
  ASSERT_FALSE(FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false)
               == FloatingPoint::fpzero(6, 8, false));
  ASSERT_TRUE(FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false)
              != FloatingPoint::fpzero(6, 8, false));
  ASSERT_FALSE(FloatingPointSymFPU::fpzero(d_typefp16, false)
               == FloatingPointSymFPU::fpzero(d_nm.mk_fp_type(6, 8), false));
  ASSERT_TRUE(FloatingPointSymFPU::fpzero(d_typefp16, false)
              != FloatingPointSymFPU::fpzero(d_nm.mk_fp_type(6, 8), false));

  //// same format
  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "0.1"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "0.1"));
  ASSERT_EQ(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "0.1"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "0.1"));

  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-0.1"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "0.1"));
  ASSERT_NE(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-0.1"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "0.1"));

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777"));
  ASSERT_EQ(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-5.17777"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-5.17777"));

  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RTZ, "-5.17777"));
  ASSERT_NE(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-5.17777"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RTZ, "-5.17777"));

  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-8.8"));
  ASSERT_NE(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-5.17777"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-8.8"));

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "3.27"),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "3.27"));
  ASSERT_EQ(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "3.27"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "3.27"));

  ASSERT_NE(
      FloatingPoint::from_real(
          d_fp16.first, d_fp16.second, RoundingMode::RNE, "-12.11328125"),
      FloatingPoint::from_real(
          d_fp16.first, d_fp16.second, RoundingMode::RNA, "-12.11328125"));
  ASSERT_NE(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-12.11328125"),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNA, "-12.11328125"));

  ASSERT_EQ(FloatingPoint::fpnan(d_fp16.first, d_fp16.second),
            FloatingPoint::fpnan(d_fp16.first, d_fp16.second));
  ASSERT_EQ(FloatingPointSymFPU::fpnan(d_typefp16),
            FloatingPointSymFPU::fpnan(d_typefp16));

  ASSERT_EQ(FloatingPoint::fpinf(d_fp16.first, d_fp16.second, true),
            FloatingPoint::fpinf(d_fp16.first, d_fp16.second, true));
  ASSERT_EQ(FloatingPointSymFPU::fpinf(d_typefp16, true),
            FloatingPointSymFPU::fpinf(d_typefp16, true));

  ASSERT_EQ(FloatingPoint::fpinf(d_fp16.first, d_fp16.second, false),
            FloatingPoint::fpinf(d_fp16.first, d_fp16.second, false));
  ASSERT_EQ(FloatingPointSymFPU::fpinf(d_typefp16, false),
            FloatingPointSymFPU::fpinf(d_typefp16, false));

  ASSERT_NE(FloatingPoint::fpinf(d_fp16.first, d_fp16.second, true),
            FloatingPoint::fpinf(d_fp16.first, d_fp16.second, false));
  ASSERT_NE(FloatingPointSymFPU::fpinf(d_typefp16, true),
            FloatingPointSymFPU::fpinf(d_typefp16, false));

  ASSERT_EQ(FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false),
            FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false));
  ASSERT_EQ(FloatingPointSymFPU::fpzero(d_typefp16, false),
            FloatingPointSymFPU::fpzero(d_typefp16, false));

  ASSERT_NE(FloatingPoint::fpzero(d_fp16.first, d_fp16.second, true),
            FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false));
  ASSERT_NE(FloatingPointSymFPU::fpzero(d_typefp16, true),
            FloatingPointSymFPU::fpzero(d_typefp16, false));

  ASSERT_NE(FloatingPoint::fpzero(d_fp16.first, d_fp16.second, true),
            FloatingPoint::fpinf(d_fp16.first, d_fp16.second, true));
  ASSERT_NE(FloatingPointSymFPU::fpzero(d_typefp16, true),
            FloatingPointSymFPU::fpinf(d_typefp16, true));

  ASSERT_NE(FloatingPoint::fpnan(d_fp16.first, d_fp16.second),
            FloatingPoint::fpinf(d_fp16.first, d_fp16.second, false));
  ASSERT_NE(FloatingPointSymFPU::fpnan(d_typefp16),
            FloatingPointSymFPU::fpinf(d_typefp16, false));

  for (const auto& f : d_all_formats)
  {
    uint64_t bv_size = f.first + f.second;
    Type type        = d_nm.mk_fp_type(f.first, f.second);
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      bool isnan1   = bv_is_fpnan(f.first, f.second, bv1);
      bool isnan2   = bv_is_fpnan(f.first, f.second, bv2);
      {
        FloatingPoint fp1(f.first, f.second, bv1);
        FloatingPoint fp2(f.first, f.second, bv2);
        if (bv1 == bv2)
        {
          ASSERT_TRUE(fp1 == fp2);
          ASSERT_FALSE(fp1 != fp2);
        }
        else
        {
          ASSERT_TRUE(!isnan1 || !isnan2 || fp1 == fp2);
          ASSERT_TRUE((isnan1 && isnan2) || fp1 != fp2);
        }
      }

      {
        FloatingPointSymFPU fp1(type, bv1);
        FloatingPointSymFPU fp2(type, bv2);
        if (bv1 == bv2)
        {
          ASSERT_TRUE(fp1 == fp2);
          ASSERT_FALSE(fp1 != fp2);
        }
        else
        {
          ASSERT_TRUE(!isnan1 || !isnan2 || fp1 == fp2);
          ASSERT_TRUE((isnan1 && isnan2) || fp1 != fp2);
        }
      }
    }
  }
}

TEST_F(TestFpEqIneq, lt) { TEST_INEQ(lt); }
TEST_F(TestFpEqIneq, leq) { TEST_INEQ(le); }
TEST_F(TestFpEqIneq, gt) { TEST_INEQ(gt); }
TEST_F(TestFpEqIneq, geq) { TEST_INEQ(ge); }

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
