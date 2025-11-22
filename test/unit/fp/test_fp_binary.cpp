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

#define TEST_BINARY(FUN)                                                \
  do                                                                    \
  {                                                                     \
    /* more comprehensive tests for all values in Float16 */            \
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
      std::string fp_str        = fp1.fp##FUN(fp2).str();               \
      std::string fp_symfpu_str = fp_symfpu1.fp##FUN(fp_symfpu2).str(); \
      ASSERT_EQ(fp_str, fp_symfpu_str);                                 \
    };                                                                  \
    test_for_float16(fun);                                              \
                                                                        \
    /* random tests for Float32, Float64, Float128 */                   \
    for (const auto& f : d_formats_32_128)                              \
    {                                                                   \
      uint64_t bv_size = f.first + f.second;                            \
      for (uint32_t i = 0; i < N_TESTS; ++i)                            \
      {                                                                 \
        BitVector bv1 = BitVector(bv_size, *d_rng);                     \
        BitVector bv2 = BitVector(bv_size, *d_rng);                     \
        FloatingPoint fp1(f.first, f.second, bv1);                      \
        FloatingPoint fp2(f.first, f.second, bv2);                      \
        Type type = d_nm.mk_fp_type(f.first, f.second);                 \
        FloatingPointSymFPU fp_symfpu1(type, bv1);                      \
        FloatingPointSymFPU fp_symfpu2(type, bv2);                      \
        ASSERT_EQ(fp1.fp##FUN(fp2).str(),                               \
                  fp_symfpu1.fp##FUN(fp_symfpu2).str());                \
      }                                                                 \
    }                                                                   \
  } while (0);

#define TEST_MIN_MAX(FUN, CMP)                                          \
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
      BitVector bv2(16, *d_rng);                                        \
      FloatingPoint fp1(d_fp16.first, d_fp16.second, bv1);              \
      FloatingPoint fp2(d_fp16.first, d_fp16.second, bv2);              \
      FloatingPoint fp = fp1.fp##FUN(fp2);                              \
      FloatingPointSymFPU fp_symfpu1(d_typefp16, bv1);                  \
      FloatingPointSymFPU fp_symfpu2(d_typefp16, bv2);                  \
      FloatingPointSymFPU fp_symfpu = fp_symfpu1.fp##FUN(fp_symfpu2);   \
      ASSERT_EQ(fp.str(), fp_symfpu.str());                             \
      if (!fp1.fpisnan() && !fp2.fpisnan())                             \
      {                                                                 \
        ASSERT_TRUE(fp1.fp##CMP(fp));                                   \
        ASSERT_TRUE(fp2.fp##CMP(fp));                                   \
        ASSERT_TRUE(fp_symfpu1.fp##CMP(fp_symfpu));                     \
        ASSERT_TRUE(fp_symfpu2.fp##CMP(fp_symfpu));                     \
      }                                                                 \
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
        FloatingPoint fp1(f.first, f.second, bv1);                      \
        FloatingPoint fp2(f.first, f.second, bv2);                      \
        Type type = d_nm.mk_fp_type(f.first, f.second);                 \
        FloatingPointSymFPU fp_symfpu1(type, bv1);                      \
        FloatingPointSymFPU fp_symfpu2(type, bv2);                      \
        ASSERT_EQ(fp1.fp##FUN(fp2).str(),                               \
                  fp_symfpu1.fp##FUN(fp_symfpu2).str());                \
      }                                                                 \
    }                                                                   \
  }                                                                     \
  while (0)

/* -------------------------------------------------------------------------- */

class TestFpBinary : public TestFp
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestFpBinary, rem) { TEST_BINARY(rem); }

TEST_F(TestFpBinary, min) { TEST_MIN_MAX(min, ge); }
TEST_F(TestFpBinary, max) { TEST_MIN_MAX(max, le); }
}  // namespace bzla::test
