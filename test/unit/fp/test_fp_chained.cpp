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

#define TEST_CHAINED_BINARY_REM(FUN)                                          \
  do                                                                          \
  {                                                                           \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {       \
      BitVector bv1;                                                          \
      if (d_rng->flip_coin())                                                 \
      {                                                                       \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);         \
      }                                                                       \
      else                                                                    \
      {                                                                       \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);          \
      }                                                                       \
      uint64_t exp_size = bvexp.size();                                       \
      uint64_t sig_size = bvsig.size() + 1;                                   \
      uint64_t bv_size  = exp_size + sig_size;                                \
      BitVector bv2(bv_size, *d_rng);                                         \
      BitVector bv3(bv_size, *d_rng);                                         \
      FloatingPoint fp1(exp_size, sig_size, bv1);                             \
      FloatingPoint fp2(exp_size, sig_size, bv2);                             \
      FloatingPoint fp3(exp_size, sig_size, bv2);                             \
      FloatingPoint fp(exp_size, sig_size);                                   \
      Type type = d_nm.mk_fp_type(exp_size, sig_size);                        \
      FloatingPointSymFPU fp_symfpu1(type, bv1);                              \
      FloatingPointSymFPU fp_symfpu2(type, bv2);                              \
      FloatingPointSymFPU fp_symfpu3(type, bv2);                              \
      FloatingPointSymFPU fp_symfpu(type);                                    \
      std::string fp_str, fp_symfpu_str;                                      \
      RoundingMode rm = pick_rm();                                            \
      if (d_rng->flip_coin())                                                 \
      {                                                                       \
        /* First, test order (a FUN b) rem c. */                              \
        fp            = fp1.fp##FUN(rm, fp2).fprem(fp3);                      \
        fp_symfpu     = fp_symfpu1.fp##FUN(rm, fp_symfpu2).fprem(fp_symfpu3); \
        fp_str        = fp.str();                                             \
        fp_symfpu_str = fp_symfpu.str();                                      \
        ASSERT_EQ(fp_str, fp_symfpu_str);                                     \
      }                                                                       \
      else                                                                    \
      {                                                                       \
        /* Then, test order (a rem b) FUN c. */                               \
        fp            = fp1.fprem(fp2).fp##FUN(rm, fp3);                      \
        fp_symfpu     = fp_symfpu1.fprem(fp_symfpu2).fp##FUN(rm, fp_symfpu3); \
        fp_str        = fp.str();                                             \
        fp_symfpu_str = fp_symfpu.str();                                      \
        ASSERT_EQ(fp_str, fp_symfpu_str);                                     \
      }                                                                       \
    };                                                                        \
    test_for_formats(d_all_formats, 100, fun);                                \
  } while (0)

#define TEST_CHAINED_BINARY_RM(FUN1, FUN2)                                  \
  do                                                                        \
  {                                                                         \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {     \
      BitVector bv1;                                                        \
      if (d_rng->flip_coin())                                               \
      {                                                                     \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);       \
      }                                                                     \
      else                                                                  \
      {                                                                     \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);        \
      }                                                                     \
      uint64_t exp_size = bvexp.size();                                     \
      uint64_t sig_size = bvsig.size() + 1;                                 \
      uint64_t bv_size  = exp_size + sig_size;                              \
      BitVector bv2(bv_size, *d_rng);                                       \
      BitVector bv3(bv_size, *d_rng);                                       \
      FloatingPoint fp1(exp_size, sig_size, bv1);                           \
      FloatingPoint fp2(exp_size, sig_size, bv2);                           \
      FloatingPoint fp3(exp_size, sig_size, bv2);                           \
      FloatingPoint fp(exp_size, sig_size);                                 \
      Type type = d_nm.mk_fp_type(bvexp.size(), bvsig.size() + 1);          \
      FloatingPointSymFPU fp_symfpu1(type, bv1);                            \
      FloatingPointSymFPU fp_symfpu2(type, bv2);                            \
      FloatingPointSymFPU fp_symfpu3(type, bv2);                            \
      FloatingPointSymFPU fp_symfpu(type);                                  \
      std::string fp_str, fp_symfpu_str;                                    \
      RoundingMode rm1 = pick_rm();                                         \
      RoundingMode rm2 = pick_rm();                                         \
      if (d_rng->flip_coin())                                               \
      {                                                                     \
        /* First, test order (a FUN1 b) FUN2 c. */                          \
        fp = fp1.fp##FUN1(rm1, fp2).fp##FUN2(rm2, fp3);                     \
        fp_symfpu =                                                         \
            fp_symfpu1.fp##FUN1(rm1, fp_symfpu2).fp##FUN2(rm2, fp_symfpu3); \
        fp_str        = fp.str();                                           \
        fp_symfpu_str = fp_symfpu.str();                                    \
        ASSERT_EQ(fp_str, fp_symfpu_str);                                   \
      }                                                                     \
      else                                                                  \
      {                                                                     \
        /* Then, test order (a FUN2 b) FUN1 c. */                           \
        fp = fp1.fp##FUN2(rm2, fp2).fp##FUN1(rm1, fp3);                     \
        fp_symfpu =                                                         \
            fp_symfpu1.fp##FUN2(rm2, fp_symfpu2).fp##FUN1(rm1, fp_symfpu3); \
        fp_str        = fp.str();                                           \
        fp_symfpu_str = fp_symfpu.str();                                    \
        ASSERT_EQ(fp_str, fp_symfpu_str);                                   \
      }                                                                     \
    };                                                                      \
    test_for_formats(d_all_formats, N_TESTS, fun);                          \
  } while (0)

#define TEST_CHAINED_UNARY_BINARY_RM(FUN1, FUN2)                        \
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
      uint64_t exp_size = bvexp.size();                                 \
      uint64_t sig_size = bvsig.size() + 1;                             \
      uint64_t bv_size  = exp_size + sig_size;                          \
      BitVector bv2(bv_size, *d_rng);                                   \
      FloatingPoint fp1(exp_size, sig_size, bv1);                       \
      FloatingPoint fp2(exp_size, sig_size, bv2);                       \
      FloatingPoint fp(exp_size, sig_size);                             \
      Type type = d_nm.mk_fp_type(exp_size, sig_size);                  \
      FloatingPointSymFPU fp_symfpu1(type, bv1);                        \
      FloatingPointSymFPU fp_symfpu2(type, bv2);                        \
      FloatingPointSymFPU fp_symfpu(type);                              \
      std::string fp_str, fp_symfpu_str;                                \
      RoundingMode rm = pick_rm();                                      \
      fp              = fp1.fp##FUN2(rm, fp2).fp##FUN1();               \
      fp_symfpu       = fp_symfpu1.fp##FUN2(rm, fp_symfpu2).fp##FUN1(); \
      fp_str          = fp.str();                                       \
      fp_symfpu_str   = fp_symfpu.str();                                \
      ASSERT_EQ(fp_str, fp_symfpu_str);                                 \
    };                                                                  \
    test_for_formats(d_all_formats, N_TESTS, fun);                      \
  } while (0)

#define TEST_CHAINED_UNARY_RM_BINARY_RM(FUN1, FUN2)                          \
  do                                                                         \
  {                                                                          \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {      \
      BitVector bv1;                                                         \
      if (d_rng->flip_coin())                                                \
      {                                                                      \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);        \
      }                                                                      \
      else                                                                   \
      {                                                                      \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);         \
      }                                                                      \
      uint64_t exp_size = bvexp.size();                                      \
      uint64_t sig_size = bvsig.size() + 1;                                  \
      uint64_t bv_size  = exp_size + sig_size;                               \
      BitVector bv2(bv_size, *d_rng);                                        \
      FloatingPoint fp1(exp_size, sig_size, bv1);                            \
      FloatingPoint fp2(exp_size, sig_size, bv2);                            \
      FloatingPoint fp(exp_size, sig_size);                                  \
      Type type = d_nm.mk_fp_type(exp_size, sig_size);                       \
      FloatingPointSymFPU fp_symfpu1(type, bv1);                             \
      FloatingPointSymFPU fp_symfpu2(type, bv2);                             \
      FloatingPointSymFPU fp_symfpu(type);                                   \
      std::string fp_str, fp_symfpu_str;                                     \
      RoundingMode rm1 = pick_rm();                                          \
      RoundingMode rm2 = pick_rm();                                          \
      fp               = fp1.fp##FUN2(rm2, fp2).fp##FUN1(rm1);               \
      fp_symfpu        = fp_symfpu1.fp##FUN2(rm2, fp_symfpu2).fp##FUN1(rm1); \
      fp_str           = fp.str();                                           \
      fp_symfpu_str    = fp_symfpu.str();                                    \
      ASSERT_EQ(fp_str, fp_symfpu_str);                                      \
    };                                                                       \
    test_for_formats(d_all_formats, N_TESTS, fun);                           \
  } while (0)

/* -------------------------------------------------------------------------- */

class TestFpChained : public TestFp
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestFpChained, chained_rem)
{
  // (a + b) rem c, (a rem b) + c
  TEST_CHAINED_BINARY_REM(add);
  // (a * b) rem c, (a rem b) * c
  TEST_CHAINED_BINARY_REM(mul);
#ifdef NDEBUG
  // SymFPU may fail with an assertion failure (see issue #164) but agrees with
  // MPFR on all tests for release builds without assertions.
  // (a / b) rem c, (a rem b) / c
  TEST_CHAINED_BINARY_REM(div);
#endif
}
TEST_F(TestFpChained, chained_bin_rm)
{
  TEST_CHAINED_BINARY_RM(add, mul);
#ifdef NDEBUG
  // SymFPU may fail with an assertion failure (see issue #164) but agrees with
  // MPFR on all tests for release builds without assertions.
  // (a / b) rem c, (a rem b) / c
  TEST_CHAINED_BINARY_RM(add, div);
#endif
}
TEST_F(TestFpChained, chained_un_bin_rm)
{
  TEST_CHAINED_UNARY_BINARY_RM(abs, add);
  TEST_CHAINED_UNARY_BINARY_RM(neg, add);
  TEST_CHAINED_UNARY_BINARY_RM(abs, mul);
  TEST_CHAINED_UNARY_BINARY_RM(neg, mul);
#ifdef NDEBUG
  // SymFPU may fail with an assertion failure (see issue #164) but agrees with
  // MPFR on all tests for release builds without assertions.
  // (a / b) rem c, (a rem b) / c
  TEST_CHAINED_UNARY_BINARY_RM(abs, div);
  TEST_CHAINED_UNARY_BINARY_RM(neg, div);
#endif
}
TEST_F(TestFpChained, chained_un_rm_bin_rm)
{
  TEST_CHAINED_UNARY_RM_BINARY_RM(sqrt, add);
  TEST_CHAINED_UNARY_RM_BINARY_RM(rti, add);
  TEST_CHAINED_UNARY_RM_BINARY_RM(sqrt, mul);
  TEST_CHAINED_UNARY_RM_BINARY_RM(rti, mul);
#ifdef NDEBUG
  // SymFPU may fail with an assertion failure (see issue #164) but agrees with
  // MPFR on all tests for release builds without assertions.
  // (a / b) rem c, (a rem b) / c
  TEST_CHAINED_UNARY_RM_BINARY_RM(sqrt, div);
  TEST_CHAINED_UNARY_RM_BINARY_RM(rti, div);
#endif
}

}  // namespace bzla::test
