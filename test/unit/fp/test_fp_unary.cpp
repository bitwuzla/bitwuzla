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

#define TEST_UNARY(FUN)                                                        \
  do                                                                           \
  {                                                                            \
    /* comprehensive tests for all values in Float16 */                        \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {        \
      BitVector _bv = bvexp.bvconcat(bvsig);                                   \
      for (const auto& bv : {BitVector::mk_false().ibvconcat(_bv),             \
                             BitVector::mk_true().ibvconcat(_bv)})             \
      {                                                                        \
        FloatingPoint fp(d_fp16.first, d_fp16.second, bv);                     \
        FloatingPointSymFPU fp_symfpu(d_typefp16, bv);                         \
        std::string fp_str        = fp.fp##FUN().str();                        \
        std::string fp_symfpu_str = fp_symfpu.fp##FUN().str();                 \
        ASSERT_EQ(fp_str, fp_symfpu_str);                                      \
      }                                                                        \
    };                                                                         \
    test_for_float16(fun);                                                     \
    /* random tests for Float32, Float64, Float128 */                          \
    for (const auto& f : d_formats_32_128)                                     \
    {                                                                          \
      uint64_t bv_size = f.first + f.second;                                   \
      for (uint32_t i = 0; i < N_TESTS; ++i)                                   \
      {                                                                        \
        BitVector bv = BitVector(bv_size, *d_rng);                             \
        FloatingPoint fp(f.first, f.second, bv);                               \
        FloatingPointSymFPU fp_symfpu(d_nm.mk_fp_type(f.first, f.second), bv); \
        ASSERT_EQ(fp.fp##FUN().str(), fp_symfpu.fp##FUN().str());              \
      }                                                                        \
    }                                                                          \
  } while (0);

#define TEST_UNARY_RM(FUN)                                                     \
  do                                                                           \
  {                                                                            \
    /* comprehensive tests for all values in Float16 */                        \
    auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {        \
      BitVector _bv = bvexp.bvconcat(bvsig);                                   \
      for (const auto& bv : {BitVector::mk_false().ibvconcat(_bv),             \
                             BitVector::mk_true().ibvconcat(_bv)})             \
      {                                                                        \
        FloatingPoint fp(d_fp16.first, d_fp16.second, bv);                     \
        FloatingPointSymFPU fp_symfpu(d_typefp16, bv);                         \
        for (auto rm : d_all_rms)                                              \
        {                                                                      \
          std::string fp_str        = fp.fp##FUN(rm).str();                    \
          std::string fp_symfpu_str = fp_symfpu.fp##FUN(rm).str();             \
          ASSERT_EQ(fp_str, fp_symfpu_str);                                    \
        }                                                                      \
      }                                                                        \
    };                                                                         \
    test_for_float16(fun);                                                     \
    /* random tests for Float32, Float64, Float128 */                          \
    for (const auto& f : d_formats_32_128)                                     \
    {                                                                          \
      uint64_t bv_size = f.first + f.second;                                   \
      for (uint32_t i = 0; i < N_TESTS; ++i)                                   \
      {                                                                        \
        BitVector bv = BitVector(bv_size, *d_rng);                             \
        FloatingPoint fp(f.first, f.second, bv);                               \
        FloatingPointSymFPU fp_symfpu(d_nm.mk_fp_type(f.first, f.second), bv); \
        for (auto rm : d_all_rms)                                              \
        {                                                                      \
          std::string fp_str        = fp.fp##FUN(rm).str();                    \
          std::string fp_symfpu_str = fp_symfpu.fp##FUN(rm).str();             \
          ASSERT_EQ(fp_str, fp_symfpu_str);                                    \
        }                                                                      \
      }                                                                        \
    }                                                                          \
  } while (0);

/* -------------------------------------------------------------------------- */

class TestFpUnary : public TestFp
{
};

/* -------------------------------------------------------------------------- */

TEST_F(TestFpUnary, abs) { TEST_UNARY(abs); }
TEST_F(TestFpUnary, neg) { TEST_UNARY(neg); }
TEST_F(TestFpUnary, sqrt) { TEST_UNARY_RM(sqrt); }
TEST_F(TestFpUnary, rti) { TEST_UNARY_RM(rti); }

TEST_F(TestFpUnary, isX)
{
  auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {
    bool exp_iszero = bvexp.is_zero();
    bool exp_isones = bvexp.is_ones();
    for (bool sign : {false, true})
    {
      BitVector bvsign = sign ? BitVector::mk_true() : BitVector::mk_false();
      FloatingPoint fp(5, 11, bvsign.bvconcat(bvexp).ibvconcat(bvsig));
      FloatingPoint fp_symfpu(5, 11, bvsign.bvconcat(bvexp).ibvconcat(bvsig));
      ASSERT_EQ(fp.fpisnormal(), fp_symfpu.fpisnormal());
      ASSERT_EQ(fp.fpissubnormal(), fp_symfpu.fpissubnormal());
      ASSERT_EQ(fp.fpiszero(), fp_symfpu.fpiszero());
      ASSERT_EQ(fp.fpisinf(), fp_symfpu.fpisinf());
      ASSERT_EQ(fp.fpisnan(), fp_symfpu.fpisnan());
      if (!exp_iszero)
      {
        if (!exp_isones)
        {
          ASSERT_TRUE(fp.fpisnormal());
          ASSERT_FALSE(fp.fpissubnormal());
          ASSERT_FALSE(fp.fpisinf());
          ASSERT_FALSE(fp.fpisnan());
          ASSERT_FALSE(fp.fpiszero());
        }
        else
        {
          if (bvsig.is_zero())
          {
            ASSERT_TRUE(fp.fpisinf());
            ASSERT_FALSE(fp.fpisnan());
            ASSERT_FALSE(fp.fpisnormal());
            ASSERT_FALSE(fp.fpissubnormal());
            ASSERT_FALSE(fp.fpiszero());
          }
          else
          {
            ASSERT_TRUE(fp.fpisnan());
            ASSERT_FALSE(fp.fpisinf());
            ASSERT_FALSE(fp.fpisnormal());
            ASSERT_FALSE(fp.fpissubnormal());
            ASSERT_FALSE(fp.fpiszero());
          }
        }
      }
      else
      {
        if (bvsig.is_zero())
        {
          ASSERT_TRUE(fp.fpiszero());
          ASSERT_FALSE(fp.fpisnormal());
          ASSERT_FALSE(fp.fpissubnormal());
          ASSERT_FALSE(fp.fpisinf());
          ASSERT_FALSE(fp.fpisnan());
        }
        else
        {
          ASSERT_TRUE(fp.fpissubnormal());
          ASSERT_FALSE(fp.fpisnormal());
          ASSERT_FALSE(fp.fpisinf());
          ASSERT_FALSE(fp.fpisnan());
          ASSERT_FALSE(fp.fpiszero());
        }
      }
    }
  };
  test_for_float16(fun);
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
