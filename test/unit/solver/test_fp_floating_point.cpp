/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2019 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <bitset>
#include <cstdint>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "rng/rng.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/floating_point_mpfr.h"
#include "solver/fp/symfpu_nm.h"
#include "test/unit/test.h"

/* -------------------------------------------------------------------------- */

#define TEST_UNARY(FUN)                                                 \
  do                                                                    \
  {                                                                     \
    /* comprehensive tests for all values in Float16 */                 \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) { \
      BitVector _bv = bvexp.bvconcat(bvsig);                            \
      for (const auto &bv : {BitVector::mk_false().ibvconcat(_bv),      \
                             BitVector::mk_true().ibvconcat(_bv)})      \
      {                                                                 \
        FloatingPoint fp(d_fp16, bv);                                   \
        FloatingPointMPFR fp_mpfr(d_fp16, bv);                          \
        std::string fp_str      = fp.fp##FUN().str();                   \
        std::string fp_mpfr_str = fp_mpfr.fp##FUN().str();              \
        if (fp_str != fp_mpfr_str)                                      \
        {                                                               \
          std::cout << "bv: " << bv << std::endl;                       \
          std::cout << "fp: " << fp_str << std::endl;                   \
          std::cout << "fp_mpfr: " << fp_mpfr_str << std::endl;         \
        }                                                               \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                 \
      }                                                                 \
    };                                                                  \
    test_for_float16(fun);                                              \
    /* random tests for Float32, Float64, Float128 */                   \
    for (const auto &type : d_formats_32_128)                           \
    {                                                                   \
      uint64_t bv_size = type.fp_ieee_bv_size();                        \
      for (uint32_t i = 0; i < N_TESTS; ++i)                            \
      {                                                                 \
        BitVector bv = BitVector(bv_size, *d_rng);                      \
        FloatingPoint fp(type, bv);                                     \
        FloatingPointMPFR fp_mpfr(type, bv);                            \
        ASSERT_EQ(fp.fp##FUN().str(), fp_mpfr.fp##FUN().str());         \
      }                                                                 \
    }                                                                   \
  } while (0);

#define TEST_UNARY_RM(FUN)                                              \
  do                                                                    \
  {                                                                     \
    /* comprehensive tests for all values in Float16 */                 \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) { \
      BitVector _bv = bvexp.bvconcat(bvsig);                            \
      for (const auto &bv : {BitVector::mk_false().ibvconcat(_bv),      \
                             BitVector::mk_true().ibvconcat(_bv)})      \
      {                                                                 \
        FloatingPoint fp(d_fp16, bv);                                   \
        FloatingPointMPFR fp_mpfr(d_fp16, bv);                          \
        for (auto rm : d_all_rms)                                       \
        {                                                               \
          std::string fp_str      = fp.fp##FUN(rm).str();               \
          std::string fp_mpfr_str = fp_mpfr.fp##FUN(rm).str();          \
          if (fp_str != fp_mpfr_str)                                    \
          {                                                             \
            std::cout << "rm: " << rm << std::endl;                     \
            std::cout << "bv: " << bv << std::endl;                     \
            std::cout << "fp: " << fp_str << std::endl;                 \
            std::cout << "fp_mpfr: " << fp_mpfr_str << std::endl;       \
          }                                                             \
          ASSERT_EQ(fp_str, fp_mpfr_str);                               \
        }                                                               \
      }                                                                 \
    };                                                                  \
    test_for_float16(fun);                                              \
    /* random tests for Float32, Float64, Float128 */                   \
    for (const auto &type : d_formats_32_128)                           \
    {                                                                   \
      uint64_t bv_size = type.fp_ieee_bv_size();                        \
      for (uint32_t i = 0; i < N_TESTS; ++i)                            \
      {                                                                 \
        BitVector bv = BitVector(bv_size, *d_rng);                      \
        FloatingPoint fp(type, bv);                                     \
        FloatingPointMPFR fp_mpfr(type, bv);                            \
        for (auto rm : d_all_rms)                                       \
        {                                                               \
          std::string fp_str      = fp.fp##FUN(rm).str();               \
          std::string fp_mpfr_str = fp_mpfr.fp##FUN(rm).str();          \
          if (fp_str != fp_mpfr_str)                                    \
          {                                                             \
            std::cout << "rm: " << rm << std::endl;                     \
            std::cout << "bv: " << bv << std::endl;                     \
            std::cout << "fp: " << fp_str << std::endl;                 \
            std::cout << "fp_mpfr: " << fp_mpfr_str << std::endl;       \
          }                                                             \
          ASSERT_EQ(fp_str, fp_mpfr_str);                               \
        }                                                               \
      }                                                                 \
    }                                                                   \
  } while (0);

#define TEST_BINARY(FUN)                                                     \
  do                                                                         \
  {                                                                          \
    /* more comprehensive tests for all values in Float16 */                 \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {      \
      BitVector bv1;                                                         \
      if (d_rng->flip_coin())                                                \
      {                                                                      \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);        \
      }                                                                      \
      else                                                                   \
      {                                                                      \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);         \
      }                                                                      \
      BitVector bv2 = BitVector(16, *d_rng);                                 \
      FloatingPoint fp1(d_fp16, bv1);                                        \
      FloatingPoint fp2(d_fp16, bv2);                                        \
      FloatingPointMPFR fp_mpfr1(d_fp16, bv1);                               \
      FloatingPointMPFR fp_mpfr2(d_fp16, bv2);                               \
      std::string fp_str      = fp1.fp##FUN(fp2).str();                      \
      std::string fp_mpfr_str = fp_mpfr1.fp##FUN(fp_mpfr2).str();            \
      if (fp_str != fp_mpfr_str)                                             \
      {                                                                      \
        std::cout << "bv1: " << bv1 << std::endl;                            \
        std::cout << "bv2: " << bv2 << std::endl;                            \
        std::cout << "fp: " << fp_str << std::endl;                          \
        std::cout << "fp_mpfr: " << fp_mpfr_str << std::endl;                \
      }                                                                      \
      ASSERT_EQ(fp_str, fp_mpfr_str);                                        \
    };                                                                       \
    test_for_float16(fun);                                                   \
                                                                             \
    /* random tests for Float32, Float64, Float128 */                        \
    for (const auto &type : d_formats_32_128)                                \
    {                                                                        \
      uint64_t bv_size = type.fp_ieee_bv_size();                             \
      for (uint32_t i = 0; i < N_TESTS; ++i)                                 \
      {                                                                      \
        BitVector bv1 = BitVector(bv_size, *d_rng);                          \
        BitVector bv2 = BitVector(bv_size, *d_rng);                          \
        FloatingPoint fp1(type, bv1);                                        \
        FloatingPoint fp2(type, bv2);                                        \
        FloatingPointMPFR fp_mpfr1(type, bv1);                               \
        FloatingPointMPFR fp_mpfr2(type, bv2);                               \
        ASSERT_EQ(fp1.fp##FUN(fp2).str(), fp_mpfr1.fp##FUN(fp_mpfr2).str()); \
      }                                                                      \
    }                                                                        \
  } while (0);

#define TEST_BINARY_RM(FUN)                                                \
  do                                                                       \
  {                                                                        \
    /* more comprehensive tests for all values in Float16 */               \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {    \
      BitVector bv1;                                                       \
      if (d_rng->flip_coin())                                              \
      {                                                                    \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);      \
      }                                                                    \
      else                                                                 \
      {                                                                    \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);       \
      }                                                                    \
      BitVector bv2(16, *d_rng);                                           \
      FloatingPoint fp1(d_fp16, bv1);                                      \
      FloatingPoint fp2(d_fp16, bv2);                                      \
      FloatingPointMPFR fp_mpfr1(d_fp16, bv1);                             \
      FloatingPointMPFR fp_mpfr2(d_fp16, bv2);                             \
      for (auto rm : d_all_rms)                                            \
      {                                                                    \
        FloatingPoint fp          = fp1.fp##FUN(rm, fp2);                  \
        FloatingPointMPFR fp_mpfr = fp_mpfr1.fp##FUN(rm, fp_mpfr2);        \
        std::string fp_str        = fp.str();                              \
        std::string fp_mpfr_str   = fp_mpfr.str();                         \
        if (fp_str != fp_mpfr_str)                                         \
        {                                                                  \
          std::cout << "rm: " << rm << std::endl;                          \
          std::cout << "bv1: " << bv1 << std::endl;                        \
          std::cout << "bv2: " << bv2 << std::endl;                        \
          std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")" \
                    << std::endl;                                          \
          std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                  \
                    << fp_mpfr.to_real_str() << ")" << std::endl;          \
        }                                                                  \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                    \
      }                                                                    \
    };                                                                     \
    test_for_float16(fun);                                                 \
                                                                           \
    /* random tests for Float32, Float64, Float128 */                      \
    for (const auto &type : d_formats_32_128)                              \
    {                                                                      \
      uint64_t bv_size = type.fp_ieee_bv_size();                           \
      for (uint32_t i = 0; i < N_TESTS; ++i)                               \
      {                                                                    \
        BitVector bv1 = BitVector(bv_size, *d_rng);                        \
        BitVector bv2 = BitVector(bv_size, *d_rng);                        \
        FloatingPoint fp1(type, bv1);                                      \
        FloatingPoint fp2(type, bv2);                                      \
        FloatingPointMPFR fp_mpfr1(type, bv1);                             \
        FloatingPointMPFR fp_mpfr2(type, bv2);                             \
        for (auto rm : d_all_rms)                                          \
        {                                                                  \
          ASSERT_EQ(fp1.fp##FUN(rm, fp2).str(),                            \
                    fp_mpfr1.fp##FUN(rm, fp_mpfr2).str());                 \
        }                                                                  \
      }                                                                    \
    }                                                                      \
  } while (0);

#define TEST_TERNARY_RM(FUN)                                            \
  do                                                                    \
  {                                                                     \
    /* more comprehensive tests for all values in Float16 */            \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) { \
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
      BitVector bv3(16, *d_rng);                                        \
      FloatingPoint fp1(d_fp16, bv1);                                   \
      FloatingPoint fp2(d_fp16, bv2);                                   \
      FloatingPoint fp3(d_fp16, bv2);                                   \
      FloatingPointMPFR fp_mpfr1(d_fp16, bv1);                          \
      FloatingPointMPFR fp_mpfr2(d_fp16, bv2);                          \
      FloatingPointMPFR fp_mpfr3(d_fp16, bv2);                          \
      for (auto rm : d_all_rms)                                         \
      {                                                                 \
        std::string fp_str = fp1.fp##FUN(rm, fp2, fp3).str();           \
        std::string fp_mpfr_str =                                       \
            fp_mpfr1.fp##FUN(rm, fp_mpfr2, fp_mpfr3).str();             \
        if (fp_str != fp_mpfr_str)                                      \
        {                                                               \
          std::cout << "rm: " << rm << std::endl;                       \
          std::cout << "bv1: " << bv1 << std::endl;                     \
          std::cout << "bv2: " << bv2 << std::endl;                     \
          std::cout << "fp: " << fp_str << std::endl;                   \
          std::cout << "fp_mpfr: " << fp_mpfr_str << std::endl;         \
        }                                                               \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                 \
      }                                                                 \
    };                                                                  \
    test_for_float16(fun);                                              \
                                                                        \
    /* random tests for Float32, Float64, Float128 */                   \
    for (const auto &type : d_formats_32_128)                           \
    {                                                                   \
      uint64_t bv_size = type.fp_ieee_bv_size();                        \
      for (uint32_t i = 0; i < N_TESTS; ++i)                            \
      {                                                                 \
        BitVector bv1 = BitVector(bv_size, *d_rng);                     \
        BitVector bv2 = BitVector(bv_size, *d_rng);                     \
        BitVector bv3 = BitVector(bv_size, *d_rng);                     \
        FloatingPoint fp1(type, bv1);                                   \
        FloatingPoint fp2(type, bv2);                                   \
        FloatingPoint fp3(type, bv3);                                   \
        FloatingPointMPFR fp_mpfr1(type, bv1);                          \
        FloatingPointMPFR fp_mpfr2(type, bv2);                          \
        FloatingPointMPFR fp_mpfr3(type, bv3);                          \
        for (auto rm : d_all_rms)                                       \
        {                                                               \
          ASSERT_EQ(fp1.fp##FUN(rm, fp2, fp3).str(),                    \
                    fp_mpfr1.fp##FUN(rm, fp_mpfr2, fp_mpfr3).str());    \
        }                                                               \
      }                                                                 \
    }                                                                   \
  } while (0);

#define TEST_CHAINED_BINARY_REM(FUN)                                       \
  do                                                                       \
  {                                                                        \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {    \
      BitVector bv1;                                                       \
      if (d_rng->flip_coin())                                              \
      {                                                                    \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);      \
      }                                                                    \
      else                                                                 \
      {                                                                    \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);       \
      }                                                                    \
      uint64_t bv_size = bvexp.size() + bvsig.size() + 1;                  \
      Type fp_type     = d_nm.mk_fp_type(bvexp.size(), bvsig.size() + 1);  \
      BitVector bv2(bv_size, *d_rng);                                      \
      BitVector bv3(bv_size, *d_rng);                                      \
      FloatingPoint fp1(fp_type, bv1);                                     \
      FloatingPoint fp2(fp_type, bv2);                                     \
      FloatingPoint fp3(fp_type, bv2);                                     \
      FloatingPointMPFR fp_mpfr1(fp_type, bv1);                            \
      FloatingPointMPFR fp_mpfr2(fp_type, bv2);                            \
      FloatingPointMPFR fp_mpfr3(fp_type, bv2);                            \
      FloatingPoint fp(fp_type);                                           \
      FloatingPointMPFR fp_mpfr(fp_type);                                  \
      std::string fp_str, fp_mpfr_str;                                     \
      RoundingMode rm = pick_rm();                                         \
      if (d_rng->flip_coin())                                              \
      {                                                                    \
        /* First, test order (a FUN b) rem c. */                           \
        fp          = fp1.fp##FUN(rm, fp2).fprem(fp3);                     \
        fp_mpfr     = fp_mpfr1.fp##FUN(rm, fp_mpfr2).fprem(fp_mpfr3);      \
        fp_str      = fp.str();                                            \
        fp_mpfr_str = fp_mpfr.str();                                       \
        if (fp_str != fp_mpfr_str)                                         \
        {                                                                  \
          std::cout << "rm: " << rm << std::endl;                          \
          std::cout << "bv1: " << bv1 << std::endl;                        \
          std::cout << "bv2: " << bv2 << std::endl;                        \
          std::cout << "bv3: " << bv3 << std::endl;                        \
          std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")" \
                    << std::endl;                                          \
          std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                  \
                    << fp_mpfr.to_real_str() << ")" << std::endl;          \
        }                                                                  \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                    \
      }                                                                    \
      else                                                                 \
      {                                                                    \
        /* Then, test order (a rem b) FUN c. */                            \
        fp          = fp1.fprem(fp2).fp##FUN(rm, fp3);                     \
        fp_mpfr     = fp_mpfr1.fprem(fp_mpfr2).fp##FUN(rm, fp_mpfr3);      \
        fp_str      = fp.str();                                            \
        fp_mpfr_str = fp_mpfr.str();                                       \
        if (fp_str != fp_mpfr_str)                                         \
        {                                                                  \
          std::cout << "rm: " << rm << std::endl;                          \
          std::cout << "bv1: " << bv1 << std::endl;                        \
          std::cout << "bv2: " << bv2 << std::endl;                        \
          std::cout << "bv3: " << bv3 << std::endl;                        \
          std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")" \
                    << std::endl;                                          \
          std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                  \
                    << fp_mpfr.to_real_str() << ")" << std::endl;          \
        }                                                                  \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                    \
      }                                                                    \
    };                                                                     \
    test_for_formats(d_all_formats, 100, fun);                             \
  } while (0)

#define TEST_CHAINED_BINARY_RM(FUN1, FUN2)                                      \
  do                                                                            \
  {                                                                             \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {         \
      BitVector bv1;                                                            \
      if (d_rng->flip_coin())                                                   \
      {                                                                         \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);           \
      }                                                                         \
      else                                                                      \
      {                                                                         \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);            \
      }                                                                         \
      uint64_t bv_size = bvexp.size() + bvsig.size() + 1;                       \
      Type fp_type     = d_nm.mk_fp_type(bvexp.size(), bvsig.size() + 1);       \
      BitVector bv2(bv_size, *d_rng);                                           \
      BitVector bv3(bv_size, *d_rng);                                           \
      FloatingPoint fp1(fp_type, bv1);                                          \
      FloatingPoint fp2(fp_type, bv2);                                          \
      FloatingPoint fp3(fp_type, bv2);                                          \
      FloatingPointMPFR fp_mpfr1(fp_type, bv1);                                 \
      FloatingPointMPFR fp_mpfr2(fp_type, bv2);                                 \
      FloatingPointMPFR fp_mpfr3(fp_type, bv2);                                 \
      FloatingPoint fp(fp_type);                                                \
      FloatingPointMPFR fp_mpfr(fp_type);                                       \
      std::string fp_str, fp_mpfr_str;                                          \
      RoundingMode rm1 = pick_rm();                                             \
      RoundingMode rm2 = pick_rm();                                             \
      if (d_rng->flip_coin())                                                   \
      {                                                                         \
        /* First, test order (a FUN1 b) FUN2 c. */                              \
        fp          = fp1.fp##FUN1(rm1, fp2).fp##FUN2(rm2, fp3);                \
        fp_mpfr     = fp_mpfr1.fp##FUN1(rm1, fp_mpfr2).fp##FUN2(rm2, fp_mpfr3); \
        fp_str      = fp.str();                                                 \
        fp_mpfr_str = fp_mpfr.str();                                            \
        if (fp_str != fp_mpfr_str)                                              \
        {                                                                       \
          std::cout << "rm1: " << rm1 << std::endl;                             \
          std::cout << "rm2: " << rm2 << std::endl;                             \
          std::cout << "bv1: " << bv1 << std::endl;                             \
          std::cout << "bv2: " << bv2 << std::endl;                             \
          std::cout << "bv3: " << bv3 << std::endl;                             \
          std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")"      \
                    << std::endl;                                               \
          std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                       \
                    << fp_mpfr.to_real_str() << ")" << std::endl;               \
        }                                                                       \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                         \
      }                                                                         \
      else                                                                      \
      {                                                                         \
        /* Then, test order (a FUN2 b) FUN1 c. */                               \
        fp          = fp1.fp##FUN2(rm2, fp2).fp##FUN1(rm1, fp3);                \
        fp_mpfr     = fp_mpfr1.fp##FUN2(rm2, fp_mpfr2).fp##FUN1(rm1, fp_mpfr3); \
        fp_str      = fp.str();                                                 \
        fp_mpfr_str = fp_mpfr.str();                                            \
        if (fp_str != fp_mpfr_str)                                              \
        {                                                                       \
          std::cout << "rm1: " << rm1 << std::endl;                             \
          std::cout << "rm2: " << rm2 << std::endl;                             \
          std::cout << "bv1: " << bv1 << std::endl;                             \
          std::cout << "bv2: " << bv2 << std::endl;                             \
          std::cout << "bv3: " << bv3 << std::endl;                             \
          std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")"      \
                    << std::endl;                                               \
          std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                       \
                    << fp_mpfr.to_real_str() << ")" << std::endl;               \
        }                                                                       \
        ASSERT_EQ(fp_str, fp_mpfr_str);                                         \
      }                                                                         \
    };                                                                          \
    test_for_formats(d_all_formats, N_TESTS, fun);                              \
  } while (0)

#define TEST_CHAINED_UNARY_BINARY_RM(FUN1, FUN2)                          \
  do                                                                      \
  {                                                                       \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {   \
      BitVector bv1;                                                      \
      if (d_rng->flip_coin())                                             \
      {                                                                   \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);     \
      }                                                                   \
      else                                                                \
      {                                                                   \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);      \
      }                                                                   \
      uint64_t bv_size = bvexp.size() + bvsig.size() + 1;                 \
      Type fp_type     = d_nm.mk_fp_type(bvexp.size(), bvsig.size() + 1); \
      BitVector bv2(bv_size, *d_rng);                                     \
      FloatingPoint fp1(fp_type, bv1);                                    \
      FloatingPoint fp2(fp_type, bv2);                                    \
      FloatingPointMPFR fp_mpfr1(fp_type, bv1);                           \
      FloatingPointMPFR fp_mpfr2(fp_type, bv2);                           \
      FloatingPoint fp(fp_type);                                          \
      FloatingPointMPFR fp_mpfr(fp_type);                                 \
      std::string fp_str, fp_mpfr_str;                                    \
      RoundingMode rm = pick_rm();                                        \
      fp              = fp1.fp##FUN2(rm, fp2).fp##FUN1();                 \
      fp_mpfr         = fp_mpfr1.fp##FUN2(rm, fp_mpfr2).fp##FUN1();       \
      fp_str          = fp.str();                                         \
      fp_mpfr_str     = fp_mpfr.str();                                    \
      if (fp_str != fp_mpfr_str)                                          \
      {                                                                   \
        std::cout << "rm: " << rm << std::endl;                           \
        std::cout << "bv1: " << bv1 << std::endl;                         \
        std::cout << "bv2: " << bv2 << std::endl;                         \
        std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")"  \
                  << std::endl;                                           \
        std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                   \
                  << fp_mpfr.to_real_str() << ")" << std::endl;           \
      }                                                                   \
      ASSERT_EQ(fp_str, fp_mpfr_str);                                     \
    };                                                                    \
    test_for_formats(d_all_formats, N_TESTS, fun);                        \
  } while (0)

#define TEST_CHAINED_UNARY_RM_BINARY_RM(FUN1, FUN2)                       \
  do                                                                      \
  {                                                                       \
    auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {   \
      BitVector bv1;                                                      \
      if (d_rng->flip_coin())                                             \
      {                                                                   \
        bv1 = BitVector::mk_false().ibvconcat(bvexp).bvconcat(bvsig);     \
      }                                                                   \
      else                                                                \
      {                                                                   \
        bv1 = BitVector::mk_true().ibvconcat(bvexp).bvconcat(bvsig);      \
      }                                                                   \
      uint64_t bv_size = bvexp.size() + bvsig.size() + 1;                 \
      Type fp_type     = d_nm.mk_fp_type(bvexp.size(), bvsig.size() + 1); \
      BitVector bv2(bv_size, *d_rng);                                     \
      FloatingPoint fp1(fp_type, bv1);                                    \
      FloatingPoint fp2(fp_type, bv2);                                    \
      FloatingPointMPFR fp_mpfr1(fp_type, bv1);                           \
      FloatingPointMPFR fp_mpfr2(fp_type, bv2);                           \
      FloatingPoint fp(fp_type);                                          \
      FloatingPointMPFR fp_mpfr(fp_type);                                 \
      std::string fp_str, fp_mpfr_str;                                    \
      RoundingMode rm1 = pick_rm();                                       \
      RoundingMode rm2 = pick_rm();                                       \
      fp               = fp1.fp##FUN2(rm2, fp2).fp##FUN1(rm1);            \
      fp_mpfr          = fp_mpfr1.fp##FUN2(rm2, fp_mpfr2).fp##FUN1(rm1);  \
      fp_str           = fp.str();                                        \
      fp_mpfr_str      = fp_mpfr.str();                                   \
      if (fp_str != fp_mpfr_str)                                          \
      {                                                                   \
        std::cout << "rm1: " << rm1 << std::endl;                         \
        std::cout << "rm2: " << rm2 << std::endl;                         \
        std::cout << "bv1: " << bv1 << std::endl;                         \
        std::cout << "bv2: " << bv2 << std::endl;                         \
        std::cout << "fp: " << fp_str << " (" << fp.to_real_str() << ")"  \
                  << std::endl;                                           \
        std::cout << "fp_mpfr: " << fp_mpfr_str << " ("                   \
                  << fp_mpfr.to_real_str() << ")" << std::endl;           \
      }                                                                   \
      ASSERT_EQ(fp_str, fp_mpfr_str);                                     \
    };                                                                    \
    test_for_formats(d_all_formats, N_TESTS, fun);                        \
  } while (0)

/* -------------------------------------------------------------------------- */

namespace bzla::test {

using namespace node;

class TestFp : public TestCommon
{
  TestFp() : snm(d_nm) {}

 protected:
  static constexpr uint32_t N_TESTS = 1000;

  enum RationalMode
  {
    INT,
    NUM_DEC,
    DEN_DEC,
    DEC
  };

  void SetUp() override
  {
    TestCommon::SetUp();
    d_rng.reset(new RNG(1234));
    d_fp16  = d_nm.mk_fp_type(5, 11);
    d_fp32  = d_nm.mk_fp_type(8, 24);
    d_fp64  = d_nm.mk_fp_type(11, 53);
    d_fp128 = d_nm.mk_fp_type(15, 113);
    for (int32_t i = 0, n = static_cast<int32_t>(RoundingMode::NUM_RM); i < n;
         ++i)
    {
      d_all_rms.push_back(static_cast<RoundingMode>(i));
    }
    d_all_formats    = {d_fp16, d_fp32, d_fp64, d_fp128};
    d_formats_32_128 = {d_fp32, d_fp64, d_fp128};
  }

  RoundingMode pick_rm() const
  {
    return d_rng->pick_from_set<std::vector<RoundingMode>, RoundingMode>(
        d_all_rms);
  }

  Type pick_type(const std::vector<Type> &formats) const
  {
    Type t = d_rng->pick_from_set<std::vector<Type>, Type>(formats);
    assert(t.is_fp());
    return t;
  }

  void test_for_float16(
      std::function<void(const BitVector &, const BitVector &)> fun);

  void test_for_formats(
      const std::vector<Type> &formats,
      uint64_t n_tests,
      std::function<void(const BitVector &, const BitVector &)> fun);

  void test_to_fp_from_real(RoundingMode rm,
                            std::vector<std::vector<const char *>> &expected);

  void test_to_fp_from_rational(
      RationalMode mode,
      RoundingMode rm,
      std::vector<std::vector<const char *>> &expected);

  NodeManager d_nm;
  fp::SymFpuNM snm;

  std::vector<const char *> d_constants_dec = {
      "00",
      "0.0",
      "0.000001",
      "0.0117749388721091",
      "0.01745240643728",
      "0.03489949670250",
      "0.05233595624294",
      "0.0544",
      "0.06975647374412",
      "0.06975647374413",
      "0.08715574274766",
      "0.10452846326765",
      "0.12186934340515",
      "0.13917310096007",
      "0.15643446504023",
      "0.17364817766693",
      "0.19080899537654",
      "0.2",
      "0.20791169081776",
      "0.22495105434386",
      "0.22495105434387",
      "0.24192189559967",
      "0.244",
      "0.25881904510252",
      "0.27563735581700",
      "0.29237170472274",
      "0.3",
      "0.30901699437495",
      "0.32556815445716",
      "0.34202014332567",
      "0.35836794954530",
      "0.37460659341591",
      "0.39073112848927",
      "0.4",
      "0.403",
      "0.40673664307580",
      "0.42261826174070",
      "0.4344376",
      "0.43837114678908",
      "0.45399049973955",
      "0.4677826",
      "0.46947156278589",
      "0.48480962024634",
      "0.5",
      "0.50000000000000",
      "0.51503807491005",
      "0.5179422053046",
      "0.52991926423320",
      "0.52991926423321",
      "0.54463903501503",
      "0.5522073405779",
      "0.55919290347075",
      "0.57357643635105",
      "0.58778525229247",
      "0.60181502315205",
      "0.61566147532566",
      "0.62932039104984",
      "0.64278760968654",
      "0.65605902899051",
      "0.66913060635886",
      "0.6740477",
      "0.68199836006250",
      "0.69465837045900",
      "0.7",
      "0.70710678118655",
      "0.71933980033865",
      "0.73135370161917",
      "0.74314482547739",
      "0.75470958022277",
      "0.76604444311898",
      "0.7700725",
      "0.77714596145697",
      "0.78801075360672",
      "0.79863551004729",
      "0.8",
      "0.80901699437495",
      "0.81915204428899",
      "0.820939679242",
      "0.82903757255504",
      "0.83867056794542",
      "0.84804809615643",
      "0.85716730070211",
      "0.86602540378444",
      "0.87461970713940",
      "0.88294759285893",
      "0.89100652418837",
      "0.89879404629917",
      "0.90630778703665",
      "0.91354545764260",
      "0.92050485345244",
      "0.92718385456679",
      "0.93358042649720",
      "0.93969262078591",
      "0.94551857559932",
      "0.95105651629515",
      "0.95630475596304",
      "0.96126169593832",
      "0.96592582628907",
      "0.97029572627600",
      "0.97437006478524",
      "0.97814760073381",
      "0.98",
      "0.98162718344766",
      "0.98480775301221",
      "0.98768834059514",
      "0.99026806874157",
      "0.99254615164132",
      "0.99452189536827",
      "0.99619469809175",
      "0.99756405025982",
      "0.99862953475457",
      "0.99939082701910",
      "0.99984769515639",
      "1.0",
      "1.00000000000000",
      "1.1",
      "1.3",
      "1.4",
      "1.470767736573",
      "1.5",
      "1.5419",
      "1.633101801841",
      "1.7",
      "1.742319554830",
      "10.0",
      "100.0",
      "10000.0",
      "1000000.0",
      "10000000000.0",
      "1000000000000000000000000000000.0",
      "100000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "0000000000000.0",
      "11.0",
      "111.0",
      "1130.0",
      "120.0",
      "121.0",
      "15.0",
      "16.0",
      "179000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000000000000000000000000000000000000000000000000000000"
      "000000000000000000000.0",
      "180.0",
      "2.0",
      "20.0",
      "24.0",
      "256.0",
      "3.0",
      "30.0",
      "3000.0",
      "33096.0",
      "33554432.0",
      "360.0",
      "5.0",
      "5040.0",
      "6.0",
      "7.0",
      "720.0",
      "77617.0",
      "8.0",
      "85.0",
      "9.0",
      "180",
      "2",
      "20",
      "24",
      "256",
      "3",
      "30",
      "3000",
      "33096",
      "33554432",
      "360",
      "5",
      "5040",
      "6",
      "7",
      "720",
      "77617",
      "8",
      "85",
      "9",
  };

  std::vector<std::pair<const char *, const char *>> d_constants_rat = {
      {"1", "1"},
      {"1", "10"},
      {"1", "1000000"},
      {"1", "10000000000"},
      {"1", "1000000000000000000000000000000"},
      {"1", "16"},
      {"1", "2"},
      {"1", "256"},
      {"1", "4"},
      {"1", "5"},
      {"1", "8"},
      {"1", "85070591730234615865843651857942052864"},
      {"10", "1"},
      {"1000", "1"},
      {"1001", "1000"},
      {"101", "100"},
      {"10300761498201", "20000000000000"},
      {"10416666977", "250000000000"},
      {"1041666721", "125000000000"},
      {"109", "100"},
      {"109077540233", "6250000000000"},
      {"10911973761", "16000000000"},
      {"1093474403", "50000000000"},
      {"10959278669727", "25000000000000"},
      {"11", "10"},
      {"11", "2"},
      {"111", "100"},
      {"11247552717193", "50000000000000"},
      {"11444091797", "25000000000000"},
      {"11471528727021", "20000000000000"},
      {"1152921504606847", "1152921504606846976"},
      {"117749388721091", "10000000000000000"},
      {"11863283", "8388608"},
      {"12", "1"},
      {"120", "1"},
      {"12015771199229", "12500000000000"},
      {"12036300463041", "20000000000000"},
      {"124007936447383647089", "5000000000000000000000000"},
      {"12400793821", "500000000000000"},
      {"129", "100"},
      {"12953652913", "500000000000000"},
      {"12993812561", "500000000000000"},
      {"1299448067611", "6250000000000"},
      {"131", "100"},
      {"1324798160583", "2500000000000"},
      {"13333334029", "100000000000"},
      {"1335", "4"},
      {"138888888885077966921", "50000000000000000000000"},
      {"138888888888741095749", "100000000000000000000000"},
      {"139", "100"},
      {"13917310096007", "100000000000000"},
      {"13959798681", "400000000000"},
      {"139843", "100000"},
      {"1399", "1000"},
      {"141", "100"},
      {"14142135623731", "20000000000000"},
      {"14386796006773", "20000000000000"},
      {"1442695040888963387", "1000000000000000000"},
      {"14618585236137", "50000000000000"},
      {"15419", "10000"},
      {"15635888849", "200000000000000"},
      {"15643446504023", "100000000000000"},
      {"15707962513", "10000000000"},
      {"15707962513", "20000000000"},
      {"157079632679", "100000000000"},
      {"1570796326794896619", "500000000000000000"},
      {"1571", "1000"},
      {"15896910177", "100000000000000000000"},
      {"16180339887499", "20000000000000"},
      {"16533902205465251539", "10000000000000000000000000"},
      {"166666666666666019037", "1000000000000000000000"},
      {"16666667163", "100000000000"},
      {"16777215", "67108864"},
      {"1725329017245637", "2251799813685248"},
      {"17364817766693", "100000000000000"},
      {"1743911843603", "25000000000000"},
      {"17851813027", "250000000000000"},
      {"18126155740733", "20000000000000"},
      {"1820261823", "1250000000000"},
      {"19021130325903", "20000000000000"},
      {"2", "1"},
      {"2", "5"},
      {"20000001", "100000000"},
      {"201", "128"},
      {"2033683215379", "5000000000000"},
      {"20875723212981748279", "10000000000000000000000000000"},
      {"2090569265353", "20000000000000"},
      {"21650635094611", "25000000000000"},
      {"2236771613883", "4000000000000"},
      {"22495105434387", "100000000000000"},
      {"22719295115576389653", "2000000000000000000000000000000"},
      {"229761391", "1000000000"},
      {"23012621336311", "25000000000000"},
      {"2333951066243", "2500000000000"},
      {"2338913", "5000000"},
      {"2357410267", "31250000000000000"},
      {"23637964389983", "25000000000000"},
      {"24", "1"},
      {"24192189559967", "100000000000000"},
      {"24240481012317", "50000000000000"},
      {"242573931569", "250000000000"},
      {"24359251619631", "25000000000000"},
      {"2437386868103", "20000000000000"},
      {"2462533605021", "3125000000000"},
      {"24646313977", "100000000000000"},
      {"2467767", "5000000"},
      {"24813653791033", "25000000000000"},
      {"25050759689", "1000000000000000000"},
      {"2616797812147", "50000000000000"},
      {"26922908347", "5000000000000000000000000"},
      {"2701068297", "250000000000000"},
      {"2701083531", "250000000000000"},
      {"27557314297", "10000000000000000"},
      {"27557314297", "100000000000000000"},
      {"275637355817", "1000000000000"},
      {"2797", "2000"},
      {"3", "10"},
      {"3", "2"},
      {"3", "33554432"},
      {"3", "4"},
      {"3", "5"},
      {"3", "50"},
      {"30000001", "100000000"},
      {"30783073766283", "50000000000000"},
      {"308029", "400000"},
      {"3141592741", "1000000000"},
      {"3141592741", "2000000000"},
      {"3141592741", "4000000000"},
      {"32139380484327", "50000000000000"},
      {"32756352257", "100000000000000000000000000000000"},
      {"333333333333", "1000000000000"},
      {"3333333333333333333333", "10000000000000000000000"},
      {"33333334327", "100000000000"},
      {"33456530317943", "50000000000000"},
      {"34202014332567", "100000000000000"},
      {"34961", "25000"},
      {"3583679495453", "10000000000000"},
      {"35920790397", "10000000000000"},
      {"362880", "1"},
      {"37256660955097055421", "50000000000000000"},
      {"37460659341591", "100000000000000"},
      {"37748947079", "1000000000000000000"},
      {"3798187459", "62500000000000000000"},
      {"38302222155949", "50000000000000"},
      {"39073112848927", "100000000000000"},
      {"3984778792367", "4000000000000"},
      {"4", "5"},
      {"40320", "1"},
      {"413813679705723846039", "10000000000000000000000000000"},
      {"416666666666666019037", "10000000000000000000000"},
      {"41933528397271", "50000000000000"},
      {"4226182617407", "10000000000000"},
      {"4357787137383", "50000000000000"},
      {"4373098535697", "5000000000000"},
      {"45000000000000000", "1"},
      {"4567727288213", "5000000000000"},
      {"4639659437", "250000000000000"},
      {"46947156278589", "100000000000000"},
      {"4722366482869645", "4722366482869645213696"},
      {"49081359172383", "50000000000000"},
      {"49384417029757", "50000000000000"},
      {"4951760157141521", "4951760157141521099596496896"},
      {"49878202512991", "50000000000000"},
      {"5", "128"},
      {"5", "2"},
      {"50000001", "100000000"},
      {"5040", "1"},
      {"5181484828469", "6250000000000"},
      {"51869421", "40000000"},
      {"5218930843", "2500000000000000000"},
      {"52991926423321", "100000000000000"},
      {"53968254477", "1000000000000"},
      {"543047", "1250000"},
      {"54463903501503", "100000000000000"},
      {"55114628702781326607", "200000000000000000000000000"},
      {"555555569", "400000000000"},
      {"56378512969", "10000000000000000000000000000"},
      {"5679823799", "500000000000000000000"},
      {"5764607523034235", "576460752303423488"},
      {"58778525229247", "100000000000000"},
      {"59479333", "500000000"},
      {"5976904724769", "6250000000000"},
      {"6", "1"},
      {"6", "5"},
      {"60", "1"},
      {"60026650317", "1000000000000000000000"},
      {"60770943833", "1000000000000000000000"},
      {"61232342629", "1000000000000000000000000000"},
      {"6180339887499", "20000000000000"},
      {"628314209", "400000000"},
      {"63331015649", "100000000000000000000000000000000000"},
      {"63661980629", "100000000000"},
      {"6470476127563", "25000000000000"},
      {"65605902899051", "100000000000000"},
      {"661375632143793436117", "10000000000000000000000000"},
      {"6740477", "10000000"},
      {"6743802672015265", "1125899906842624"},
      {"69", "100"},
      {"69314718036912381649", "100000000000000000000"},
      {"694658370459", "1000000000000"},
      {"6975647374413", "100000000000000"},
      {"699", "500"},
      {"7", "5"},
      {"707106769", "500000000"},
      {"71", "100"},
      {"720", "1"},
      {"73135370161917", "100000000000000"},
      {"7350515807", "12500000000000"},
      {"7378697629483821", "73786976294838206464"},
      {"73896444519", "100000000000000000000000"},
      {"74314482547739", "100000000000000"},
      {"7450580597", "250000000000000000"},
      {"75470958022277", "100000000000000"},
      {"75497894159", "1000000000000000000"},
      {"7737125245533627", "77371252455336267181195264"},
      {"77714596145697", "100000000000000"},
      {"7866504888123", "12500000000000"},
      {"79863551004729", "100000000000000"},
      {"8", "5"},
      {"8139203861429", "25000000000000"},
      {"81915204428899", "100000000000000"},
      {"83009228831", "1000000000000000000000000000000"},
      {"8388609", "8388608"},
      {"8479827738375907", "2251799813685248"},
      {"84804809615643", "100000000000000"},
      {"85716730070211", "100000000000000"},
      {"88294759285893", "100000000000000"},
      {"88632395491", "10000000000000"},
      {"88722839111672996637", "125000000000000000"},
      {"89100652418837", "100000000000000"},
      {"89879404629917", "100000000000000"},
      {"9", "10"},
      {"90109837", "100000000"},
      {"9079809994791", "20000000000000"},
      {"92718385456679", "100000000000000"},
      {"93326361850321887899",
       "10000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000"},
      {"93969262078591", "100000000000000"},
      {"9540449768827", "50000000000000"},
      {"95410746463529385001", "500000000000000000000000000000"},
      {"96592582628907", "100000000000000"},
      {"97814760073381", "100000000000000"},
      {"98480775301221", "100000000000000"},
      {"99", "100"},
      {"99026806874157", "100000000000000"},
      {"9920635057", "50000000000000"},
      {"99452189536827", "100000000000000"},
      {"99862953475457", "100000000000000"},
      {"999", "1000"},
      {"9993908270191", "10000000000000"},
      {"99984769515639", "100000000000000"},
  };

  std::vector<std::pair<const char *, const char *>> d_constants_rat_num_dec = {
      {"1.0", "1"},
      {"1.0", "10"},
      {"1.0", "1000000"},
      {"1.0", "10000000000"},
      {"1.0", "1000000000000000000000000000000"},
      {"1.0", "16"},
      {"1.0", "2"},
      {"1.0", "256"},
      {"1.0", "4"},
      {"1.0", "5"},
      {"1.0", "8"},
      {"1.0", "85070591730234615865843651857942052864"},
      {"10.0", "1"},
      {"1000.0", "1"},
      {"1001.0", "1000"},
      {"101.0", "100"},
      {"10300761498201.0", "20000000000000"},
      {"10416666977.0", "250000000000"},
      {"1041666721.0", "125000000000"},
      {"109.0", "100"},
      {"109077540233.0", "6250000000000"},
      {"10911973761.0", "16000000000"},
      {"1093474403.0", "50000000000"},
      {"10959278669727.0", "25000000000000"},
      {"11.0", "10"},
      {"11.0", "2"},
      {"111.0", "100"},
      {"11247552717193.0", "50000000000000"},
      {"11444091797.0", "25000000000000"},
      {"11471528727021.0", "20000000000000"},
      {"1152921504606847.0", "1152921504606846976"},
      {"117749388721091.0", "10000000000000000"},
      {"11863283.0", "8388608"},
      {"12.0", "1"},
      {"120.0", "1"},
      {"12015771199229.0", "12500000000000"},
      {"12036300463041.0", "20000000000000"},
      {"124007936447383647089.0", "5000000000000000000000000"},
      {"12400793821.0", "500000000000000"},
      {"129.0", "100"},
      {"12953652913.0", "500000000000000"},
      {"12993812561.0", "500000000000000"},
      {"1299448067611.0", "6250000000000"},
      {"131.0", "100"},
      {"1324798160583.0", "2500000000000"},
      {"13333334029.0", "100000000000"},
      {"1335.0", "4"},
      {"138888888885077966921.0", "50000000000000000000000"},
      {"138888888888741095749.0", "100000000000000000000000"},
      {"139.0", "100"},
      {"13917310096007.0", "100000000000000"},
      {"13959798681.0", "400000000000"},
      {"139843.0", "100000"},
      {"1399.0", "1000"},
      {"141.0", "100"},
      {"14142135623731.0", "20000000000000"},
      {"14386796006773.0", "20000000000000"},
      {"1442695040888963387.0", "1000000000000000000"},
      {"14618585236137.0", "50000000000000"},
      {"15419.0", "10000"},
      {"15635888849.0", "200000000000000"},
      {"15643446504023.0", "100000000000000"},
      {"15707962513.0", "10000000000"},
      {"15707962513.0", "20000000000"},
      {"157079632679.0", "100000000000"},
      {"1570796326794896619.0", "500000000000000000"},
      {"1571.0", "1000"},
      {"15896910177.0", "100000000000000000000"},
      {"16180339887499.0", "20000000000000"},
      {"16533902205465251539.0", "10000000000000000000000000"},
      {"166666666666666019037.0", "1000000000000000000000"},
      {"16666667163.0", "100000000000"},
      {"16777215.0", "67108864"},
      {"1725329017245637.0", "2251799813685248"},
      {"17364817766693.0", "100000000000000"},
      {"1743911843603.0", "25000000000000"},
      {"17851813027.0", "250000000000000"},
      {"18126155740733.0", "20000000000000"},
      {"1820261823.0", "1250000000000"},
      {"19021130325903.0", "20000000000000"},
      {"2.0", "1"},
      {"2.0", "5"},
      {"20000001.0", "100000000"},
      {"201.0", "128"},
      {"2033683215379.0", "5000000000000"},
      {"20875723212981748279.0", "10000000000000000000000000000"},
      {"2090569265353.0", "20000000000000"},
      {"21650635094611.0", "25000000000000"},
      {"2236771613883.0", "4000000000000"},
      {"22495105434387.0", "100000000000000"},
      {"22719295115576389653.0", "2000000000000000000000000000000"},
      {"229761391.0", "1000000000"},
      {"23012621336311.0", "25000000000000"},
      {"2333951066243.0", "2500000000000"},
      {"2338913.0", "5000000"},
      {"2357410267.0", "31250000000000000"},
      {"23637964389983.0", "25000000000000"},
      {"24.0", "1"},
      {"24192189559967.0", "100000000000000"},
      {"24240481012317.0", "50000000000000"},
      {"242573931569.0", "250000000000"},
      {"24359251619631.0", "25000000000000"},
      {"2437386868103.0", "20000000000000"},
      {"2462533605021.0", "3125000000000"},
      {"24646313977.0", "100000000000000"},
      {"2467767.0", "5000000"},
      {"24813653791033.0", "25000000000000"},
      {"25050759689.0", "1000000000000000000"},
      {"2616797812147.0", "50000000000000"},
      {"26922908347.0", "5000000000000000000000000"},
      {"2701068297.0", "250000000000000"},
      {"2701083531.0", "250000000000000"},
      {"27557314297.0", "10000000000000000"},
      {"27557314297.0", "100000000000000000"},
      {"275637355817.0", "1000000000000"},
      {"2797.0", "2000"},
      {"3.0", "10"},
      {"3.0", "2"},
      {"3.0", "33554432"},
      {"3.0", "4"},
      {"3.0", "5"},
      {"3.0", "50"},
      {"30000001.0", "100000000"},
      {"30783073766283.0", "50000000000000"},
      {"308029.0", "400000"},
      {"3141592741.0", "1000000000"},
      {"3141592741.0", "2000000000"},
      {"3141592741.0", "4000000000"},
      {"32139380484327.0", "50000000000000"},
      {"32756352257.0", "100000000000000000000000000000000"},
      {"333333333333.0", "1000000000000"},
      {"3333333333333333333333.0", "10000000000000000000000"},
      {"33333334327.0", "100000000000"},
      {"33456530317943.0", "50000000000000"},
      {"34202014332567.0", "100000000000000"},
      {"34961.0", "25000"},
      {"3583679495453.0", "10000000000000"},
      {"35920790397.0", "10000000000000"},
      {"362880.0", "1"},
      {"37256660955097055421.0", "50000000000000000"},
      {"37460659341591.0", "100000000000000"},
      {"37748947079.0", "1000000000000000000"},
      {"3798187459.0", "62500000000000000000"},
      {"38302222155949.0", "50000000000000"},
      {"39073112848927.0", "100000000000000"},
      {"3984778792367.0", "4000000000000"},
      {"4.0", "5"},
      {"40320.0", "1"},
      {"413813679705723846039.0", "10000000000000000000000000000"},
      {"416666666666666019037.0", "10000000000000000000000"},
      {"41933528397271.0", "50000000000000"},
      {"4226182617407.0", "10000000000000"},
      {"4357787137383.0", "50000000000000"},
      {"4373098535697.0", "5000000000000"},
      {"45000000000000000.0", "1"},
      {"4567727288213.0", "5000000000000"},
      {"4639659437.0", "250000000000000"},
      {"46947156278589.0", "100000000000000"},
      {"4722366482869645.0", "4722366482869645213696"},
      {"49081359172383.0", "50000000000000"},
      {"49384417029757.0", "50000000000000"},
      {"4951760157141521.0", "4951760157141521099596496896"},
      {"49878202512991.0", "50000000000000"},
      {"5.0", "128"},
      {"5.0", "2"},
      {"50000001.0", "100000000"},
      {"5040.0", "1"},
      {"5181484828469.0", "6250000000000"},
      {"51869421.0", "40000000"},
      {"5218930843.0", "2500000000000000000"},
      {"52991926423321.0", "100000000000000"},
      {"53968254477.0", "1000000000000"},
      {"543047.0", "1250000"},
      {"54463903501503.0", "100000000000000"},
      {"55114628702781326607.0", "200000000000000000000000000"},
      {"555555569.0", "400000000000"},
      {"56378512969.0", "10000000000000000000000000000"},
      {"5679823799.0", "500000000000000000000"},
      {"5764607523034235.0", "576460752303423488"},
      {"58778525229247.0", "100000000000000"},
      {"59479333.0", "500000000"},
      {"5976904724769.0", "6250000000000"},
      {"6.0", "1"},
      {"6.0", "5"},
      {"60.0", "1"},
      {"60026650317.0", "1000000000000000000000"},
      {"60770943833.0", "1000000000000000000000"},
      {"61232342629.0", "1000000000000000000000000000"},
      {"6180339887499.0", "20000000000000"},
      {"628314209.0", "400000000"},
      {"63331015649.0", "100000000000000000000000000000000000"},
      {"63661980629.0", "100000000000"},
      {"6470476127563.0", "25000000000000"},
      {"65605902899051.0", "100000000000000"},
      {"661375632143793436117.0", "10000000000000000000000000"},
      {"6740477.0", "10000000"},
      {"6743802672015265.0", "1125899906842624"},
      {"69.0", "100"},
      {"69314718036912381649.0", "100000000000000000000"},
      {"694658370459.0", "1000000000000"},
      {"6975647374413.0", "100000000000000"},
      {"699.0", "500"},
      {"7.0", "5"},
      {"707106769.0", "500000000"},
      {"71.0", "100"},
      {"720.0", "1"},
      {"73135370161917.0", "100000000000000"},
      {"7350515807.0", "12500000000000"},
      {"7378697629483821.0", "73786976294838206464"},
      {"73896444519.0", "100000000000000000000000"},
      {"74314482547739.0", "100000000000000"},
      {"7450580597.0", "250000000000000000"},
      {"75470958022277.0", "100000000000000"},
      {"75497894159.0", "1000000000000000000"},
      {"7737125245533627.0", "77371252455336267181195264"},
      {"77714596145697.0", "100000000000000"},
      {"7866504888123.0", "12500000000000"},
      {"79863551004729.0", "100000000000000"},
      {"8.0", "5"},
      {"8139203861429.0", "25000000000000"},
      {"81915204428899.0", "100000000000000"},
      {"83009228831.0", "1000000000000000000000000000000"},
      {"8388609.0", "8388608"},
      {"8479827738375907.0", "2251799813685248"},
      {"84804809615643.0", "100000000000000"},
      {"85716730070211.0", "100000000000000"},
      {"88294759285893.0", "100000000000000"},
      {"88632395491.0", "10000000000000"},
      {"88722839111672996637.0", "125000000000000000"},
      {"89100652418837.0", "100000000000000"},
      {"89879404629917.0", "100000000000000"},
      {"9.0", "10"},
      {"90109837.0", "100000000"},
      {"9079809994791.0", "20000000000000"},
      {"92718385456679.0", "100000000000000"},
      {"93326361850321887899",
       "10000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000"},
      {"93969262078591.0", "100000000000000"},
      {"9540449768827.0", "50000000000000"},
      {"95410746463529385001.0", "500000000000000000000000000000"},
      {"96592582628907.0", "100000000000000"},
      {"97814760073381.0", "100000000000000"},
      {"98480775301221.0", "100000000000000"},
      {"99.0", "100"},
      {"99026806874157.0", "100000000000000"},
      {"9920635057.0", "50000000000000"},
      {"99452189536827.0", "100000000000000"},
      {"99862953475457.0", "100000000000000"},
      {"999.0", "1000"},
      {"9993908270191.0", "10000000000000"},
      {"99984769515639.0", "100000000000000"},
  };

  std::vector<std::pair<const char *, const char *>> d_constants_rat_den_dec = {
      {"1", "1.0"},
      {"1", "10.0"},
      {"1", "1000000.0"},
      {"1", "10000000000.0"},
      {"1", "1000000000000000000000000000000.0"},
      {"1", "16.0"},
      {"1", "2.0"},
      {"1", "256.0"},
      {"1", "4.0"},
      {"1", "5.0"},
      {"1", "8.0"},
      {"1", "85070591730234615865843651857942052864.0"},
      {"10", "1.0"},
      {"1000", "1.0"},
      {"1001", "1000.0"},
      {"101", "100.0"},
      {"10300761498201", "20000000000000.0"},
      {"10416666977", "250000000000.0"},
      {"1041666721", "125000000000.0"},
      {"109", "100.0"},
      {"109077540233", "6250000000000.0"},
      {"10911973761", "16000000000.0"},
      {"1093474403", "50000000000.0"},
      {"10959278669727", "25000000000000.0"},
      {"11", "10.0"},
      {"11", "2.0"},
      {"111", "100.0"},
      {"11247552717193", "50000000000000.0"},
      {"11444091797", "25000000000000.0"},
      {"11471528727021", "20000000000000.0"},
      {"1152921504606847", "1152921504606846976.0"},
      {"117749388721091", "10000000000000000.0"},
      {"11863283", "8388608.0"},
      {"12", "1.0"},
      {"120", "1.0"},
      {"12015771199229", "12500000000000.0"},
      {"12036300463041", "20000000000000.0"},
      {"124007936447383647089", "5000000000000000000000000.0"},
      {"12400793821", "500000000000000.0"},
      {"129", "100.0"},
      {"12953652913", "500000000000000.0"},
      {"12993812561", "500000000000000.0"},
      {"1299448067611", "6250000000000.0"},
      {"131", "100.0"},
      {"1324798160583", "2500000000000.0"},
      {"13333334029", "100000000000.0"},
      {"1335", "4.0"},
      {"138888888885077966921", "50000000000000000000000.0"},
      {"138888888888741095749", "100000000000000000000000.0"},
      {"139", "100.0"},
      {"13917310096007", "100000000000000.0"},
      {"13959798681", "400000000000.0"},
      {"139843", "100000.0"},
      {"1399", "1000.0"},
      {"141", "100.0"},
      {"14142135623731", "20000000000000.0"},
      {"14386796006773", "20000000000000.0"},
      {"1442695040888963387", "1000000000000000000.0"},
      {"14618585236137", "50000000000000.0"},
      {"15419", "10000.0"},
      {"15635888849", "200000000000000.0"},
      {"15643446504023", "100000000000000.0"},
      {"15707962513", "10000000000.0"},
      {"15707962513", "20000000000.0"},
      {"157079632679", "100000000000.0"},
      {"1570796326794896619", "500000000000000000.0"},
      {"1571", "1000.0"},
      {"15896910177", "100000000000000000000.0"},
      {"16180339887499", "20000000000000.0"},
      {"16533902205465251539", "10000000000000000000000000.0"},
      {"166666666666666019037", "1000000000000000000000.0"},
      {"16666667163", "100000000000.0"},
      {"16777215", "67108864.0"},
      {"1725329017245637", "2251799813685248.0"},
      {"17364817766693", "100000000000000.0"},
      {"1743911843603", "25000000000000.0"},
      {"17851813027", "250000000000000.0"},
      {"18126155740733", "20000000000000.0"},
      {"1820261823", "1250000000000.0"},
      {"19021130325903", "20000000000000.0"},
      {"2", "1.0"},
      {"2", "5.0"},
      {"20000001", "100000000.0"},
      {"201", "128.0"},
      {"2033683215379", "5000000000000.0"},
      {"20875723212981748279", "10000000000000000000000000000.0"},
      {"2090569265353", "20000000000000.0"},
      {"21650635094611", "25000000000000.0"},
      {"2236771613883", "4000000000000.0"},
      {"22495105434387", "100000000000000.0"},
      {"22719295115576389653", "2000000000000000000000000000000.0"},
      {"229761391", "1000000000.0"},
      {"23012621336311", "25000000000000.0"},
      {"2333951066243", "2500000000000.0"},
      {"2338913", "5000000.0"},
      {"2357410267", "31250000000000000.0"},
      {"23637964389983", "25000000000000.0"},
      {"24", "1.0"},
      {"24192189559967", "100000000000000.0"},
      {"24240481012317", "50000000000000.0"},
      {"242573931569", "250000000000.0"},
      {"24359251619631", "25000000000000.0"},
      {"2437386868103", "20000000000000.0"},
      {"2462533605021", "3125000000000.0"},
      {"24646313977", "100000000000000.0"},
      {"2467767", "5000000.0"},
      {"24813653791033", "25000000000000.0"},
      {"25050759689", "1000000000000000000.0"},
      {"2616797812147", "50000000000000.0"},
      {"26922908347", "5000000000000000000000000.0"},
      {"2701068297", "250000000000000.0"},
      {"2701083531", "250000000000000.0"},
      {"27557314297", "10000000000000000.0"},
      {"27557314297", "100000000000000000.0"},
      {"275637355817", "1000000000000.0"},
      {"2797", "2000.0"},
      {"3", "10.0"},
      {"3", "2.0"},
      {"3", "33554432.0"},
      {"3", "4.0"},
      {"3", "5.0"},
      {"3", "50.0"},
      {"30000001", "100000000.0"},
      {"30783073766283", "50000000000000.0"},
      {"308029", "400000.0"},
      {"3141592741", "1000000000.0"},
      {"3141592741", "2000000000.0"},
      {"3141592741", "4000000000.0"},
      {"32139380484327", "50000000000000.0"},
      {"32756352257", "100000000000000000000000000000000.0"},
      {"333333333333", "1000000000000.0"},
      {"3333333333333333333333", "10000000000000000000000.0"},
      {"33333334327", "100000000000.0"},
      {"33456530317943", "50000000000000.0"},
      {"34202014332567", "100000000000000.0"},
      {"34961", "25000.0"},
      {"3583679495453", "10000000000000.0"},
      {"35920790397", "10000000000000.0"},
      {"362880", "1.0"},
      {"37256660955097055421", "50000000000000000.0"},
      {"37460659341591", "100000000000000.0"},
      {"37748947079", "1000000000000000000.0"},
      {"3798187459", "62500000000000000000.0"},
      {"38302222155949", "50000000000000.0"},
      {"39073112848927", "100000000000000.0"},
      {"3984778792367", "4000000000000.0"},
      {"4", "5.0"},
      {"40320", "1.0"},
      {"413813679705723846039", "10000000000000000000000000000.0"},
      {"416666666666666019037", "10000000000000000000000.0"},
      {"41933528397271", "50000000000000.0"},
      {"4226182617407", "10000000000000.0"},
      {"4357787137383", "50000000000000.0"},
      {"4373098535697", "5000000000000.0"},
      {"45000000000000000", "1.0"},
      {"4567727288213", "5000000000000.0"},
      {"4639659437", "250000000000000.0"},
      {"46947156278589", "100000000000000.0"},
      {"4722366482869645", "4722366482869645213696.0"},
      {"49081359172383", "50000000000000.0"},
      {"49384417029757", "50000000000000.0"},
      {"4951760157141521", "4951760157141521099596496896.0"},
      {"49878202512991", "50000000000000.0"},
      {"5", "128.0"},
      {"5", "2.0"},
      {"50000001", "100000000.0"},
      {"5040", "1.0"},
      {"5181484828469", "6250000000000.0"},
      {"51869421", "40000000.0"},
      {"5218930843", "2500000000000000000.0"},
      {"52991926423321", "100000000000000.0"},
      {"53968254477", "1000000000000.0"},
      {"543047", "1250000.0"},
      {"54463903501503", "100000000000000.0"},
      {"55114628702781326607", "200000000000000000000000000.0"},
      {"555555569", "400000000000.0"},
      {"56378512969", "10000000000000000000000000000.0"},
      {"5679823799", "500000000000000000000.0"},
      {"5764607523034235", "576460752303423488.0"},
      {"58778525229247", "100000000000000.0"},
      {"59479333", "500000000.0"},
      {"5976904724769", "6250000000000.0"},
      {"6", "1.0"},
      {"6", "5.0"},
      {"60", "1.0"},
      {"60026650317", "1000000000000000000000.0"},
      {"60770943833", "1000000000000000000000.0"},
      {"61232342629", "1000000000000000000000000000.0"},
      {"6180339887499", "20000000000000.0"},
      {"628314209", "400000000.0"},
      {"63331015649", "100000000000000000000000000000000000.0"},
      {"63661980629", "100000000000.0"},
      {"6470476127563", "25000000000000.0"},
      {"65605902899051", "100000000000000.0"},
      {"661375632143793436117", "10000000000000000000000000.0"},
      {"6740477", "10000000.0"},
      {"6743802672015265", "1125899906842624.0"},
      {"69", "100.0"},
      {"69314718036912381649", "100000000000000000000.0"},
      {"694658370459", "1000000000000.0"},
      {"6975647374413", "100000000000000.0"},
      {"699", "500.0"},
      {"7", "5.0"},
      {"707106769", "500000000.0"},
      {"71", "100.0"},
      {"720", "1.0"},
      {"73135370161917", "100000000000000.0"},
      {"7350515807", "12500000000000.0"},
      {"7378697629483821", "73786976294838206464.0"},
      {"73896444519", "100000000000000000000000.0"},
      {"74314482547739", "100000000000000.0"},
      {"7450580597", "250000000000000000.0"},
      {"75470958022277", "100000000000000.0"},
      {"75497894159", "1000000000000000000.0"},
      {"7737125245533627", "77371252455336267181195264.0"},
      {"77714596145697", "100000000000000.0"},
      {"7866504888123", "12500000000000.0"},
      {"79863551004729", "100000000000000.0"},
      {"8", "5.0"},
      {"8139203861429", "25000000000000.0"},
      {"81915204428899", "100000000000000.0"},
      {"83009228831", "1000000000000000000000000000000.0"},
      {"8388609", "8388608.0"},
      {"8479827738375907", "2251799813685248.0"},
      {"84804809615643", "100000000000000.0"},
      {"85716730070211", "100000000000000.0"},
      {"88294759285893", "100000000000000.0"},
      {"88632395491", "10000000000000.0"},
      {"88722839111672996637", "125000000000000000.0"},
      {"89100652418837", "100000000000000.0"},
      {"89879404629917", "100000000000000.0"},
      {"9", "10.0"},
      {"90109837", "100000000.0"},
      {"9079809994791", "20000000000000.0"},
      {"92718385456679", "100000000000000.0"},
      {"93326361850321887899",
       "10000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000"},
      {"93969262078591", "100000000000000.0"},
      {"9540449768827", "50000000000000.0"},
      {"95410746463529385001", "500000000000000000000000000000.0"},
      {"96592582628907", "100000000000000.0"},
      {"97814760073381", "100000000000000.0"},
      {"98480775301221", "100000000000000.0"},
      {"99", "100.0"},
      {"99026806874157", "100000000000000.0"},
      {"9920635057", "50000000000000.0"},
      {"99452189536827", "100000000000000.0"},
      {"99862953475457", "100000000000000.0"},
      {"999", "1000.0"},
      {"9993908270191", "10000000000000.0"},
      {"99984769515639", "100000000000000.0"},
  };

  std::vector<std::pair<const char *, const char *>> d_constants_rat_dec = {
      {"1.0", "1.0"},
      {"1.0", "10.0"},
      {"1.0", "1000000.0"},
      {"1.0", "10000000000.0"},
      {"1.0", "1000000000000000000000000000000.0"},
      {"1.0", "16.0"},
      {"1.0", "2.0"},
      {"1.0", "256.0"},
      {"1.0", "4.0"},
      {"1.0", "5.0"},
      {"1.0", "8.0"},
      {"1.0", "85070591730234615865843651857942052864.0"},
      {"10.0", "1.0"},
      {"1000.0", "1.0"},
      {"1001.0", "1000.0"},
      {"101.0", "100.0"},
      {"10300761498201.0", "20000000000000.0"},
      {"10416666977.0", "250000000000.0"},
      {"1041666721.0", "125000000000.0"},
      {"109.0", "100.0"},
      {"109077540233.0", "6250000000000.0"},
      {"10911973761.0", "16000000000.0"},
      {"1093474403.0", "50000000000.0"},
      {"10959278669727.0", "25000000000000.0"},
      {"11.0", "10.0"},
      {"11.0", "2.0"},
      {"111.0", "100.0"},
      {"11247552717193.0", "50000000000000.0"},
      {"11444091797.0", "25000000000000.0"},
      {"11471528727021.0", "20000000000000.0"},
      {"1152921504606847.0", "1152921504606846976.0"},
      {"117749388721091.0", "10000000000000000.0"},
      {"11863283.0", "8388608.0"},
      {"12.0", "1.0"},
      {"120.0", "1.0"},
      {"12015771199229.0", "12500000000000.0"},
      {"12036300463041.0", "20000000000000.0"},
      {"124007936447383647089.0", "5000000000000000000000000.0"},
      {"12400793821.0", "500000000000000.0"},
      {"129.0", "100.0"},
      {"12953652913.0", "500000000000000.0"},
      {"12993812561.0", "500000000000000.0"},
      {"1299448067611.0", "6250000000000.0"},
      {"131.0", "100.0"},
      {"1324798160583.0", "2500000000000.0"},
      {"13333334029.0", "100000000000.0"},
      {"1335.0", "4.0"},
      {"138888888885077966921.0", "50000000000000000000000.0"},
      {"138888888888741095749.0", "100000000000000000000000.0"},
      {"139.0", "100.0"},
      {"13917310096007.0", "100000000000000.0"},
      {"13959798681.0", "400000000000.0"},
      {"139843.0", "100000.0"},
      {"1399.0", "1000.0"},
      {"141.0", "100.0"},
      {"14142135623731.0", "20000000000000.0"},
      {"14386796006773.0", "20000000000000.0"},
      {"1442695040888963387.0", "1000000000000000000.0"},
      {"14618585236137.0", "50000000000000.0"},
      {"15419.0", "10000.0"},
      {"15635888849.0", "200000000000000.0"},
      {"15643446504023.0", "100000000000000.0"},
      {"15707962513.0", "10000000000.0"},
      {"15707962513.0", "20000000000.0"},
      {"157079632679.0", "100000000000.0"},
      {"1570796326794896619.0", "500000000000000000.0"},
      {"1571.0", "1000.0"},
      {"15896910177.0", "100000000000000000000.0"},
      {"16180339887499.0", "20000000000000.0"},
      {"16533902205465251539.0", "10000000000000000000000000.0"},
      {"166666666666666019037.0", "1000000000000000000000.0"},
      {"16666667163.0", "100000000000.0"},
      {"16777215.0", "67108864.0"},
      {"1725329017245637.0", "2251799813685248.0"},
      {"17364817766693.0", "100000000000000.0"},
      {"1743911843603.0", "25000000000000.0"},
      {"17851813027.0", "250000000000000.0"},
      {"18126155740733.0", "20000000000000.0"},
      {"1820261823.0", "1250000000000.0"},
      {"19021130325903.0", "20000000000000.0"},
      {"2.0", "1.0"},
      {"2.0", "5.0"},
      {"20000001.0", "100000000.0"},
      {"201.0", "128.0"},
      {"2033683215379.0", "5000000000000.0"},
      {"20875723212981748279.0", "10000000000000000000000000000.0"},
      {"2090569265353.0", "20000000000000.0"},
      {"21650635094611.0", "25000000000000.0"},
      {"2236771613883.0", "4000000000000.0"},
      {"22495105434387.0", "100000000000000.0"},
      {"22719295115576389653.0", "2000000000000000000000000000000.0"},
      {"229761391.0", "1000000000.0"},
      {"23012621336311.0", "25000000000000.0"},
      {"2333951066243.0", "2500000000000.0"},
      {"2338913.0", "5000000.0"},
      {"2357410267.0", "31250000000000000.0"},
      {"23637964389983.0", "25000000000000.0"},
      {"24.0", "1.0"},
      {"24192189559967.0", "100000000000000.0"},
      {"24240481012317.0", "50000000000000.0"},
      {"242573931569.0", "250000000000.0"},
      {"24359251619631.0", "25000000000000.0"},
      {"2437386868103.0", "20000000000000.0"},
      {"2462533605021.0", "3125000000000.0"},
      {"24646313977.0", "100000000000000.0"},
      {"2467767.0", "5000000.0"},
      {"24813653791033.0", "25000000000000.0"},
      {"25050759689.0", "1000000000000000000.0"},
      {"2616797812147.0", "50000000000000.0"},
      {"26922908347.0", "5000000000000000000000000.0"},
      {"2701068297.0", "250000000000000.0"},
      {"2701083531.0", "250000000000000.0"},
      {"27557314297.0", "10000000000000000.0"},
      {"27557314297.0", "100000000000000000.0"},
      {"275637355817.0", "1000000000000.0"},
      {"2797.0", "2000.0"},
      {"3.0", "10.0"},
      {"3.0", "2.0"},
      {"3.0", "33554432.0"},
      {"3.0", "4.0"},
      {"3.0", "5.0"},
      {"3.0", "50.0"},
      {"30000001.0", "100000000.0"},
      {"30783073766283.0", "50000000000000.0"},
      {"308029.0", "400000.0"},
      {"3141592741.0", "1000000000.0"},
      {"3141592741.0", "2000000000.0"},
      {"3141592741.0", "4000000000.0"},
      {"32139380484327.0", "50000000000000.0"},
      {"32756352257.0", "100000000000000000000000000000000.0"},
      {"333333333333.0", "1000000000000.0"},
      {"3333333333333333333333.0", "10000000000000000000000.0"},
      {"33333334327.0", "100000000000.0"},
      {"33456530317943.0", "50000000000000.0"},
      {"34202014332567.0", "100000000000000.0"},
      {"34961.0", "25000.0"},
      {"3583679495453.0", "10000000000000.0"},
      {"35920790397.0", "10000000000000.0"},
      {"362880.0", "1.0"},
      {"37256660955097055421.0", "50000000000000000.0"},
      {"37460659341591.0", "100000000000000.0"},
      {"37748947079.0", "1000000000000000000.0"},
      {"3798187459.0", "62500000000000000000.0"},
      {"38302222155949.0", "50000000000000.0"},
      {"39073112848927.0", "100000000000000.0"},
      {"3984778792367.0", "4000000000000.0"},
      {"4.0", "5.0"},
      {"40320.0", "1.0"},
      {"413813679705723846039.0", "10000000000000000000000000000.0"},
      {"416666666666666019037.0", "10000000000000000000000.0"},
      {"41933528397271.0", "50000000000000.0"},
      {"4226182617407.0", "10000000000000.0"},
      {"4357787137383.0", "50000000000000.0"},
      {"4373098535697.0", "5000000000000.0"},
      {"45000000000000000.0", "1.0"},
      {"4567727288213.0", "5000000000000.0"},
      {"4639659437.0", "250000000000000.0"},
      {"46947156278589.0", "100000000000000.0"},
      {"4722366482869645.0", "4722366482869645213696.0"},
      {"49081359172383.0", "50000000000000.0"},
      {"49384417029757.0", "50000000000000.0"},
      {"4951760157141521.0", "4951760157141521099596496896.0"},
      {"49878202512991.0", "50000000000000.0"},
      {"5.0", "128.0"},
      {"5.0", "2.0"},
      {"50000001.0", "100000000.0"},
      {"5040.0", "1.0"},
      {"5181484828469.0", "6250000000000.0"},
      {"51869421.0", "40000000.0"},
      {"5218930843.0", "2500000000000000000.0"},
      {"52991926423321.0", "100000000000000.0"},
      {"53968254477.0", "1000000000000.0"},
      {"543047.0", "1250000.0"},
      {"54463903501503.0", "100000000000000.0"},
      {"55114628702781326607.0", "200000000000000000000000000.0"},
      {"555555569.0", "400000000000.0"},
      {"56378512969.0", "10000000000000000000000000000.0"},
      {"5679823799.0", "500000000000000000000.0"},
      {"5764607523034235.0", "576460752303423488.0"},
      {"58778525229247.0", "100000000000000.0"},
      {"59479333.0", "500000000.0"},
      {"5976904724769.0", "6250000000000.0"},
      {"6.0", "1.0"},
      {"6.0", "5.0"},
      {"60.0", "1.0"},
      {"60026650317.0", "1000000000000000000000.0"},
      {"60770943833.0", "1000000000000000000000.0"},
      {"61232342629.0", "1000000000000000000000000000.0"},
      {"6180339887499.0", "20000000000000.0"},
      {"628314209.0", "400000000.0"},
      {"63331015649.0", "100000000000000000000000000000000000.0"},
      {"63661980629.0", "100000000000.0"},
      {"6470476127563.0", "25000000000000.0"},
      {"65605902899051.0", "100000000000000.0"},
      {"661375632143793436117.0", "10000000000000000000000000.0"},
      {"6740477.0", "10000000.0"},
      {"6743802672015265.0", "1125899906842624.0"},
      {"69.0", "100.0"},
      {"69314718036912381649.0", "100000000000000000000.0"},
      {"694658370459.0", "1000000000000.0"},
      {"6975647374413.0", "100000000000000.0"},
      {"699.0", "500.0"},
      {"7.0", "5.0"},
      {"707106769.0", "500000000.0"},
      {"71.0", "100.0"},
      {"720.0", "1.0"},
      {"73135370161917.0", "100000000000000.0"},
      {"7350515807.0", "12500000000000.0"},
      {"7378697629483821.0", "73786976294838206464.0"},
      {"73896444519.0", "100000000000000000000000.0"},
      {"74314482547739.0", "100000000000000.0"},
      {"7450580597.0", "250000000000000000.0"},
      {"75470958022277.0", "100000000000000.0"},
      {"75497894159.0", "1000000000000000000.0"},
      {"7737125245533627.0", "77371252455336267181195264.0"},
      {"77714596145697.0", "100000000000000.0"},
      {"7866504888123.0", "12500000000000.0"},
      {"79863551004729.0", "100000000000000.0"},
      {"8.0", "5.0"},
      {"8139203861429.0", "25000000000000.0"},
      {"81915204428899.0", "100000000000000.0"},
      {"83009228831.0", "1000000000000000000000000000000.0"},
      {"8388609.0", "8388608.0"},
      {"8479827738375907.0", "2251799813685248.0"},
      {"84804809615643.0", "100000000000000.0"},
      {"85716730070211.0", "100000000000000.0"},
      {"88294759285893.0", "100000000000000.0"},
      {"88632395491.0", "10000000000000.0"},
      {"88722839111672996637.0", "125000000000000000.0"},
      {"89100652418837.0", "100000000000000.0"},
      {"89879404629917.0", "100000000000000.0"},
      {"9.0", "10.0"},
      {"90109837.0", "100000000.0"},
      {"9079809994791.0", "20000000000000.0"},
      {"92718385456679.0", "100000000000000.0"},
      {"93326361850321887899.0",
       "10000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000000000000000000000000000000000000"
       "00000000000000000000000000000000000000.0"},
      {"93969262078591.0", "100000000000000.0"},
      {"9540449768827.0", "50000000000000.0"},
      {"95410746463529385001.0", "500000000000000000000000000000.0"},
      {"96592582628907.0", "100000000000000.0"},
      {"97814760073381.0", "100000000000000.0"},
      {"98480775301221.0", "100000000000000.0"},
      {"99.0", "100.0"},
      {"99026806874157.0", "100000000000000.0"},
      {"9920635057.0", "50000000000000.0"},
      {"99452189536827.0", "100000000000000.0"},
      {"99862953475457.0", "100000000000000.0"},
      {"999.0", "1000.0"},
      {"9993908270191.0", "10000000000000.0"},
      {"99984769515639.0", "100000000000000.0"},
  };

  std::unique_ptr<RNG> d_rng;

  Type d_fp16;
  Type d_fp32;
  Type d_fp64;
  Type d_fp128;

  std::vector<Type> d_all_formats;
  std::vector<Type> d_formats_32_128;
  std::vector<RoundingMode> d_all_rms;
};

/* -------------------------------------------------------------------------- */

void
TestFp::test_for_float16(
    std::function<void(const BitVector &bvexp, const BitVector &bvsig)> fun)
{
  for (uint64_t i = 0; i < (1u << 5); ++i)
  {
    for (uint64_t j = 0; j < (1u << 10); ++j)
    {
      BitVector bvexp = BitVector::from_ui(5, i);
      BitVector bvsig = BitVector::from_ui(10, j);
      fun(bvexp, bvsig);
    }
  }
}

void
TestFp::test_for_formats(
    const std::vector<Type> &formats,
    uint64_t n_tests,
    std::function<void(const BitVector &, const BitVector &)> fun)
{
  for (const auto &type : formats)
  {
    uint64_t exp_size = type.fp_exp_size();
    uint64_t sig_size = type.fp_sig_size() - 1;
    for (uint32_t i = 0; i < n_tests; ++i)
    {
      BitVector bvexp, bvsig;
      if (d_rng->flip_coin())
      {
        // normals
        bvexp = BitVector(exp_size,
                          *d_rng,
                          BitVector::mk_one(exp_size),
                          BitVector::mk_ones(exp_size).ibvdec());
        bvsig = BitVector(sig_size, *d_rng);
      }
      else
      {
        if (d_rng->pick_with_prob(600))
        {
          // zero exponent
          bvexp = BitVector::mk_zero(exp_size);
          bvsig = BitVector(sig_size, *d_rng);
        }
        else
        {
          // ones exponent
          bvexp = BitVector::mk_ones(exp_size);
          if (d_rng->pick_with_prob(100))
          {
            // inf
            bvsig = BitVector::mk_zero(sig_size);
          }
          else
          {
            // nan
            bvsig = BitVector(sig_size, *d_rng);
          }
        }
      }
      fun(bvexp, bvsig);
    }
  }
}

void
TestFp::test_to_fp_from_real(RoundingMode rm,
                             std::vector<std::vector<const char *>> &expected)
{
  assert(d_constants_dec.size() == expected.size());
  for (size_t i = 0, n = d_constants_dec.size(); i < n; ++i)
  {
    FloatingPoint fp =
        FloatingPoint::from_real(d_nm, d_fp16, rm, d_constants_dec[i]);
    BitVector sign, exp, sig;
    FloatingPoint::ieee_bv_as_bvs(d_fp16, fp.as_bv(), sign, exp, sig);
    ASSERT_EQ(sign.str(), expected[i][0]);
    ASSERT_EQ(exp.str(), expected[i][1]);
    ASSERT_EQ(sig.str(), expected[i][2]);

    FloatingPointMPFR fp_mpfr =
        FloatingPointMPFR::from_real(d_nm, d_fp16, rm, d_constants_dec[i]);
    FloatingPoint::ieee_bv_as_bvs(d_fp16, fp.as_bv(), sign, exp, sig);
    ASSERT_EQ(sign.str(), expected[i][0]);
    ASSERT_EQ(exp.str(), expected[i][1]);
    ASSERT_EQ(sig.str(), expected[i][2]);
  }
}

void
TestFp::test_to_fp_from_rational(
    RationalMode mode,
    RoundingMode rm,
    std::vector<std::vector<const char *>> &expected)
{
  std::vector<std::pair<const char *, const char *>> &constants =
      d_constants_rat;

  if (mode == NUM_DEC)
  {
    constants = d_constants_rat_num_dec;
  }
  else if (mode == DEN_DEC)
  {
    constants = d_constants_rat_den_dec;
  }
  else if (mode == DEC)
  {
    constants = d_constants_rat_dec;
  }

  assert(constants.size() == expected.size());
  for (size_t i = 0, n = constants.size(); i < n; ++i)
  {
    FloatingPoint fp = FloatingPoint::from_rational(
        d_nm, d_fp16, rm, constants[i].first, constants[i].second);
    BitVector sign, exp, sig;
    FloatingPoint::ieee_bv_as_bvs(d_fp16, fp.as_bv(), sign, exp, sig);
    ASSERT_EQ(sign.str(), expected[i][0]);
    ASSERT_EQ(exp.str(), expected[i][1]);
    ASSERT_EQ(sig.str(), expected[i][2]);

    FloatingPointMPFR fp_mpfr = FloatingPointMPFR::from_rational(
        d_nm, d_fp16, rm, constants[i].first, constants[i].second);
    FloatingPoint::ieee_bv_as_bvs(d_fp16, fp.as_bv(), sign, exp, sig);
    ASSERT_EQ(sign.str(), expected[i][0]);
    ASSERT_EQ(exp.str(), expected[i][1]);
    ASSERT_EQ(sig.str(), expected[i][2]);
  }
}

/* -------------------------------------------------------------------------- */

TEST_F(TestFp, isX)
{
  for (uint64_t i = 0; i < (1u << 5); ++i)
  {
    BitVector bvexp = BitVector::from_ui(5, i);
    bool exp_iszero = bvexp.is_zero();
    bool exp_isones = bvexp.is_ones();
    for (uint64_t j = 0; j < (1u << 10); ++j)
    {
      BitVector bvsig = BitVector::from_ui(10, j);
      FloatingPoint fp_pos(
          d_fp16, BitVector::mk_false().ibvconcat(bvexp).ibvconcat(bvsig));
      FloatingPoint fp_neg(
          d_fp16, BitVector::mk_false().ibvconcat(bvexp).ibvconcat(bvsig));
      FloatingPointMPFR fp_mpfr_pos(
          d_fp16, BitVector::mk_false().ibvconcat(bvexp).ibvconcat(bvsig));
      FloatingPointMPFR fp_mpfr_neg(
          d_fp16, BitVector::mk_true().ibvconcat(bvexp).ibvconcat(bvsig));
      if (!exp_iszero)
      {
        if (!exp_isones)
        {
          ASSERT_TRUE(fp_pos.fpisnormal());
          ASSERT_TRUE(fp_neg.fpisnormal());

          ASSERT_FALSE(fp_pos.fpissubnormal());
          ASSERT_FALSE(fp_neg.fpissubnormal());

          ASSERT_FALSE(fp_pos.fpisinf());
          ASSERT_FALSE(fp_neg.fpisinf());

          ASSERT_FALSE(fp_pos.fpisnan());
          ASSERT_FALSE(fp_neg.fpisnan());

          ASSERT_FALSE(fp_pos.fpiszero());
          ASSERT_FALSE(fp_neg.fpiszero());

          ASSERT_TRUE(fp_mpfr_pos.fpisnormal());
          ASSERT_TRUE(fp_mpfr_neg.fpisnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpissubnormal());
          ASSERT_FALSE(fp_mpfr_neg.fpissubnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpisinf());
          ASSERT_FALSE(fp_mpfr_neg.fpisinf());

          ASSERT_FALSE(fp_mpfr_pos.fpisnan());
          ASSERT_FALSE(fp_mpfr_neg.fpisnan());

          ASSERT_FALSE(fp_mpfr_pos.fpiszero());
          ASSERT_FALSE(fp_mpfr_neg.fpiszero());
        }
        else
        {
          if (bvsig.is_zero())
          {
            ASSERT_TRUE(fp_pos.fpisinf());
            ASSERT_TRUE(fp_neg.fpisinf());

            ASSERT_FALSE(fp_pos.fpisnan());
            ASSERT_FALSE(fp_neg.fpisnan());

            ASSERT_FALSE(fp_pos.fpisnormal());
            ASSERT_FALSE(fp_neg.fpisnormal());

            ASSERT_FALSE(fp_pos.fpissubnormal());
            ASSERT_FALSE(fp_neg.fpissubnormal());

            ASSERT_FALSE(fp_pos.fpiszero());
            ASSERT_FALSE(fp_neg.fpiszero());

            ASSERT_TRUE(fp_mpfr_pos.fpisinf());
            ASSERT_TRUE(fp_mpfr_neg.fpisinf());

            ASSERT_FALSE(fp_mpfr_pos.fpisnan());
            ASSERT_FALSE(fp_mpfr_neg.fpisnan());

            ASSERT_FALSE(fp_mpfr_pos.fpisnormal());
            ASSERT_FALSE(fp_mpfr_neg.fpisnormal());

            ASSERT_FALSE(fp_mpfr_pos.fpissubnormal());
            ASSERT_FALSE(fp_mpfr_neg.fpissubnormal());

            ASSERT_FALSE(fp_mpfr_pos.fpiszero());
            ASSERT_FALSE(fp_mpfr_neg.fpiszero());
          }
          else
          {
            ASSERT_TRUE(fp_pos.fpisnan());
            ASSERT_TRUE(fp_neg.fpisnan());

            ASSERT_FALSE(fp_pos.fpisinf());
            ASSERT_FALSE(fp_neg.fpisinf());

            ASSERT_FALSE(fp_pos.fpisnormal());
            ASSERT_FALSE(fp_neg.fpisnormal());

            ASSERT_FALSE(fp_pos.fpissubnormal());
            ASSERT_FALSE(fp_neg.fpissubnormal());

            ASSERT_FALSE(fp_pos.fpiszero());
            ASSERT_FALSE(fp_neg.fpiszero());

            ASSERT_TRUE(fp_mpfr_pos.fpisnan());
            ASSERT_TRUE(fp_mpfr_neg.fpisnan());

            ASSERT_FALSE(fp_mpfr_pos.fpisinf());
            ASSERT_FALSE(fp_mpfr_neg.fpisinf());

            ASSERT_FALSE(fp_mpfr_pos.fpisnormal());
            ASSERT_FALSE(fp_mpfr_neg.fpisnormal());

            ASSERT_FALSE(fp_mpfr_pos.fpissubnormal());
            ASSERT_FALSE(fp_mpfr_neg.fpissubnormal());

            ASSERT_FALSE(fp_mpfr_pos.fpiszero());
            ASSERT_FALSE(fp_mpfr_neg.fpiszero());
          }
        }
      }
      else
      {
        if (bvsig.is_zero())
        {
          ASSERT_TRUE(fp_pos.fpiszero());
          ASSERT_TRUE(fp_neg.fpiszero());

          ASSERT_FALSE(fp_pos.fpisnormal());
          ASSERT_FALSE(fp_neg.fpisnormal());

          ASSERT_FALSE(fp_pos.fpissubnormal());
          ASSERT_FALSE(fp_neg.fpissubnormal());

          ASSERT_FALSE(fp_pos.fpisinf());
          ASSERT_FALSE(fp_neg.fpisinf());

          ASSERT_FALSE(fp_pos.fpisnan());
          ASSERT_FALSE(fp_neg.fpisnan());

          ASSERT_TRUE(fp_mpfr_pos.fpiszero());
          ASSERT_TRUE(fp_mpfr_neg.fpiszero());

          ASSERT_FALSE(fp_mpfr_pos.fpisnormal());
          ASSERT_FALSE(fp_mpfr_neg.fpisnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpissubnormal());
          ASSERT_FALSE(fp_mpfr_neg.fpissubnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpisinf());
          ASSERT_FALSE(fp_mpfr_neg.fpisinf());

          ASSERT_FALSE(fp_mpfr_pos.fpisnan());
          ASSERT_FALSE(fp_mpfr_neg.fpisnan());
        }
        else
        {
          ASSERT_TRUE(fp_pos.fpissubnormal());
          ASSERT_TRUE(fp_neg.fpissubnormal());

          ASSERT_FALSE(fp_pos.fpisnormal());
          ASSERT_FALSE(fp_neg.fpisnormal());

          ASSERT_FALSE(fp_pos.fpisinf());
          ASSERT_FALSE(fp_neg.fpisinf());

          ASSERT_FALSE(fp_pos.fpisnan());
          ASSERT_FALSE(fp_neg.fpisnan());

          ASSERT_FALSE(fp_pos.fpiszero());
          ASSERT_FALSE(fp_neg.fpiszero());

          ASSERT_TRUE(fp_mpfr_pos.fpissubnormal());
          ASSERT_TRUE(fp_mpfr_neg.fpissubnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpisnormal());
          ASSERT_FALSE(fp_mpfr_neg.fpisnormal());

          ASSERT_FALSE(fp_mpfr_pos.fpisinf());
          ASSERT_FALSE(fp_mpfr_neg.fpisinf());

          ASSERT_FALSE(fp_mpfr_pos.fpisnan());
          ASSERT_FALSE(fp_mpfr_neg.fpisnan());

          ASSERT_FALSE(fp_mpfr_pos.fpiszero());
          ASSERT_FALSE(fp_mpfr_neg.fpiszero());
        }
      }
    }
  }
}

TEST_F(TestFp, str_as_bv)
{
  auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {
    uint64_t exp_size = bvexp.size();
    uint64_t sig_size = bvsig.size() + 1;

    Type type_sign = d_nm.mk_bv_type(1);
    Type type_exp  = d_nm.mk_bv_type(exp_size);
    Type type_sig  = d_nm.mk_bv_type(sig_size - 1);
    Type type_fp   = d_nm.mk_fp_type(exp_size, sig_size);

    for (const auto &bv :
         {BitVector::mk_false().bvconcat(bvexp).ibvconcat(bvsig),
          BitVector::mk_true().bvconcat(bvexp).ibvconcat(bvsig)})
    {
      BitVector bvsign =
          bv.msb() ? BitVector::mk_true() : BitVector::mk_false();
      // test constructor and str()
      FloatingPoint fp(type_fp, bv);
      FloatingPointMPFR fp_mpfr(type_fp, bv);
      if (fp.fpisnan())
      {
        ASSERT_TRUE(fp == FloatingPoint::fpnan(type_fp));
        std::string str = "(fp #b" + BitVector::mk_false().str() + " #b"
                          + BitVector::mk_ones(exp_size).str() + " #b"
                          + BitVector::mk_min_signed(sig_size - 1).str() + ")";
        ASSERT_EQ(fp.str(), str);
        // ASSERT_TRUE(fp_mpfr == FloatingPointMPFR::fpnan(type_fp));
        ASSERT_EQ(fp_mpfr.str(), str);
      }
      else
      {
        std::string str = "(fp #b" + bvsign.str() + " #b" + bvexp.str() + " #b"
                          + bvsig.str() + ")";
        ASSERT_EQ(fp.str(), str);
        ASSERT_EQ(fp.str(), str);
      }
      if (fp.str() != fp_mpfr.str())
      {
        std::cout << "bv: " << bv << std::endl;
        std::cout << "fp: " << fp << std::endl;
        std::cout << "fp_mpfr: " << fp_mpfr << std::endl;
      }
      assert(fp.str() == fp_mpfr.str());
      ASSERT_EQ(fp.str(), fp_mpfr.str());

      // test as_bv() via fpfp() and Node
      FloatingPoint fpfp = FloatingPoint::fpfp(
          d_nm,
          bv.msb() ? BitVector::mk_true() : BitVector::mk_false(),
          bvexp,
          bvsig);
      ASSERT_EQ(fp.str(), fpfp.str());
      Node node_fp    = d_nm.mk_value(fpfp);
      fpfp            = node_fp.value<FloatingPoint>();
      BitVector as_bv = fpfp.as_bv();
      BitVector as_bvsign, as_bvexp, as_bvsig;
      FloatingPoint::ieee_bv_as_bvs(
          type_fp, as_bv, as_bvsign, as_bvexp, as_bvsig);
      if (bvexp.is_ones() && !bvsig.is_zero())
      {
        // we use a single nan representation
        ASSERT_EQ(
            as_bv,
            BitVector(bv.size(),
                      "0" + BitVector::mk_ones(exp_size).str()
                          + BitVector::mk_min_signed(sig_size - 1).str()));
      }
      else
      {
        ASSERT_EQ(as_bv.compare(bv), 0);
      }
      ASSERT_EQ(as_bv.compare(as_bvsign.bvconcat(as_bvexp).ibvconcat(as_bvsig)),
                0);
      // only via fpfp() for MPFR implementation
      FloatingPointMPFR fpfp_mpfr =
          FloatingPointMPFR::fpfp(d_nm, bvsign, bvexp, bvsig);
      ASSERT_EQ(fp.str(), fpfp_mpfr.str());
      BitVector as_bv_mpfr = fpfp_mpfr.as_bv();
      BitVector as_bvsign_mpfr, as_bvexp_mpfr, as_bvsig_mpfr;
      FloatingPoint::ieee_bv_as_bvs(
          type_fp, as_bv_mpfr, as_bvsign_mpfr, as_bvexp_mpfr, as_bvsig_mpfr);
      if (bvexp.is_ones() && !bvsig.is_zero())
      {
        // we use a single nan representation
        ASSERT_EQ(
            as_bv_mpfr,
            BitVector(bv.size(),
                      "0" + BitVector::mk_ones(exp_size).str()
                          + BitVector::mk_min_signed(sig_size - 1).str()));
      }
      else
      {
        ASSERT_EQ(as_bv_mpfr.compare(bv), 0);
      }
      ASSERT_EQ(
          as_bv_mpfr.compare(
              as_bvsign_mpfr.bvconcat(as_bvexp_mpfr).ibvconcat(as_bvsig_mpfr)),
          0);
    }
  };

  test_for_float16(fun);
  test_for_formats(d_formats_32_128, N_TESTS, fun);
}

TEST_F(TestFp, fp_is_value)
{
  Type types[4] = {d_fp16, d_fp32, d_fp64, d_fp128};

  for (uint32_t i = 0; i < 4; i++)
  {
    {
      FloatingPoint fp = FloatingPoint::fpzero(types[i], false);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_TRUE(fp_value.fpiszero());
      ASSERT_TRUE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointMPFR fp_mpfr = FloatingPointMPFR::fpzero(types[i], false);
      ASSERT_TRUE(fp_mpfr.fpiszero());
      ASSERT_TRUE(fp_mpfr.fpispos());
      ASSERT_FALSE(fp_mpfr.fpisneg());
      ASSERT_FALSE(fp_mpfr.fpisinf());
      ASSERT_FALSE(fp_mpfr.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpzero(types[i], true);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_TRUE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_TRUE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointMPFR fp_mpfr = FloatingPointMPFR::fpzero(types[i], true);
      ASSERT_TRUE(fp_mpfr.fpiszero());
      ASSERT_FALSE(fp_mpfr.fpispos());
      ASSERT_TRUE(fp_mpfr.fpisneg());
      ASSERT_FALSE(fp_mpfr.fpisinf());
      ASSERT_FALSE(fp_mpfr.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpinf(types[i], false);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_TRUE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_TRUE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointMPFR fp_mpfr = FloatingPointMPFR::fpinf(types[i], false);
      ASSERT_FALSE(fp_mpfr.fpiszero());
      ASSERT_TRUE(fp_mpfr.fpispos());
      ASSERT_FALSE(fp_mpfr.fpisneg());
      ASSERT_TRUE(fp_mpfr.fpisinf());
      ASSERT_FALSE(fp_mpfr.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpinf(types[i], true);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_TRUE(fp_value.fpisneg());
      ASSERT_TRUE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointMPFR fp_mpfr = FloatingPointMPFR::fpinf(types[i], true);
      ASSERT_FALSE(fp_mpfr.fpiszero());
      ASSERT_FALSE(fp_mpfr.fpispos());
      ASSERT_TRUE(fp_mpfr.fpisneg());
      ASSERT_TRUE(fp_mpfr.fpisinf());
      ASSERT_FALSE(fp_mpfr.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpnan(types[i]);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_TRUE(fp_value.fpisnan());

      FloatingPointMPFR fp_mpfr = FloatingPointMPFR::fpnan(types[i]);
      ASSERT_FALSE(fp_mpfr.fpiszero());
      ASSERT_FALSE(fp_mpfr.fpispos());
      ASSERT_FALSE(fp_mpfr.fpisneg());
      ASSERT_FALSE(fp_mpfr.fpisinf());
      ASSERT_TRUE(fp_mpfr.fpisnan());
    }
  }
}

TEST_F(TestFp, fp_from_real_dec_str_rna)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000010001"}, {"0", "01000", "1000000111"},
      {"0", "01001", "0001111000"}, {"0", "01010", "0001111000"},
      {"0", "01010", "1010110011"}, {"0", "01010", "1011110111"},
      {"0", "01011", "0001110111"}, {"0", "01011", "0001110111"},
      {"0", "01011", "0110010100"}, {"0", "01011", "1010110001"},
      {"0", "01011", "1111001101"}, {"0", "01100", "0001110100"},
      {"0", "01100", "0100000010"}, {"0", "01100", "0110001111"},
      {"0", "01100", "1000011011"}, {"0", "01100", "1001100110"},
      {"0", "01100", "1010100111"}, {"0", "01100", "1100110011"},
      {"0", "01100", "1100110011"}, {"0", "01100", "1110111110"},
      {"0", "01100", "1111001111"}, {"0", "01101", "0000100100"},
      {"0", "01101", "0001101001"}, {"0", "01101", "0010101110"},
      {"0", "01101", "0011001101"}, {"0", "01101", "0011110010"},
      {"0", "01101", "0100110110"}, {"0", "01101", "0101111001"},
      {"0", "01101", "0110111100"}, {"0", "01101", "0111111110"},
      {"0", "01101", "1001000000"}, {"0", "01101", "1001100110"},
      {"0", "01101", "1001110011"}, {"0", "01101", "1010000010"},
      {"0", "01101", "1011000011"}, {"0", "01101", "1011110011"},
      {"0", "01101", "1100000100"}, {"0", "01101", "1101000100"},
      {"0", "01101", "1101111100"}, {"0", "01101", "1110000011"},
      {"0", "01101", "1111000010"}, {"0", "01110", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "01110", "0000011111"},
      {"0", "01110", "0000100101"}, {"0", "01110", "0000111101"},
      {"0", "01110", "0000111101"}, {"0", "01110", "0001011011"},
      {"0", "01110", "0001101011"}, {"0", "01110", "0001111001"},
      {"0", "01110", "0010010111"}, {"0", "01110", "0010110100"},
      {"0", "01110", "0011010001"}, {"0", "01110", "0011101101"},
      {"0", "01110", "0100001001"}, {"0", "01110", "0100100100"},
      {"0", "01110", "0101000000"}, {"0", "01110", "0101011010"},
      {"0", "01110", "0101100100"}, {"0", "01110", "0101110101"},
      {"0", "01110", "0110001111"}, {"0", "01110", "0110011010"},
      {"0", "01110", "0110101000"}, {"0", "01110", "0111000001"},
      {"0", "01110", "0111011010"}, {"0", "01110", "0111110010"},
      {"0", "01110", "1000001010"}, {"0", "01110", "1000100001"},
      {"0", "01110", "1000101001"}, {"0", "01110", "1000111000"},
      {"0", "01110", "1001001110"}, {"0", "01110", "1001100100"},
      {"0", "01110", "1001100110"}, {"0", "01110", "1001111001"},
      {"0", "01110", "1010001110"}, {"0", "01110", "1010010001"},
      {"0", "01110", "1010100010"}, {"0", "01110", "1010110110"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1011101110"}, {"0", "01110", "1011111111"},
      {"0", "01110", "1100010000"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1101000000"},
      {"0", "01110", "1101001111"}, {"0", "01110", "1101011101"},
      {"0", "01110", "1101101011"}, {"0", "01110", "1101111000"},
      {"0", "01110", "1110000100"}, {"0", "01110", "1110010000"},
      {"0", "01110", "1110011100"}, {"0", "01110", "1110100111"},
      {"0", "01110", "1110110001"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001100"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111010111"},
      {"0", "01110", "1111011010"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111100111"}, {"0", "01110", "1111101100"},
      {"0", "01110", "1111110001"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111000"}, {"0", "01110", "1111111011"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111111"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0001100110"},
      {"0", "01111", "0100110011"}, {"0", "01111", "0110011010"},
      {"0", "01111", "0111100010"}, {"0", "01111", "1000000000"},
      {"0", "01111", "1000101011"}, {"0", "01111", "1010001000"},
      {"0", "01111", "1011001101"}, {"0", "01111", "1011111000"},
      {"0", "10010", "0100000000"}, {"0", "10101", "1001000000"},
      {"0", "11100", "0011100010"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10010", "0110000000"},
      {"0", "10101", "1011110000"}, {"0", "11001", "0001101010"},
      {"0", "10101", "1110000000"}, {"0", "10101", "1110010000"},
      {"0", "10010", "1110000000"}, {"0", "10011", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"},
  };

  test_to_fp_from_real(RoundingMode::RNA, expected);
}

TEST_F(TestFp, fp_from_real_dec_str_rne)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000010001"}, {"0", "01000", "1000000111"},
      {"0", "01001", "0001111000"}, {"0", "01010", "0001111000"},
      {"0", "01010", "1010110011"}, {"0", "01010", "1011110111"},
      {"0", "01011", "0001110111"}, {"0", "01011", "0001110111"},
      {"0", "01011", "0110010100"}, {"0", "01011", "1010110001"},
      {"0", "01011", "1111001101"}, {"0", "01100", "0001110100"},
      {"0", "01100", "0100000010"}, {"0", "01100", "0110001111"},
      {"0", "01100", "1000011011"}, {"0", "01100", "1001100110"},
      {"0", "01100", "1010100111"}, {"0", "01100", "1100110011"},
      {"0", "01100", "1100110011"}, {"0", "01100", "1110111110"},
      {"0", "01100", "1111001111"}, {"0", "01101", "0000100100"},
      {"0", "01101", "0001101001"}, {"0", "01101", "0010101110"},
      {"0", "01101", "0011001101"}, {"0", "01101", "0011110010"},
      {"0", "01101", "0100110110"}, {"0", "01101", "0101111001"},
      {"0", "01101", "0110111100"}, {"0", "01101", "0111111110"},
      {"0", "01101", "1001000000"}, {"0", "01101", "1001100110"},
      {"0", "01101", "1001110011"}, {"0", "01101", "1010000010"},
      {"0", "01101", "1011000011"}, {"0", "01101", "1011110011"},
      {"0", "01101", "1100000100"}, {"0", "01101", "1101000100"},
      {"0", "01101", "1101111100"}, {"0", "01101", "1110000011"},
      {"0", "01101", "1111000010"}, {"0", "01110", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "01110", "0000011111"},
      {"0", "01110", "0000100101"}, {"0", "01110", "0000111101"},
      {"0", "01110", "0000111101"}, {"0", "01110", "0001011011"},
      {"0", "01110", "0001101011"}, {"0", "01110", "0001111001"},
      {"0", "01110", "0010010111"}, {"0", "01110", "0010110100"},
      {"0", "01110", "0011010001"}, {"0", "01110", "0011101101"},
      {"0", "01110", "0100001001"}, {"0", "01110", "0100100100"},
      {"0", "01110", "0101000000"}, {"0", "01110", "0101011010"},
      {"0", "01110", "0101100100"}, {"0", "01110", "0101110101"},
      {"0", "01110", "0110001111"}, {"0", "01110", "0110011010"},
      {"0", "01110", "0110101000"}, {"0", "01110", "0111000001"},
      {"0", "01110", "0111011010"}, {"0", "01110", "0111110010"},
      {"0", "01110", "1000001010"}, {"0", "01110", "1000100001"},
      {"0", "01110", "1000101001"}, {"0", "01110", "1000111000"},
      {"0", "01110", "1001001110"}, {"0", "01110", "1001100100"},
      {"0", "01110", "1001100110"}, {"0", "01110", "1001111001"},
      {"0", "01110", "1010001110"}, {"0", "01110", "1010010001"},
      {"0", "01110", "1010100010"}, {"0", "01110", "1010110110"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1011101110"}, {"0", "01110", "1011111111"},
      {"0", "01110", "1100010000"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1101000000"},
      {"0", "01110", "1101001111"}, {"0", "01110", "1101011101"},
      {"0", "01110", "1101101011"}, {"0", "01110", "1101111000"},
      {"0", "01110", "1110000100"}, {"0", "01110", "1110010000"},
      {"0", "01110", "1110011100"}, {"0", "01110", "1110100111"},
      {"0", "01110", "1110110001"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001100"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111010111"},
      {"0", "01110", "1111011010"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111100111"}, {"0", "01110", "1111101100"},
      {"0", "01110", "1111110001"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111000"}, {"0", "01110", "1111111011"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111111"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0001100110"},
      {"0", "01111", "0100110011"}, {"0", "01111", "0110011010"},
      {"0", "01111", "0111100010"}, {"0", "01111", "1000000000"},
      {"0", "01111", "1000101011"}, {"0", "01111", "1010001000"},
      {"0", "01111", "1011001101"}, {"0", "01111", "1011111000"},
      {"0", "10010", "0100000000"}, {"0", "10101", "1001000000"},
      {"0", "11100", "0011100010"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10010", "0110000000"},
      {"0", "10101", "1011110000"}, {"0", "11001", "0001101010"},
      {"0", "10101", "1110000000"}, {"0", "10101", "1110010000"},
      {"0", "10010", "1110000000"}, {"0", "10011", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"},
  };

  test_to_fp_from_real(RoundingMode::RNE, expected);
}

TEST_F(TestFp, fp_from_real_dec_str_rtn)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000010000"}, {"0", "01000", "1000000111"},
      {"0", "01001", "0001110111"}, {"0", "01010", "0001110111"},
      {"0", "01010", "1010110010"}, {"0", "01010", "1011110110"},
      {"0", "01011", "0001110110"}, {"0", "01011", "0001110110"},
      {"0", "01011", "0110010011"}, {"0", "01011", "1010110000"},
      {"0", "01011", "1111001100"}, {"0", "01100", "0001110100"},
      {"0", "01100", "0100000001"}, {"0", "01100", "0110001110"},
      {"0", "01100", "1000011011"}, {"0", "01100", "1001100110"},
      {"0", "01100", "1010100111"}, {"0", "01100", "1100110010"},
      {"0", "01100", "1100110010"}, {"0", "01100", "1110111101"},
      {"0", "01100", "1111001110"}, {"0", "01101", "0000100100"},
      {"0", "01101", "0001101001"}, {"0", "01101", "0010101101"},
      {"0", "01101", "0011001100"}, {"0", "01101", "0011110001"},
      {"0", "01101", "0100110101"}, {"0", "01101", "0101111000"},
      {"0", "01101", "0110111011"}, {"0", "01101", "0111111110"},
      {"0", "01101", "1001000000"}, {"0", "01101", "1001100110"},
      {"0", "01101", "1001110010"}, {"0", "01101", "1010000001"},
      {"0", "01101", "1011000011"}, {"0", "01101", "1011110011"},
      {"0", "01101", "1100000011"}, {"0", "01101", "1101000011"},
      {"0", "01101", "1101111100"}, {"0", "01101", "1110000010"},
      {"0", "01101", "1111000001"}, {"0", "01110", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "01110", "0000011110"},
      {"0", "01110", "0000100100"}, {"0", "01110", "0000111101"},
      {"0", "01110", "0000111101"}, {"0", "01110", "0001011011"},
      {"0", "01110", "0001101010"}, {"0", "01110", "0001111001"},
      {"0", "01110", "0010010110"}, {"0", "01110", "0010110011"},
      {"0", "01110", "0011010000"}, {"0", "01110", "0011101100"},
      {"0", "01110", "0100001000"}, {"0", "01110", "0100100100"},
      {"0", "01110", "0100111111"}, {"0", "01110", "0101011010"},
      {"0", "01110", "0101100100"}, {"0", "01110", "0101110100"},
      {"0", "01110", "0110001110"}, {"0", "01110", "0110011001"},
      {"0", "01110", "0110101000"}, {"0", "01110", "0111000001"},
      {"0", "01110", "0111011001"}, {"0", "01110", "0111110001"},
      {"0", "01110", "1000001001"}, {"0", "01110", "1000100000"},
      {"0", "01110", "1000101001"}, {"0", "01110", "1000110111"},
      {"0", "01110", "1001001101"}, {"0", "01110", "1001100011"},
      {"0", "01110", "1001100110"}, {"0", "01110", "1001111000"},
      {"0", "01110", "1010001101"}, {"0", "01110", "1010010001"},
      {"0", "01110", "1010100001"}, {"0", "01110", "1010110101"},
      {"0", "01110", "1011001000"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1011101101"}, {"0", "01110", "1011111111"},
      {"0", "01110", "1100010000"}, {"0", "01110", "1100100000"},
      {"0", "01110", "1100110000"}, {"0", "01110", "1101000000"},
      {"0", "01110", "1101001110"}, {"0", "01110", "1101011101"},
      {"0", "01110", "1101101010"}, {"0", "01110", "1101110111"},
      {"0", "01110", "1110000100"}, {"0", "01110", "1110010000"},
      {"0", "01110", "1110011011"}, {"0", "01110", "1110100110"},
      {"0", "01110", "1110110000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001011"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111010111"},
      {"0", "01110", "1111011010"}, {"0", "01110", "1111100000"},
      {"0", "01110", "1111100110"}, {"0", "01110", "1111101100"},
      {"0", "01110", "1111110000"}, {"0", "01110", "1111110100"},
      {"0", "01110", "1111111000"}, {"0", "01110", "1111111011"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111110"},
      {"0", "01110", "1111111111"}, {"0", "01111", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0001100110"},
      {"0", "01111", "0100110011"}, {"0", "01111", "0110011001"},
      {"0", "01111", "0111100010"}, {"0", "01111", "1000000000"},
      {"0", "01111", "1000101010"}, {"0", "01111", "1010001000"},
      {"0", "01111", "1011001100"}, {"0", "01111", "1011111000"},
      {"0", "10010", "0100000000"}, {"0", "10101", "1001000000"},
      {"0", "11100", "0011100010"}, {"0", "11110", "1111111111"},
      {"0", "11110", "1111111111"}, {"0", "11110", "1111111111"},
      {"0", "11110", "1111111111"}, {"0", "10010", "0110000000"},
      {"0", "10101", "1011110000"}, {"0", "11001", "0001101010"},
      {"0", "10101", "1110000000"}, {"0", "10101", "1110010000"},
      {"0", "10010", "1110000000"}, {"0", "10011", "0000000000"},
      {"0", "11110", "1111111111"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11110", "1111111111"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11110", "1111111111"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11110", "1111111111"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11110", "1111111111"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"},
  };

  test_to_fp_from_real(RoundingMode::RTN, expected);
}

TEST_F(TestFp, fp_from_real_dec_str_rtp)
{
  std::vector<std::vector<const char *>> expected = {

      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000010001"}, {"0", "01000", "1000001000"},
      {"0", "01001", "0001111000"}, {"0", "01010", "0001111000"},
      {"0", "01010", "1010110011"}, {"0", "01010", "1011110111"},
      {"0", "01011", "0001110111"}, {"0", "01011", "0001110111"},
      {"0", "01011", "0110010100"}, {"0", "01011", "1010110001"},
      {"0", "01011", "1111001101"}, {"0", "01100", "0001110101"},
      {"0", "01100", "0100000010"}, {"0", "01100", "0110001111"},
      {"0", "01100", "1000011100"}, {"0", "01100", "1001100111"},
      {"0", "01100", "1010101000"}, {"0", "01100", "1100110011"},
      {"0", "01100", "1100110011"}, {"0", "01100", "1110111110"},
      {"0", "01100", "1111001111"}, {"0", "01101", "0000100101"},
      {"0", "01101", "0001101010"}, {"0", "01101", "0010101110"},
      {"0", "01101", "0011001101"}, {"0", "01101", "0011110010"},
      {"0", "01101", "0100110110"}, {"0", "01101", "0101111001"},
      {"0", "01101", "0110111100"}, {"0", "01101", "0111111111"},
      {"0", "01101", "1001000001"}, {"0", "01101", "1001100111"},
      {"0", "01101", "1001110011"}, {"0", "01101", "1010000010"},
      {"0", "01101", "1011000100"}, {"0", "01101", "1011110100"},
      {"0", "01101", "1100000100"}, {"0", "01101", "1101000100"},
      {"0", "01101", "1101111101"}, {"0", "01101", "1110000011"},
      {"0", "01101", "1111000010"}, {"0", "01110", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "01110", "0000011111"},
      {"0", "01110", "0000100101"}, {"0", "01110", "0000111110"},
      {"0", "01110", "0000111110"}, {"0", "01110", "0001011100"},
      {"0", "01110", "0001101011"}, {"0", "01110", "0001111010"},
      {"0", "01110", "0010010111"}, {"0", "01110", "0010110100"},
      {"0", "01110", "0011010001"}, {"0", "01110", "0011101101"},
      {"0", "01110", "0100001001"}, {"0", "01110", "0100100101"},
      {"0", "01110", "0101000000"}, {"0", "01110", "0101011011"},
      {"0", "01110", "0101100101"}, {"0", "01110", "0101110101"},
      {"0", "01110", "0110001111"}, {"0", "01110", "0110011010"},
      {"0", "01110", "0110101001"}, {"0", "01110", "0111000010"},
      {"0", "01110", "0111011010"}, {"0", "01110", "0111110010"},
      {"0", "01110", "1000001010"}, {"0", "01110", "1000100001"},
      {"0", "01110", "1000101010"}, {"0", "01110", "1000111000"},
      {"0", "01110", "1001001110"}, {"0", "01110", "1001100100"},
      {"0", "01110", "1001100111"}, {"0", "01110", "1001111001"},
      {"0", "01110", "1010001110"}, {"0", "01110", "1010010010"},
      {"0", "01110", "1010100010"}, {"0", "01110", "1010110110"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011100"},
      {"0", "01110", "1011101110"}, {"0", "01110", "1100000000"},
      {"0", "01110", "1100010001"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1101000001"},
      {"0", "01110", "1101001111"}, {"0", "01110", "1101011110"},
      {"0", "01110", "1101101011"}, {"0", "01110", "1101111000"},
      {"0", "01110", "1110000101"}, {"0", "01110", "1110010001"},
      {"0", "01110", "1110011100"}, {"0", "01110", "1110100111"},
      {"0", "01110", "1110110001"}, {"0", "01110", "1110111011"},
      {"0", "01110", "1111000100"}, {"0", "01110", "1111001100"},
      {"0", "01110", "1111010100"}, {"0", "01110", "1111011000"},
      {"0", "01110", "1111011011"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111100111"}, {"0", "01110", "1111101101"},
      {"0", "01110", "1111110001"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111001"}, {"0", "01110", "1111111100"},
      {"0", "01110", "1111111110"}, {"0", "01110", "1111111111"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0001100111"},
      {"0", "01111", "0100110100"}, {"0", "01111", "0110011010"},
      {"0", "01111", "0111100011"}, {"0", "01111", "1000000000"},
      {"0", "01111", "1000101011"}, {"0", "01111", "1010001001"},
      {"0", "01111", "1011001101"}, {"0", "01111", "1011111001"},
      {"0", "10010", "0100000000"}, {"0", "10101", "1001000000"},
      {"0", "11100", "0011100010"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "11111", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10010", "0110000000"},
      {"0", "10101", "1011110000"}, {"0", "11001", "0001101010"},
      {"0", "10101", "1110000000"}, {"0", "10101", "1110010000"},
      {"0", "10010", "1110000000"}, {"0", "10011", "0000000000"},
      {"0", "11111", "0000000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001011"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001011"},
      {"0", "11111", "0000000000"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11111", "0000000000"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"},
  };

  test_to_fp_from_real(RoundingMode::RTP, expected);
}

TEST_F(TestFp, fp_from_real_dec_str_rtz)
{
  std::vector<std::vector<const char *>> expected = {

      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000010000"}, {"0", "01000", "1000000111"},
      {"0", "01001", "0001110111"}, {"0", "01010", "0001110111"},
      {"0", "01010", "1010110010"}, {"0", "01010", "1011110110"},
      {"0", "01011", "0001110110"}, {"0", "01011", "0001110110"},
      {"0", "01011", "0110010011"}, {"0", "01011", "1010110000"},
      {"0", "01011", "1111001100"}, {"0", "01100", "0001110100"},
      {"0", "01100", "0100000001"}, {"0", "01100", "0110001110"},
      {"0", "01100", "1000011011"}, {"0", "01100", "1001100110"},
      {"0", "01100", "1010100111"}, {"0", "01100", "1100110010"},
      {"0", "01100", "1100110010"}, {"0", "01100", "1110111101"},
      {"0", "01100", "1111001110"}, {"0", "01101", "0000100100"},
      {"0", "01101", "0001101001"}, {"0", "01101", "0010101101"},
      {"0", "01101", "0011001100"}, {"0", "01101", "0011110001"},
      {"0", "01101", "0100110101"}, {"0", "01101", "0101111000"},
      {"0", "01101", "0110111011"}, {"0", "01101", "0111111110"},
      {"0", "01101", "1001000000"}, {"0", "01101", "1001100110"},
      {"0", "01101", "1001110010"}, {"0", "01101", "1010000001"},
      {"0", "01101", "1011000011"}, {"0", "01101", "1011110011"},
      {"0", "01101", "1100000011"}, {"0", "01101", "1101000011"},
      {"0", "01101", "1101111100"}, {"0", "01101", "1110000010"},
      {"0", "01101", "1111000001"}, {"0", "01110", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "01110", "0000011110"},
      {"0", "01110", "0000100100"}, {"0", "01110", "0000111101"},
      {"0", "01110", "0000111101"}, {"0", "01110", "0001011011"},
      {"0", "01110", "0001101010"}, {"0", "01110", "0001111001"},
      {"0", "01110", "0010010110"}, {"0", "01110", "0010110011"},
      {"0", "01110", "0011010000"}, {"0", "01110", "0011101100"},
      {"0", "01110", "0100001000"}, {"0", "01110", "0100100100"},
      {"0", "01110", "0100111111"}, {"0", "01110", "0101011010"},
      {"0", "01110", "0101100100"}, {"0", "01110", "0101110100"},
      {"0", "01110", "0110001110"}, {"0", "01110", "0110011001"},
      {"0", "01110", "0110101000"}, {"0", "01110", "0111000001"},
      {"0", "01110", "0111011001"}, {"0", "01110", "0111110001"},
      {"0", "01110", "1000001001"}, {"0", "01110", "1000100000"},
      {"0", "01110", "1000101001"}, {"0", "01110", "1000110111"},
      {"0", "01110", "1001001101"}, {"0", "01110", "1001100011"},
      {"0", "01110", "1001100110"}, {"0", "01110", "1001111000"},
      {"0", "01110", "1010001101"}, {"0", "01110", "1010010001"},
      {"0", "01110", "1010100001"}, {"0", "01110", "1010110101"},
      {"0", "01110", "1011001000"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1011101101"}, {"0", "01110", "1011111111"},
      {"0", "01110", "1100010000"}, {"0", "01110", "1100100000"},
      {"0", "01110", "1100110000"}, {"0", "01110", "1101000000"},
      {"0", "01110", "1101001110"}, {"0", "01110", "1101011101"},
      {"0", "01110", "1101101010"}, {"0", "01110", "1101110111"},
      {"0", "01110", "1110000100"}, {"0", "01110", "1110010000"},
      {"0", "01110", "1110011011"}, {"0", "01110", "1110100110"},
      {"0", "01110", "1110110000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001011"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111010111"},
      {"0", "01110", "1111011010"}, {"0", "01110", "1111100000"},
      {"0", "01110", "1111100110"}, {"0", "01110", "1111101100"},
      {"0", "01110", "1111110000"}, {"0", "01110", "1111110100"},
      {"0", "01110", "1111111000"}, {"0", "01110", "1111111011"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111110"},
      {"0", "01110", "1111111111"}, {"0", "01111", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "01111", "0001100110"},
      {"0", "01111", "0100110011"}, {"0", "01111", "0110011001"},
      {"0", "01111", "0111100010"}, {"0", "01111", "1000000000"},
      {"0", "01111", "1000101010"}, {"0", "01111", "1010001000"},
      {"0", "01111", "1011001100"}, {"0", "01111", "1011111000"},
      {"0", "10010", "0100000000"}, {"0", "10101", "1001000000"},
      {"0", "11100", "0011100010"}, {"0", "11110", "1111111111"},
      {"0", "11110", "1111111111"}, {"0", "11110", "1111111111"},
      {"0", "11110", "1111111111"}, {"0", "10010", "0110000000"},
      {"0", "10101", "1011110000"}, {"0", "11001", "0001101010"},
      {"0", "10101", "1110000000"}, {"0", "10101", "1110010000"},
      {"0", "10010", "1110000000"}, {"0", "10011", "0000000000"},
      {"0", "11110", "1111111111"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11110", "1111111111"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11110", "1111111111"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"}, {"0", "10110", "0110100000"},
      {"0", "10000", "0000000000"}, {"0", "10011", "0100000000"},
      {"0", "10011", "1000000000"}, {"0", "10111", "0000000000"},
      {"0", "10000", "1000000000"}, {"0", "10011", "1110000000"},
      {"0", "11010", "0111011100"}, {"0", "11110", "0000001010"},
      {"0", "11110", "1111111111"}, {"0", "10111", "0110100000"},
      {"0", "10001", "0100000000"}, {"0", "11011", "0011101100"},
      {"0", "10001", "1000000000"}, {"0", "10001", "1100000000"},
      {"0", "11000", "0110100000"}, {"0", "11110", "1111111111"},
      {"0", "10010", "0000000000"}, {"0", "10101", "0101010000"},
      {"0", "10010", "0010000000"},
  };

  test_to_fp_from_real(RoundingMode::RTZ, expected);
}

TEST_F(TestFp, fp_from_real_rat_str_rna)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "01111", "0000000000"}, {"0", "01011", "1001100110"},
      {"0", "00000", "0000010001"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01011", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "00111", "0000000000"},
      {"0", "01101", "0000000000"}, {"0", "01100", "1001100110"},
      {"0", "01100", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "10010", "0100000000"}, {"0", "11000", "1111010000"},
      {"0", "01111", "0000000001"}, {"0", "01111", "0000001010"},
      {"0", "01110", "0000011111"}, {"0", "01010", "0101010101"},
      {"0", "01000", "0001000100"}, {"0", "01111", "0001011100"},
      {"0", "01001", "0001111000"}, {"0", "01110", "0101110101"},
      {"0", "01001", "0110011001"}, {"0", "01101", "1100000100"},
      {"0", "01111", "0001100110"}, {"0", "10001", "0110000000"},
      {"0", "01111", "0001110001"}, {"0", "01100", "1100110011"},
      {"0", "00011", "1110000000"}, {"0", "01110", "0010010111"},
      {"0", "00101", "0000011001"}, {"0", "01000", "1000000111"},
      {"0", "01111", "0110101000"}, {"0", "10010", "1000000000"},
      {"0", "10101", "1110000000"}, {"0", "01110", "1110110001"},
      {"0", "01110", "0011010001"}, {"0", "00000", "0110100000"},
      {"0", "00000", "0110100000"}, {"0", "01111", "0100101001"},
      {"0", "00000", "0110110011"}, {"0", "00000", "0110110100"},
      {"0", "01100", "1010100111"}, {"0", "01111", "0100111101"},
      {"0", "01110", "0000111101"}, {"0", "01100", "0001000100"},
      {"0", "10111", "0100110111"}, {"0", "00110", "0110110000"},
      {"0", "00101", "0110110000"}, {"0", "01111", "0110001111"},
      {"0", "01100", "0001110100"}, {"0", "01010", "0001111000"},
      {"0", "01111", "0110011000"}, {"0", "01111", "0110011001"},
      {"0", "01111", "0110100100"}, {"0", "01110", "0110101000"},
      {"0", "01110", "0111000001"}, {"0", "01111", "0111000101"},
      {"0", "01101", "0010101110"}, {"0", "01111", "1000101011"},
      {"0", "00001", "0100100000"}, {"0", "01100", "0100000010"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001001"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1001111001"}, {"0", "00000", "0000011100"},
      {"0", "01100", "0101010101"}, {"0", "01100", "0101010101"},
      {"0", "01101", "0000000000"}, {"0", "01110", "1000100001"},
      {"0", "01100", "0110001111"}, {"0", "01011", "0001110111"},
      {"0", "00001", "0010101110"}, {"0", "01110", "1101000000"},
      {"0", "00101", "0111110111"}, {"0", "01110", "1110011100"},
      {"0", "10000", "0000000000"}, {"0", "01101", "1001100110"},
      {"0", "01100", "1001100110"}, {"0", "01111", "1001001000"},
      {"0", "01101", "1010000010"}, {"0", "00000", "0000000000"},
      {"0", "01011", "1010110001"}, {"0", "01110", "1011101110"},
      {"0", "01110", "0001111001"}, {"0", "01100", "1100110011"},
      {"0", "00000", "0000000000"}, {"0", "01100", "1101011010"},
      {"0", "01110", "1101011101"}, {"0", "01110", "1101111000"},
      {"0", "01101", "1101111100"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1110010000"}, {"0", "10011", "1000000000"},
      {"0", "01100", "1110111110"}, {"0", "01101", "1111000010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001100"},
      {"0", "01011", "1111001101"}, {"0", "01110", "1001001110"},
      {"0", "00011", "0000001010"}, {"0", "01101", "1111100110"},
      {"0", "01110", "1111110001"}, {"0", "00000", "0000000000"},
      {"0", "01010", "1010110011"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0010110101"}, {"0", "00000", "0010110101"},
      {"0", "00000", "0000101110"}, {"0", "00000", "0000000101"},
      {"0", "01101", "0001101001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0011001101"}, {"0", "01111", "1000000000"},
      {"0", "00000", "0000000010"}, {"0", "01110", "1000000000"},
      {"0", "01110", "0011001101"}, {"0", "01010", "1110101110"},
      {"0", "01101", "0011001101"}, {"0", "01110", "0011101101"},
      {"0", "01110", "1000101001"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01110", "0100100100"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0101010101"}, {"0", "01101", "0101010101"},
      {"0", "01101", "0101010101"}, {"0", "01110", "0101011010"},
      {"0", "01101", "0101111001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0110111100"}, {"0", "00110", "1101011011"},
      {"0", "11111", "0000000000"}, {"0", "11000", "0111010010"},
      {"0", "01101", "0111111110"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000100001"},
      {"0", "01101", "1001000000"}, {"0", "01110", "1111111000"},
      {"0", "01110", "1001100110"}, {"0", "11110", "0011101100"},
      {"0", "00000", "0000000001"}, {"0", "01010", "0101010101"},
      {"0", "01110", "1010110110"}, {"0", "01101", "1011000011"},
      {"0", "01011", "0110010100"}, {"0", "01110", "1011111111"},
      {"0", "11111", "0000000000"}, {"0", "01110", "1101001111"},
      {"0", "00000", "0100110111"}, {"0", "01101", "1110000011"},
      {"0", "00000", "0000010001"}, {"0", "01110", "1111011010"},
      {"0", "01110", "1111100111"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1111111011"}, {"0", "01010", "0100000000"},
      {"0", "10000", "0100000000"}, {"0", "01110", "0000000000"},
      {"0", "11011", "0011101100"}, {"0", "01110", "1010100010"},
      {"0", "01111", "0100110000"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0000111101"}, {"0", "01010", "1011101000"},
      {"0", "01101", "1011110011"}, {"0", "01110", "0001011011"},
      {"0", "00000", "0000000101"}, {"0", "00101", "0110110000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01000", "0100011111"}, {"0", "01110", "0010110100"},
      {"0", "01011", "1110011101"}, {"0", "01110", "1110100111"},
      {"0", "10001", "1000000000"}, {"0", "01111", "0011001101"},
      {"0", "10100", "1110000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0011110010"}, {"0", "01111", "1001001000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "0100011000"},
      {"0", "01101", "0000100100"}, {"0", "01110", "0101000000"},
      {"0", "00001", "0001010110"}, {"0", "01110", "0101100100"},
      {"0", "10001", "0111111101"}, {"0", "01110", "0110000101"},
      {"0", "01110", "0110001100"}, {"0", "01110", "0110001111"},
      {"0", "01011", "0001110111"}, {"0", "01111", "0110011000"},
      {"0", "01111", "0110011010"}, {"0", "01111", "0110101000"},
      {"0", "01110", "0110101110"}, {"0", "11000", "0110100000"},
      {"0", "01110", "0111011010"}, {"0", "00100", "0011010001"},
      {"0", "00001", "1010001110"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0111110010"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1000001010"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000111000"},
      {"0", "01110", "0100001001"}, {"0", "01110", "1001100100"},
      {"0", "01111", "1001100110"}, {"0", "01101", "0100110110"},
      {"0", "01110", "1010001110"}, {"0", "00000", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "10000", "1110001000"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1100010000"}, {"0", "01000", "0010001010"},
      {"0", "11000", "0110001100"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1100110011"},
      {"0", "01110", "1100110101"}, {"0", "01101", "1101000100"},
      {"0", "01110", "1101101011"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1110000100"}, {"0", "01100", "1000011011"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111101100"}, {"0", "01110", "1111101100"},
      {"0", "00010", "1010000000"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111110"},
      {"0", "01110", "1111111111"}, {"0", "01111", "0000000000"},
  };

  test_to_fp_from_rational(INT, RoundingMode::RNA, expected);
  test_to_fp_from_rational(NUM_DEC, RoundingMode::RNA, expected);
  test_to_fp_from_rational(DEN_DEC, RoundingMode::RNA, expected);
  test_to_fp_from_rational(DEC, RoundingMode::RNA, expected);
}

TEST_F(TestFp, fp_from_real_rat_str_rne)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "01111", "0000000000"}, {"0", "01011", "1001100110"},
      {"0", "00000", "0000010001"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01011", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "00111", "0000000000"},
      {"0", "01101", "0000000000"}, {"0", "01100", "1001100110"},
      {"0", "01100", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "10010", "0100000000"}, {"0", "11000", "1111010000"},
      {"0", "01111", "0000000001"}, {"0", "01111", "0000001010"},
      {"0", "01110", "0000011111"}, {"0", "01010", "0101010101"},
      {"0", "01000", "0001000100"}, {"0", "01111", "0001011100"},
      {"0", "01001", "0001111000"}, {"0", "01110", "0101110101"},
      {"0", "01001", "0110011001"}, {"0", "01101", "1100000100"},
      {"0", "01111", "0001100110"}, {"0", "10001", "0110000000"},
      {"0", "01111", "0001110001"}, {"0", "01100", "1100110011"},
      {"0", "00011", "1110000000"}, {"0", "01110", "0010010111"},
      {"0", "00101", "0000011001"}, {"0", "01000", "1000000111"},
      {"0", "01111", "0110101000"}, {"0", "10010", "1000000000"},
      {"0", "10101", "1110000000"}, {"0", "01110", "1110110001"},
      {"0", "01110", "0011010001"}, {"0", "00000", "0110100000"},
      {"0", "00000", "0110100000"}, {"0", "01111", "0100101001"},
      {"0", "00000", "0110110011"}, {"0", "00000", "0110110100"},
      {"0", "01100", "1010100111"}, {"0", "01111", "0100111101"},
      {"0", "01110", "0000111101"}, {"0", "01100", "0001000100"},
      {"0", "10111", "0100110111"}, {"0", "00110", "0110110000"},
      {"0", "00101", "0110110000"}, {"0", "01111", "0110001111"},
      {"0", "01100", "0001110100"}, {"0", "01010", "0001111000"},
      {"0", "01111", "0110011000"}, {"0", "01111", "0110011001"},
      {"0", "01111", "0110100100"}, {"0", "01110", "0110101000"},
      {"0", "01110", "0111000001"}, {"0", "01111", "0111000101"},
      {"0", "01101", "0010101110"}, {"0", "01111", "1000101011"},
      {"0", "00001", "0100100000"}, {"0", "01100", "0100000010"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001001"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1001111001"}, {"0", "00000", "0000011100"},
      {"0", "01100", "0101010101"}, {"0", "01100", "0101010101"},
      {"0", "01101", "0000000000"}, {"0", "01110", "1000100001"},
      {"0", "01100", "0110001111"}, {"0", "01011", "0001110111"},
      {"0", "00001", "0010101110"}, {"0", "01110", "1101000000"},
      {"0", "00101", "0111110111"}, {"0", "01110", "1110011100"},
      {"0", "10000", "0000000000"}, {"0", "01101", "1001100110"},
      {"0", "01100", "1001100110"}, {"0", "01111", "1001001000"},
      {"0", "01101", "1010000010"}, {"0", "00000", "0000000000"},
      {"0", "01011", "1010110001"}, {"0", "01110", "1011101110"},
      {"0", "01110", "0001111001"}, {"0", "01100", "1100110011"},
      {"0", "00000", "0000000000"}, {"0", "01100", "1101011010"},
      {"0", "01110", "1101011101"}, {"0", "01110", "1101111000"},
      {"0", "01101", "1101111100"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1110010000"}, {"0", "10011", "1000000000"},
      {"0", "01100", "1110111110"}, {"0", "01101", "1111000010"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001100"},
      {"0", "01011", "1111001101"}, {"0", "01110", "1001001110"},
      {"0", "00011", "0000001010"}, {"0", "01101", "1111100110"},
      {"0", "01110", "1111110001"}, {"0", "00000", "0000000000"},
      {"0", "01010", "1010110011"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0010110101"}, {"0", "00000", "0010110101"},
      {"0", "00000", "0000101110"}, {"0", "00000", "0000000101"},
      {"0", "01101", "0001101001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0011001101"}, {"0", "01111", "1000000000"},
      {"0", "00000", "0000000010"}, {"0", "01110", "1000000000"},
      {"0", "01110", "0011001101"}, {"0", "01010", "1110101110"},
      {"0", "01101", "0011001101"}, {"0", "01110", "0011101101"},
      {"0", "01110", "1000101001"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01110", "0100100100"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0101010101"}, {"0", "01101", "0101010101"},
      {"0", "01101", "0101010101"}, {"0", "01110", "0101011010"},
      {"0", "01101", "0101111001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0110111100"}, {"0", "00110", "1101011011"},
      {"0", "11111", "0000000000"}, {"0", "11000", "0111010010"},
      {"0", "01101", "0111111110"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000100001"},
      {"0", "01101", "1001000000"}, {"0", "01110", "1111111000"},
      {"0", "01110", "1001100110"}, {"0", "11110", "0011101100"},
      {"0", "00000", "0000000001"}, {"0", "01010", "0101010101"},
      {"0", "01110", "1010110110"}, {"0", "01101", "1011000011"},
      {"0", "01011", "0110010100"}, {"0", "01110", "1011111111"},
      {"0", "11111", "0000000000"}, {"0", "01110", "1101001111"},
      {"0", "00000", "0100110111"}, {"0", "01101", "1110000011"},
      {"0", "00000", "0000010001"}, {"0", "01110", "1111011010"},
      {"0", "01110", "1111100111"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1111111011"}, {"0", "01010", "0100000000"},
      {"0", "10000", "0100000000"}, {"0", "01110", "0000000000"},
      {"0", "11011", "0011101100"}, {"0", "01110", "1010100010"},
      {"0", "01111", "0100110000"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0000111101"}, {"0", "01010", "1011101000"},
      {"0", "01101", "1011110011"}, {"0", "01110", "0001011011"},
      {"0", "00000", "0000000101"}, {"0", "00101", "0110110000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01000", "0100011111"}, {"0", "01110", "0010110100"},
      {"0", "01011", "1110011101"}, {"0", "01110", "1110100111"},
      {"0", "10001", "1000000000"}, {"0", "01111", "0011001101"},
      {"0", "10100", "1110000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0011110010"}, {"0", "01111", "1001001000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "0100011000"},
      {"0", "01101", "0000100100"}, {"0", "01110", "0101000000"},
      {"0", "00001", "0001010110"}, {"0", "01110", "0101100100"},
      {"0", "10001", "0111111101"}, {"0", "01110", "0110000101"},
      {"0", "01110", "0110001100"}, {"0", "01110", "0110001111"},
      {"0", "01011", "0001110111"}, {"0", "01111", "0110011000"},
      {"0", "01111", "0110011010"}, {"0", "01111", "0110101000"},
      {"0", "01110", "0110101110"}, {"0", "11000", "0110100000"},
      {"0", "01110", "0111011010"}, {"0", "00100", "0011010001"},
      {"0", "00001", "1010001110"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0111110010"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1000001010"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000111000"},
      {"0", "01110", "0100001001"}, {"0", "01110", "1001100100"},
      {"0", "01111", "1001100110"}, {"0", "01101", "0100110110"},
      {"0", "01110", "1010001110"}, {"0", "00000", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "10000", "1110001000"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1100010000"}, {"0", "01000", "0010001010"},
      {"0", "11000", "0110001100"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1100110011"},
      {"0", "01110", "1100110101"}, {"0", "01101", "1101000100"},
      {"0", "01110", "1101101011"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1110000100"}, {"0", "01100", "1000011011"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111101100"}, {"0", "01110", "1111101100"},
      {"0", "00010", "1010000000"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111110"},
      {"0", "01110", "1111111111"}, {"0", "01111", "0000000000"},
  };

  test_to_fp_from_rational(INT, RoundingMode::RNE, expected);
  test_to_fp_from_rational(NUM_DEC, RoundingMode::RNE, expected);
  test_to_fp_from_rational(DEN_DEC, RoundingMode::RNE, expected);
  test_to_fp_from_rational(DEC, RoundingMode::RNE, expected);
}

TEST_F(TestFp, fp_from_real_rat_str_rtn)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "01111", "0000000000"}, {"0", "01011", "1001100110"},
      {"0", "00000", "0000010000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01011", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "00111", "0000000000"},
      {"0", "01101", "0000000000"}, {"0", "01100", "1001100110"},
      {"0", "01100", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "10010", "0100000000"}, {"0", "11000", "1111010000"},
      {"0", "01111", "0000000001"}, {"0", "01111", "0000001010"},
      {"0", "01110", "0000011110"}, {"0", "01010", "0101010101"},
      {"0", "01000", "0001000100"}, {"0", "01111", "0001011100"},
      {"0", "01001", "0001110111"}, {"0", "01110", "0101110100"},
      {"0", "01001", "0110011001"}, {"0", "01101", "1100000011"},
      {"0", "01111", "0001100110"}, {"0", "10001", "0110000000"},
      {"0", "01111", "0001110000"}, {"0", "01100", "1100110010"},
      {"0", "00011", "1110000000"}, {"0", "01110", "0010010110"},
      {"0", "00101", "0000011000"}, {"0", "01000", "1000000111"},
      {"0", "01111", "0110101000"}, {"0", "10010", "1000000000"},
      {"0", "10101", "1110000000"}, {"0", "01110", "1110110000"},
      {"0", "01110", "0011010000"}, {"0", "00000", "0110100000"},
      {"0", "00000", "0110100000"}, {"0", "01111", "0100101000"},
      {"0", "00000", "0110110010"}, {"0", "00000", "0110110011"},
      {"0", "01100", "1010100111"}, {"0", "01111", "0100111101"},
      {"0", "01110", "0000111101"}, {"0", "01100", "0001000100"},
      {"0", "10111", "0100110111"}, {"0", "00110", "0110110000"},
      {"0", "00101", "0110110000"}, {"0", "01111", "0110001111"},
      {"0", "01100", "0001110100"}, {"0", "01010", "0001110111"},
      {"0", "01111", "0110010111"}, {"0", "01111", "0110011000"},
      {"0", "01111", "0110100011"}, {"0", "01110", "0110101000"},
      {"0", "01110", "0111000001"}, {"0", "01111", "0111000101"},
      {"0", "01101", "0010101101"}, {"0", "01111", "1000101010"},
      {"0", "00001", "0100011111"}, {"0", "01100", "0100000001"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1001111000"}, {"0", "00000", "0000011011"},
      {"0", "01100", "0101010101"}, {"0", "01100", "0101010101"},
      {"0", "01100", "1111111111"}, {"0", "01110", "1000100001"},
      {"0", "01100", "0110001110"}, {"0", "01011", "0001110110"},
      {"0", "00001", "0010101110"}, {"0", "01110", "1101000000"},
      {"0", "00101", "0111110110"}, {"0", "01110", "1110011011"},
      {"0", "10000", "0000000000"}, {"0", "01101", "1001100110"},
      {"0", "01100", "1001100110"}, {"0", "01111", "1001001000"},
      {"0", "01101", "1010000001"}, {"0", "00000", "0000000000"},
      {"0", "01011", "1010110000"}, {"0", "01110", "1011101101"},
      {"0", "01110", "0001111001"}, {"0", "01100", "1100110010"},
      {"0", "00000", "0000000000"}, {"0", "01100", "1101011010"},
      {"0", "01110", "1101011101"}, {"0", "01110", "1101110111"},
      {"0", "01101", "1101111100"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1110010000"}, {"0", "10011", "1000000000"},
      {"0", "01100", "1110111101"}, {"0", "01101", "1111000001"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001011"},
      {"0", "01011", "1111001100"}, {"0", "01110", "1001001101"},
      {"0", "00011", "0000001001"}, {"0", "01101", "1111100101"},
      {"0", "01110", "1111110000"}, {"0", "00000", "0000000000"},
      {"0", "01010", "1010110010"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0010110101"}, {"0", "00000", "0010110101"},
      {"0", "00000", "0000101110"}, {"0", "00000", "0000000100"},
      {"0", "01101", "0001101001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0011001100"}, {"0", "01111", "1000000000"},
      {"0", "00000", "0000000001"}, {"0", "01110", "1000000000"},
      {"0", "01110", "0011001100"}, {"0", "01010", "1110101110"},
      {"0", "01101", "0011001100"}, {"0", "01110", "0011101100"},
      {"0", "01110", "1000101001"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01110", "0100100100"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0101010101"}, {"0", "01101", "0101010101"},
      {"0", "01101", "0101010101"}, {"0", "01110", "0101011010"},
      {"0", "01101", "0101111000"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0110111011"}, {"0", "00110", "1101011011"},
      {"0", "11110", "1111111111"}, {"0", "11000", "0111010010"},
      {"0", "01101", "0111111110"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000100000"},
      {"0", "01101", "1001000000"}, {"0", "01110", "1111111000"},
      {"0", "01110", "1001100110"}, {"0", "11110", "0011101100"},
      {"0", "00000", "0000000000"}, {"0", "01010", "0101010101"},
      {"0", "01110", "1010110101"}, {"0", "01101", "1011000011"},
      {"0", "01011", "0110010011"}, {"0", "01110", "1011111111"},
      {"0", "11110", "1111111111"}, {"0", "01110", "1101001110"},
      {"0", "00000", "0100110111"}, {"0", "01101", "1110000010"},
      {"0", "00000", "0000010000"}, {"0", "01110", "1111011010"},
      {"0", "01110", "1111100110"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1111111011"}, {"0", "01010", "0100000000"},
      {"0", "10000", "0100000000"}, {"0", "01110", "0000000000"},
      {"0", "11011", "0011101100"}, {"0", "01110", "1010100001"},
      {"0", "01111", "0100101111"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0000111101"}, {"0", "01010", "1011101000"},
      {"0", "01101", "1011110011"}, {"0", "01110", "0001011011"},
      {"0", "00000", "0000000100"}, {"0", "00101", "0110110000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01000", "0100011110"}, {"0", "01110", "0010110011"},
      {"0", "01011", "1110011101"}, {"0", "01110", "1110100110"},
      {"0", "10001", "1000000000"}, {"0", "01111", "0011001100"},
      {"0", "10100", "1110000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0011110001"}, {"0", "01111", "1001001000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "0100010111"},
      {"0", "01101", "0000100100"}, {"0", "01110", "0100111111"},
      {"0", "00001", "0001010101"}, {"0", "01110", "0101100100"},
      {"0", "10001", "0111111101"}, {"0", "01110", "0110000101"},
      {"0", "01110", "0110001011"}, {"0", "01110", "0110001110"},
      {"0", "01011", "0001110110"}, {"0", "01111", "0110010111"},
      {"0", "01111", "0110011001"}, {"0", "01111", "0110101000"},
      {"0", "01110", "0110101110"}, {"0", "11000", "0110100000"},
      {"0", "01110", "0111011001"}, {"0", "00100", "0011010001"},
      {"0", "00001", "1010001101"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0111110001"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1000001001"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000110111"},
      {"0", "01110", "0100001000"}, {"0", "01110", "1001100011"},
      {"0", "01111", "1001100110"}, {"0", "01101", "0100110101"},
      {"0", "01110", "1010001101"}, {"0", "00000", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "10000", "1110001000"},
      {"0", "01110", "1011001000"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1100010000"}, {"0", "01000", "0010001001"},
      {"0", "11000", "0110001011"}, {"0", "01110", "1100100000"},
      {"0", "01110", "1100110000"}, {"0", "01110", "1100110011"},
      {"0", "01110", "1100110101"}, {"0", "01101", "1101000011"},
      {"0", "01110", "1101101010"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1110000100"}, {"0", "01100", "1000011011"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111100000"},
      {"0", "01110", "1111101011"}, {"0", "01110", "1111101100"},
      {"0", "00010", "1010000000"}, {"0", "01110", "1111110100"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111101"},
      {"0", "01110", "1111111110"}, {"0", "01110", "1111111111"},
  };

  test_to_fp_from_rational(INT, RoundingMode::RTN, expected);
  test_to_fp_from_rational(NUM_DEC, RoundingMode::RTN, expected);
  test_to_fp_from_rational(DEN_DEC, RoundingMode::RTN, expected);
  test_to_fp_from_rational(DEC, RoundingMode::RTN, expected);
}

TEST_F(TestFp, fp_from_real_rat_str_rtp)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "01111", "0000000000"}, {"0", "01011", "1001100111"},
      {"0", "00000", "0000010001"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000001"}, {"0", "01011", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "00111", "0000000000"},
      {"0", "01101", "0000000000"}, {"0", "01100", "1001100111"},
      {"0", "01100", "0000000000"}, {"0", "00000", "0000000001"},
      {"0", "10010", "0100000000"}, {"0", "11000", "1111010000"},
      {"0", "01111", "0000000010"}, {"0", "01111", "0000001011"},
      {"0", "01110", "0000011111"}, {"0", "01010", "0101010110"},
      {"0", "01000", "0001000101"}, {"0", "01111", "0001011101"},
      {"0", "01001", "0001111000"}, {"0", "01110", "0101110101"},
      {"0", "01001", "0110011010"}, {"0", "01101", "1100000100"},
      {"0", "01111", "0001100111"}, {"0", "10001", "0110000000"},
      {"0", "01111", "0001110001"}, {"0", "01100", "1100110011"},
      {"0", "00011", "1110000001"}, {"0", "01110", "0010010111"},
      {"0", "00101", "0000011001"}, {"0", "01000", "1000001000"},
      {"0", "01111", "0110101001"}, {"0", "10010", "1000000000"},
      {"0", "10101", "1110000000"}, {"0", "01110", "1110110001"},
      {"0", "01110", "0011010001"}, {"0", "00000", "0110100001"},
      {"0", "00000", "0110100001"}, {"0", "01111", "0100101001"},
      {"0", "00000", "0110110011"}, {"0", "00000", "0110110100"},
      {"0", "01100", "1010101000"}, {"0", "01111", "0100111110"},
      {"0", "01110", "0000111110"}, {"0", "01100", "0001000101"},
      {"0", "10111", "0100110111"}, {"0", "00110", "0110110001"},
      {"0", "00101", "0110110001"}, {"0", "01111", "0110010000"},
      {"0", "01100", "0001110101"}, {"0", "01010", "0001111000"},
      {"0", "01111", "0110011000"}, {"0", "01111", "0110011001"},
      {"0", "01111", "0110100100"}, {"0", "01110", "0110101001"},
      {"0", "01110", "0111000010"}, {"0", "01111", "0111000110"},
      {"0", "01101", "0010101110"}, {"0", "01111", "1000101011"},
      {"0", "00001", "0100100000"}, {"0", "01100", "0100000010"},
      {"0", "01111", "1001001001"}, {"0", "01110", "1001001001"},
      {"0", "01111", "1001001001"}, {"0", "10000", "1001001001"},
      {"0", "01111", "1001001001"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1001111001"}, {"0", "00000", "0000011100"},
      {"0", "01100", "0101010110"}, {"0", "01100", "0101010110"},
      {"0", "01101", "0000000000"}, {"0", "01110", "1000100010"},
      {"0", "01100", "0110001111"}, {"0", "01011", "0001110111"},
      {"0", "00001", "0010101111"}, {"0", "01110", "1101000001"},
      {"0", "00101", "0111110111"}, {"0", "01110", "1110011100"},
      {"0", "10000", "0000000000"}, {"0", "01101", "1001100111"},
      {"0", "01100", "1001100111"}, {"0", "01111", "1001001000"},
      {"0", "01101", "1010000010"}, {"0", "00000", "0000000001"},
      {"0", "01011", "1010110001"}, {"0", "01110", "1011101110"},
      {"0", "01110", "0001111010"}, {"0", "01100", "1100110011"},
      {"0", "00000", "0000000001"}, {"0", "01100", "1101011011"},
      {"0", "01110", "1101011110"}, {"0", "01110", "1101111000"},
      {"0", "01101", "1101111101"}, {"0", "00000", "0000000010"},
      {"0", "01110", "1110010001"}, {"0", "10011", "1000000000"},
      {"0", "01100", "1110111110"}, {"0", "01101", "1111000010"},
      {"0", "01110", "1111000100"}, {"0", "01110", "1111001100"},
      {"0", "01011", "1111001101"}, {"0", "01110", "1001001110"},
      {"0", "00011", "0000001010"}, {"0", "01101", "1111100110"},
      {"0", "01110", "1111110001"}, {"0", "00000", "0000000001"},
      {"0", "01010", "1010110011"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0010110110"}, {"0", "00000", "0010110110"},
      {"0", "00000", "0000101111"}, {"0", "00000", "0000000101"},
      {"0", "01101", "0001101010"}, {"0", "01111", "0110011001"},
      {"0", "01101", "0011001101"}, {"0", "01111", "1000000000"},
      {"0", "00000", "0000000010"}, {"0", "01110", "1000000000"},
      {"0", "01110", "0011001101"}, {"0", "01010", "1110101111"},
      {"0", "01101", "0011001101"}, {"0", "01110", "0011101101"},
      {"0", "01110", "1000101010"}, {"0", "10000", "1001001001"},
      {"0", "01111", "1001001001"}, {"0", "01110", "1001001001"},
      {"0", "01110", "0100100101"}, {"0", "00000", "0000000001"},
      {"0", "01101", "0101010110"}, {"0", "01101", "0101010110"},
      {"0", "01101", "0101010110"}, {"0", "01110", "0101011011"},
      {"0", "01101", "0101111001"}, {"0", "01111", "0110011001"},
      {"0", "01101", "0110111100"}, {"0", "00110", "1101011100"},
      {"0", "11111", "0000000000"}, {"0", "11000", "0111010011"},
      {"0", "01101", "0111111111"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000001"}, {"0", "01110", "1000100001"},
      {"0", "01101", "1001000001"}, {"0", "01110", "1111111001"},
      {"0", "01110", "1001100111"}, {"0", "11110", "0011101100"},
      {"0", "00000", "0000000001"}, {"0", "01010", "0101010110"},
      {"0", "01110", "1010110110"}, {"0", "01101", "1011000100"},
      {"0", "01011", "0110010100"}, {"0", "01110", "1100000000"},
      {"0", "11111", "0000000000"}, {"0", "01110", "1101001111"},
      {"0", "00000", "0100111000"}, {"0", "01101", "1110000011"},
      {"0", "00000", "0000010001"}, {"0", "01110", "1111011011"},
      {"0", "01110", "1111100111"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1111111100"}, {"0", "01010", "0100000000"},
      {"0", "10000", "0100000000"}, {"0", "01110", "0000000001"},
      {"0", "11011", "0011101100"}, {"0", "01110", "1010100010"},
      {"0", "01111", "0100110000"}, {"0", "00000", "0000000001"},
      {"0", "01110", "0000111110"}, {"0", "01010", "1011101001"},
      {"0", "01101", "1011110100"}, {"0", "01110", "0001011100"},
      {"0", "00000", "0000000101"}, {"0", "00101", "0110110001"},
      {"0", "00000", "0000000001"}, {"0", "00000", "0000000001"},
      {"0", "01000", "0100011111"}, {"0", "01110", "0010110100"},
      {"0", "01011", "1110011110"}, {"0", "01110", "1110100111"},
      {"0", "10001", "1000000000"}, {"0", "01111", "0011001101"},
      {"0", "10100", "1110000000"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000001"}, {"0", "00000", "0000000001"},
      {"0", "01101", "0011110010"}, {"0", "01111", "1001001001"},
      {"0", "00000", "0000000001"}, {"0", "01110", "0100011000"},
      {"0", "01101", "0000100101"}, {"0", "01110", "0101000000"},
      {"0", "00001", "0001010110"}, {"0", "01110", "0101100101"},
      {"0", "10001", "0111111110"}, {"0", "01110", "0110000110"},
      {"0", "01110", "0110001100"}, {"0", "01110", "0110001111"},
      {"0", "01011", "0001110111"}, {"0", "01111", "0110011000"},
      {"0", "01111", "0110011010"}, {"0", "01111", "0110101001"},
      {"0", "01110", "0110101111"}, {"0", "11000", "0110100000"},
      {"0", "01110", "0111011010"}, {"0", "00100", "0011010010"},
      {"0", "00001", "1010001110"}, {"0", "00000", "0000000001"},
      {"0", "01110", "0111110010"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1000001010"}, {"0", "00000", "0000000010"},
      {"0", "00000", "0000000001"}, {"0", "01110", "1000111000"},
      {"0", "01110", "0100001001"}, {"0", "01110", "1001100100"},
      {"0", "01111", "1001100111"}, {"0", "01101", "0100110110"},
      {"0", "01110", "1010001110"}, {"0", "00000", "0000000001"},
      {"0", "01111", "0000000001"}, {"0", "10000", "1110001001"},
      {"0", "01110", "1011001001"}, {"0", "01110", "1011011100"},
      {"0", "01110", "1100010001"}, {"0", "01000", "0010001010"},
      {"0", "11000", "0110001100"}, {"0", "01110", "1100100001"},
      {"0", "01110", "1100110001"}, {"0", "01110", "1100110100"},
      {"0", "01110", "1100110110"}, {"0", "01101", "1101000100"},
      {"0", "01110", "1101101011"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1110000101"}, {"0", "01100", "1000011100"},
      {"0", "00000", "0000000001"}, {"0", "01110", "1110111011"},
      {"0", "01110", "1111010100"}, {"0", "01110", "1111100001"},
      {"0", "01110", "1111101100"}, {"0", "01110", "1111101101"},
      {"0", "00010", "1010000001"}, {"0", "01110", "1111110101"},
      {"0", "01110", "1111111110"}, {"0", "01110", "1111111110"},
      {"0", "01110", "1111111111"}, {"0", "01111", "0000000000"},
  };

  test_to_fp_from_rational(INT, RoundingMode::RTP, expected);
  test_to_fp_from_rational(NUM_DEC, RoundingMode::RTP, expected);
  test_to_fp_from_rational(DEN_DEC, RoundingMode::RTP, expected);
  test_to_fp_from_rational(DEC, RoundingMode::RTP, expected);
}

TEST_F(TestFp, fp_from_real_rat_str_rtz)
{
  std::vector<std::vector<const char *>> expected = {
      {"0", "01111", "0000000000"}, {"0", "01011", "1001100110"},
      {"0", "00000", "0000010000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01011", "0000000000"},
      {"0", "01110", "0000000000"}, {"0", "00111", "0000000000"},
      {"0", "01101", "0000000000"}, {"0", "01100", "1001100110"},
      {"0", "01100", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "10010", "0100000000"}, {"0", "11000", "1111010000"},
      {"0", "01111", "0000000001"}, {"0", "01111", "0000001010"},
      {"0", "01110", "0000011110"}, {"0", "01010", "0101010101"},
      {"0", "01000", "0001000100"}, {"0", "01111", "0001011100"},
      {"0", "01001", "0001110111"}, {"0", "01110", "0101110100"},
      {"0", "01001", "0110011001"}, {"0", "01101", "1100000011"},
      {"0", "01111", "0001100110"}, {"0", "10001", "0110000000"},
      {"0", "01111", "0001110000"}, {"0", "01100", "1100110010"},
      {"0", "00011", "1110000000"}, {"0", "01110", "0010010110"},
      {"0", "00101", "0000011000"}, {"0", "01000", "1000000111"},
      {"0", "01111", "0110101000"}, {"0", "10010", "1000000000"},
      {"0", "10101", "1110000000"}, {"0", "01110", "1110110000"},
      {"0", "01110", "0011010000"}, {"0", "00000", "0110100000"},
      {"0", "00000", "0110100000"}, {"0", "01111", "0100101000"},
      {"0", "00000", "0110110010"}, {"0", "00000", "0110110011"},
      {"0", "01100", "1010100111"}, {"0", "01111", "0100111101"},
      {"0", "01110", "0000111101"}, {"0", "01100", "0001000100"},
      {"0", "10111", "0100110111"}, {"0", "00110", "0110110000"},
      {"0", "00101", "0110110000"}, {"0", "01111", "0110001111"},
      {"0", "01100", "0001110100"}, {"0", "01010", "0001110111"},
      {"0", "01111", "0110010111"}, {"0", "01111", "0110011000"},
      {"0", "01111", "0110100011"}, {"0", "01110", "0110101000"},
      {"0", "01110", "0111000001"}, {"0", "01111", "0111000101"},
      {"0", "01101", "0010101101"}, {"0", "01111", "1000101010"},
      {"0", "00001", "0100011111"}, {"0", "01100", "0100000001"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1001111000"}, {"0", "00000", "0000011011"},
      {"0", "01100", "0101010101"}, {"0", "01100", "0101010101"},
      {"0", "01100", "1111111111"}, {"0", "01110", "1000100001"},
      {"0", "01100", "0110001110"}, {"0", "01011", "0001110110"},
      {"0", "00001", "0010101110"}, {"0", "01110", "1101000000"},
      {"0", "00101", "0111110110"}, {"0", "01110", "1110011011"},
      {"0", "10000", "0000000000"}, {"0", "01101", "1001100110"},
      {"0", "01100", "1001100110"}, {"0", "01111", "1001001000"},
      {"0", "01101", "1010000001"}, {"0", "00000", "0000000000"},
      {"0", "01011", "1010110000"}, {"0", "01110", "1011101101"},
      {"0", "01110", "0001111001"}, {"0", "01100", "1100110010"},
      {"0", "00000", "0000000000"}, {"0", "01100", "1101011010"},
      {"0", "01110", "1101011101"}, {"0", "01110", "1101110111"},
      {"0", "01101", "1101111100"}, {"0", "00000", "0000000001"},
      {"0", "01110", "1110010000"}, {"0", "10011", "1000000000"},
      {"0", "01100", "1110111101"}, {"0", "01101", "1111000001"},
      {"0", "01110", "1111000011"}, {"0", "01110", "1111001011"},
      {"0", "01011", "1111001100"}, {"0", "01110", "1001001101"},
      {"0", "00011", "0000001001"}, {"0", "01101", "1111100101"},
      {"0", "01110", "1111110000"}, {"0", "00000", "0000000000"},
      {"0", "01010", "1010110010"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0010110101"}, {"0", "00000", "0010110101"},
      {"0", "00000", "0000101110"}, {"0", "00000", "0000000100"},
      {"0", "01101", "0001101001"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0011001100"}, {"0", "01111", "1000000000"},
      {"0", "00000", "0000000001"}, {"0", "01110", "1000000000"},
      {"0", "01110", "0011001100"}, {"0", "01010", "1110101110"},
      {"0", "01101", "0011001100"}, {"0", "01110", "0011101100"},
      {"0", "01110", "1000101001"}, {"0", "10000", "1001001000"},
      {"0", "01111", "1001001000"}, {"0", "01110", "1001001000"},
      {"0", "01110", "0100100100"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0101010101"}, {"0", "01101", "0101010101"},
      {"0", "01101", "0101010101"}, {"0", "01110", "0101011010"},
      {"0", "01101", "0101111000"}, {"0", "01111", "0110011000"},
      {"0", "01101", "0110111011"}, {"0", "00110", "1101011011"},
      {"0", "11110", "1111111111"}, {"0", "11000", "0111010010"},
      {"0", "01101", "0111111110"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000100000"},
      {"0", "01101", "1001000000"}, {"0", "01110", "1111111000"},
      {"0", "01110", "1001100110"}, {"0", "11110", "0011101100"},
      {"0", "00000", "0000000000"}, {"0", "01010", "0101010101"},
      {"0", "01110", "1010110101"}, {"0", "01101", "1011000011"},
      {"0", "01011", "0110010011"}, {"0", "01110", "1011111111"},
      {"0", "11110", "1111111111"}, {"0", "01110", "1101001110"},
      {"0", "00000", "0100110111"}, {"0", "01101", "1110000010"},
      {"0", "00000", "0000010000"}, {"0", "01110", "1111011010"},
      {"0", "01110", "1111100110"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1111111011"}, {"0", "01010", "0100000000"},
      {"0", "10000", "0100000000"}, {"0", "01110", "0000000000"},
      {"0", "11011", "0011101100"}, {"0", "01110", "1010100001"},
      {"0", "01111", "0100101111"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0000111101"}, {"0", "01010", "1011101000"},
      {"0", "01101", "1011110011"}, {"0", "01110", "0001011011"},
      {"0", "00000", "0000000100"}, {"0", "00101", "0110110000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01000", "0100011110"}, {"0", "01110", "0010110011"},
      {"0", "01011", "1110011101"}, {"0", "01110", "1110100110"},
      {"0", "10001", "1000000000"}, {"0", "01111", "0011001100"},
      {"0", "10100", "1110000000"}, {"0", "00000", "0000000000"},
      {"0", "00000", "0000000000"}, {"0", "00000", "0000000000"},
      {"0", "01101", "0011110001"}, {"0", "01111", "1001001000"},
      {"0", "00000", "0000000000"}, {"0", "01110", "0100010111"},
      {"0", "01101", "0000100100"}, {"0", "01110", "0100111111"},
      {"0", "00001", "0001010101"}, {"0", "01110", "0101100100"},
      {"0", "10001", "0111111101"}, {"0", "01110", "0110000101"},
      {"0", "01110", "0110001011"}, {"0", "01110", "0110001110"},
      {"0", "01011", "0001110110"}, {"0", "01111", "0110010111"},
      {"0", "01111", "0110011001"}, {"0", "01111", "0110101000"},
      {"0", "01110", "0110101110"}, {"0", "11000", "0110100000"},
      {"0", "01110", "0111011001"}, {"0", "00100", "0011010001"},
      {"0", "00001", "1010001101"}, {"0", "00000", "0000000000"},
      {"0", "01110", "0111110001"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1000001001"}, {"0", "00000", "0000000001"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1000110111"},
      {"0", "01110", "0100001000"}, {"0", "01110", "1001100011"},
      {"0", "01111", "1001100110"}, {"0", "01101", "0100110101"},
      {"0", "01110", "1010001101"}, {"0", "00000", "0000000000"},
      {"0", "01111", "0000000000"}, {"0", "10000", "1110001000"},
      {"0", "01110", "1011001000"}, {"0", "01110", "1011011011"},
      {"0", "01110", "1100010000"}, {"0", "01000", "0010001001"},
      {"0", "11000", "0110001011"}, {"0", "01110", "1100100000"},
      {"0", "01110", "1100110000"}, {"0", "01110", "1100110011"},
      {"0", "01110", "1100110101"}, {"0", "01101", "1101000011"},
      {"0", "01110", "1101101010"}, {"0", "00000", "0000000000"},
      {"0", "01110", "1110000100"}, {"0", "01100", "1000011011"},
      {"0", "00000", "0000000000"}, {"0", "01110", "1110111010"},
      {"0", "01110", "1111010011"}, {"0", "01110", "1111100000"},
      {"0", "01110", "1111101011"}, {"0", "01110", "1111101100"},
      {"0", "00010", "1010000000"}, {"0", "01110", "1111110100"},
      {"0", "01110", "1111111101"}, {"0", "01110", "1111111101"},
      {"0", "01110", "1111111110"}, {"0", "01110", "1111111111"},
  };

  test_to_fp_from_rational(INT, RoundingMode::RTZ, expected);
  test_to_fp_from_rational(NUM_DEC, RoundingMode::RTZ, expected);
  test_to_fp_from_rational(DEN_DEC, RoundingMode::RTZ, expected);
  test_to_fp_from_rational(DEC, RoundingMode::RTZ, expected);
}

TEST_F(TestFp, op_eq)
{
  //// format different
  ASSERT_FALSE(FloatingPoint::fpzero(d_fp16, false)
               == FloatingPoint::fpzero(d_nm.mk_fp_type(6, 8), false));
  ASSERT_TRUE(FloatingPoint::fpzero(d_fp16, false)
              != FloatingPoint::fpzero(d_nm.mk_fp_type(6, 8), false));

  ASSERT_FALSE(FloatingPointMPFR::fpzero(d_fp16, false)
               == FloatingPointMPFR::fpzero(d_nm.mk_fp_type(6, 8), false));
  ASSERT_TRUE(FloatingPointMPFR::fpzero(d_fp16, false)
              != FloatingPointMPFR::fpzero(d_nm.mk_fp_type(6, 8), false));

  //// same format
  ASSERT_EQ(FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"),
            FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"));
  ASSERT_EQ(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"));

  ASSERT_NE(FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-0.1"),
            FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"));
  ASSERT_NE(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-0.1"),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1"));

  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"));
  ASSERT_EQ(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPointMPFR::from_real(
          d_nm, d_fp16, RoundingMode::RNE, "-5.17777"));

  ASSERT_NE(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RTZ, "-5.17777"));
  ASSERT_NE(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPointMPFR::from_real(
          d_nm, d_fp16, RoundingMode::RTZ, "-5.17777"));

  ASSERT_NE(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-8.8"));
  ASSERT_NE(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777"),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-8.8"));

  ASSERT_EQ(FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27"),
            FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27"));
  ASSERT_EQ(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27"),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27"));

  ASSERT_NE(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-12.11328125"),
      FloatingPoint::from_real(
          d_nm, d_fp16, RoundingMode::RNA, "-12.11328125"));
  ASSERT_NE(FloatingPointMPFR::from_real(
                d_nm, d_fp16, RoundingMode::RNE, "-12.11328125"),
            FloatingPointMPFR::from_real(
                d_nm, d_fp16, RoundingMode::RNA, "-12.11328125"));

  ASSERT_EQ(FloatingPoint::fpnan(d_fp16), FloatingPoint::fpnan(d_fp16));
  ASSERT_EQ(FloatingPointMPFR::fpnan(d_fp16), FloatingPointMPFR::fpnan(d_fp16));

  ASSERT_EQ(FloatingPoint::fpinf(d_fp16, true),
            FloatingPoint::fpinf(d_fp16, true));
  ASSERT_EQ(FloatingPointMPFR::fpinf(d_fp16, true),
            FloatingPointMPFR::fpinf(d_fp16, true));

  ASSERT_EQ(FloatingPoint::fpinf(d_fp16, false),
            FloatingPoint::fpinf(d_fp16, false));
  ASSERT_EQ(FloatingPointMPFR::fpinf(d_fp16, false),
            FloatingPointMPFR::fpinf(d_fp16, false));

  ASSERT_NE(FloatingPoint::fpinf(d_fp16, true),
            FloatingPoint::fpinf(d_fp16, false));
  ASSERT_NE(FloatingPointMPFR::fpinf(d_fp16, true),
            FloatingPointMPFR::fpinf(d_fp16, false));

  ASSERT_EQ(FloatingPoint::fpzero(d_fp16, false),
            FloatingPoint::fpzero(d_fp16, false));
  ASSERT_EQ(FloatingPointMPFR::fpzero(d_fp16, false),
            FloatingPointMPFR::fpzero(d_fp16, false));

  ASSERT_NE(FloatingPoint::fpzero(d_fp16, true),
            FloatingPoint::fpzero(d_fp16, false));
  ASSERT_NE(FloatingPointMPFR::fpzero(d_fp16, true),
            FloatingPointMPFR::fpzero(d_fp16, false));

  ASSERT_NE(FloatingPoint::fpzero(d_fp16, true),
            FloatingPoint::fpinf(d_fp16, true));
  ASSERT_NE(FloatingPointMPFR::fpzero(d_fp16, true),
            FloatingPointMPFR::fpinf(d_fp16, true));

  ASSERT_NE(FloatingPoint::fpnan(d_fp16), FloatingPoint::fpinf(d_fp16, false));
  ASSERT_NE(FloatingPointMPFR::fpnan(d_fp16),
            FloatingPointMPFR::fpinf(d_fp16, false));

  for (const auto &type : d_all_formats)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      FloatingPoint fp1(type, bv1);
      FloatingPoint fp2(type, bv2);
      ASSERT_EQ(bv1 == bv2, fp1 == fp2);
      ASSERT_EQ(bv1 != bv2, fp1 != fp2);
      FloatingPointMPFR fp_mpfr1(type, bv1);
      FloatingPointMPFR fp_mpfr2(type, bv2);
      ASSERT_EQ(bv1 == bv2, fp1 == fp2);
      ASSERT_EQ(bv1 != bv2, fp1 != fp2);
    }
  }
}

TEST_F(TestFp, to_real_str)
{
  ASSERT_EQ(FloatingPoint::fpnan(d_fp16).to_real_str(),
            "(fp.to_real (_ NaN 5 11))");
  ASSERT_EQ(FloatingPoint::fpinf(d_fp16, false).to_real_str(),
            "(fp.to_real (_ +oo 5 11))");
  ASSERT_EQ(FloatingPoint::fpinf(d_fp16, true).to_real_str(),
            "(fp.to_real (_ -oo 5 11))");
  ASSERT_EQ(FloatingPoint::fpzero(d_fp16, false).to_real_str(), "0.0");
  ASSERT_EQ(FloatingPoint::fpzero(d_fp16, true).to_real_str(), "0.0");
  ASSERT_NE(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-12.11328125")
          .to_real_str(),
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNA, "-12.11328125")
          .to_real_str());

  ASSERT_EQ(FloatingPointMPFR::fpnan(d_fp16).to_real_str(),
            "(fp.to_real (_ NaN 5 11))");
  ASSERT_EQ(FloatingPointMPFR::fpinf(d_fp16, false).to_real_str(),
            "(fp.to_real (_ +oo 5 11))");
  ASSERT_EQ(FloatingPointMPFR::fpinf(d_fp16, true).to_real_str(),
            "(fp.to_real (_ -oo 5 11))");
  ASSERT_EQ(FloatingPointMPFR::fpzero(d_fp16, false).to_real_str(), "0.0");
  ASSERT_EQ(FloatingPointMPFR::fpzero(d_fp16, true).to_real_str(), "0.0");
  ASSERT_NE(FloatingPointMPFR::from_real(
                d_nm, d_fp16, RoundingMode::RNE, "-12.11328125")
                .to_real_str(),
            FloatingPointMPFR::from_real(
                d_nm, d_fp16, RoundingMode::RNA, "-12.11328125")
                .to_real_str());

  ASSERT_EQ(FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1")
                .to_real_str(),
            FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1")
                .to_real_str());
  ASSERT_EQ(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-0.1")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-0.1")
          .to_real_str());
  ASSERT_NE(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-0.1")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "0.1")
          .to_real_str());

  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777")
          .to_real_str());
  ASSERT_NE(
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-5.17777")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RTZ, "-5.17777")
          .to_real_str());

  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-8.8")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "-8.8")
          .to_real_str());

  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27")
          .to_real_str(),
      FloatingPointMPFR::from_real(d_nm, d_fp16, RoundingMode::RNE, "3.27")
          .to_real_str());

  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNE, "-12.11328125")
          .to_real_str(),
      FloatingPointMPFR::from_real(
          d_nm, d_fp16, RoundingMode::RNE, "-12.11328125")
          .to_real_str());
  ASSERT_EQ(
      FloatingPoint::from_real(d_nm, d_fp16, RoundingMode::RNA, "-12.11328125")
          .to_real_str(),
      FloatingPointMPFR::from_real(
          d_nm, d_fp16, RoundingMode::RNA, "-12.11328125")
          .to_real_str());

  // comprehensive tests for all values in Float16
  auto fun = [this](const BitVector &bvexp, const BitVector &bvsig) {
    {
      BitVector bv = BitVector::mk_false().ibvconcat(bvexp).ibvconcat(bvsig);
      FloatingPoint fp(d_fp16, bv);
      FloatingPointMPFR fp_mpfr(d_fp16, bv);
      if (fp.to_real_str() != fp_mpfr.to_real_str())
      {
        std::cout << "bv: " << bv << std::endl;
        std::cout << "fp: " << fp << std::endl;
        std::cout << "fp_mpfr: " << fp_mpfr << std::endl;
      }
      ASSERT_EQ(fp.to_real_str(), fp_mpfr.to_real_str());
    }
    {
      BitVector bv = BitVector::mk_true().ibvconcat(bvexp).ibvconcat(bvsig);
      FloatingPoint fp(d_fp16, bv);
      FloatingPointMPFR fp_mpfr(d_fp16, bv);
      if (fp.to_real_str() != fp_mpfr.to_real_str())
      {
        std::cout << "bv: " << bv << std::endl;
        std::cout << "fp: " << fp << std::endl;
        std::cout << "fp_mpfr: " << fp_mpfr << std::endl;
      }
      ASSERT_EQ(fp.to_real_str(), fp_mpfr.to_real_str());
    }
  };
  test_for_float16(fun);

  // random tests for Float32, Float64, Float128
  for (const auto &type : d_formats_32_128)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv = BitVector(bv_size, *d_rng);
      FloatingPoint fp(type, bv);
      FloatingPointMPFR fp_mpfr(type, bv);
      if (fp.to_real_str() != fp_mpfr.to_real_str())
      {
        std::cout << bv << std::endl;
        std::cout << "fp: " << fp << std::endl;
        std::cout << "fp_mpfr: " << fp_mpfr << std::endl;
      }
      ASSERT_EQ(fp.to_real_str(), fp_mpfr.to_real_str());
    }
  }
}

TEST_F(TestFp, assignment)
{
  for (size_t i = 0; i < N_TESTS; ++i)
  {
    Type type1 = pick_type(d_all_formats);
    Type type2 = pick_type(d_all_formats);
    BitVector bv1(type1.fp_ieee_bv_size(), *d_rng);
    BitVector bv2(type2.fp_ieee_bv_size(), *d_rng);

    {
      FloatingPoint fp1(type1, bv1);
      FloatingPoint fp2(type2, bv2);
      FloatingPoint _fp1 = fp1;
      FloatingPoint _fp2 = fp2;
      ASSERT_EQ(fp1, _fp1);
      ASSERT_EQ(fp2, _fp2);
      _fp1 = fp2;
      ASSERT_EQ(fp2, _fp1);
      _fp2 = fp1;
      ASSERT_EQ(fp1, _fp2);
      _fp1 = fp1;
      _fp2 = fp2;
      ASSERT_EQ(fp1, _fp1);
      ASSERT_EQ(fp2, _fp2);
    }
    {
      FloatingPointMPFR fp1(type1, bv1);
      FloatingPointMPFR fp2(type2, bv2);
      FloatingPointMPFR _fp1 = fp1;
      FloatingPointMPFR _fp2 = fp2;
      ASSERT_EQ(fp1, _fp1);
      ASSERT_EQ(fp2, _fp2);
      _fp1 = fp2;
      ASSERT_EQ(fp2, _fp1);
      _fp2 = fp1;
      if (fp1 != _fp2)
      {
        std::cout << "bv1: " << bv1 << std::endl;
        std::cout << "bv2: " << bv2 << std::endl;
        std::cout << "fp1: " << fp1 << std::endl;
        std::cout << "fp2: " << fp2 << std::endl;
        std::cout << "_fp1: " << _fp1 << std::endl;
        std::cout << "_fp2: " << _fp2 << std::endl;
      }
      ASSERT_EQ(fp1, _fp2);
      _fp1 = fp1;
      _fp2 = fp2;
      ASSERT_EQ(fp1, _fp1);
      ASSERT_EQ(fp2, _fp2);
    }
  }
}

TEST_F(TestFp, lt)
{
  for (const auto &type : d_all_formats)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      FloatingPoint fp1(type, bv1);
      FloatingPoint fp2(type, bv2);
      FloatingPointMPFR fp_mpfr1(type, bv1);
      FloatingPointMPFR fp_mpfr2(type, bv2);
      ASSERT_EQ(fp1.fplt(fp2), fp_mpfr1.fplt(fp_mpfr2));
    }
  }
}
TEST_F(TestFp, leq)
{
  for (const auto &type : d_all_formats)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      FloatingPoint fp1(type, bv1);
      FloatingPoint fp2(type, bv2);
      FloatingPointMPFR fp_mpfr1(type, bv1);
      FloatingPointMPFR fp_mpfr2(type, bv2);
      ASSERT_EQ(fp1.fple(fp2), fp_mpfr1.fple(fp_mpfr2));
    }
  }
}
TEST_F(TestFp, gt)
{
  for (const auto &type : d_all_formats)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      FloatingPoint fp1(type, bv1);
      FloatingPoint fp2(type, bv2);
      FloatingPointMPFR fp_mpfr1(type, bv1);
      FloatingPointMPFR fp_mpfr2(type, bv2);
      ASSERT_EQ(fp1.fpgt(fp2), fp_mpfr1.fpgt(fp_mpfr2));
    }
  }
}
TEST_F(TestFp, geq)
{
  for (const auto &type : d_all_formats)
  {
    uint64_t bv_size = type.fp_ieee_bv_size();
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv1 = BitVector(bv_size, *d_rng);
      BitVector bv2 = BitVector(bv_size, *d_rng);
      FloatingPoint fp1(type, bv1);
      FloatingPoint fp2(type, bv2);
      FloatingPointMPFR fp_mpfr1(type, bv1);
      FloatingPointMPFR fp_mpfr2(type, bv2);
      ASSERT_EQ(fp1.fpge(fp2), fp_mpfr1.fpge(fp_mpfr2));
    }
  }
}
TEST_F(TestFp, abs) { TEST_UNARY(abs); }
TEST_F(TestFp, neg) { TEST_UNARY(neg); }
TEST_F(TestFp, sqrt) { TEST_UNARY_RM(sqrt); }
TEST_F(TestFp, rti) { TEST_UNARY_RM(rti); }
TEST_F(TestFp, rem) { TEST_BINARY(rem); }
TEST_F(TestFp, add) { TEST_BINARY_RM(add); }
TEST_F(TestFp, mul) { TEST_BINARY_RM(mul); }
#ifdef NDEBUG
// SymFPU fails with an assertion failure (see issue #164) but agrees with
// MPFR on all tests for release builds without assertions.
TEST_F(TestFp, div) { TEST_BINARY_RM(div); }
TEST_F(TestFp, fma) { TEST_TERNARY_RM(fma); }

TEST_F(TestFp, chained_rem)
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
TEST_F(TestFp, chained_bin_rm)
{
  TEST_CHAINED_BINARY_RM(add, mul);
#ifdef NDEBUG
  // SymFPU may fail with an assertion failure (see issue #164) but agrees with
  // MPFR on all tests for release builds without assertions.
  // (a / b) rem c, (a rem b) / c
  TEST_CHAINED_BINARY_RM(add, div);
#endif
}
TEST_F(TestFp, chained_un_bin_rm)
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
TEST_F(TestFp, chained_un_rm_bin_rm)
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
#endif

}  // namespace bzla::test
