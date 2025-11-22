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

using namespace node;

/* -------------------------------------------------------------------------- */

TEST_F(TestFp, hash)
{
  std::unordered_map<size_t, std::vector<FloatingPoint>> occs;
  std::unordered_map<size_t, std::vector<FloatingPointSymFPU>> occs_symfpu;
  for (uint64_t i = 0; i < (1u << 16); ++i)
  {
    BitVector bv = BitVector::from_ui(16, i);
    {
      FloatingPoint fp(d_fp16.first, d_fp16.second, bv);
      auto [it, inserted] =
          occs.emplace(fp.hash(), std::vector<FloatingPoint>{fp});
      if (!inserted) it->second.push_back(fp);
    }
    {
      FloatingPointSymFPU fp(d_typefp16, bv);
      auto [it, inserted] =
          occs_symfpu.emplace(fp.hash(), std::vector<FloatingPointSymFPU>{fp});
      if (!inserted) it->second.push_back(fp);
    }
  }
  size_t max = 0, n_nan = ((1u << 10) - 1) * 2;
  std::unordered_set<uint64_t> occs_cnt;
  for (const auto& p : occs)
  {
    if (p.second.size() > max) max = p.second.size();
    occs_cnt.insert(p.second.size());
  }
  // one entry > 1 for NaN, rest should be unique
  ASSERT_EQ(occs_cnt.size(), 2);
  ASSERT_TRUE(occs_cnt.find(1) != occs_cnt.end());
  ASSERT_EQ(max, n_nan);

  size_t max_symfpu = 0;
  std::unordered_set<uint64_t> occs_symfpu_cnt;
  for (const auto& p : occs_symfpu)
  {
    if (p.second.size() > max_symfpu) max_symfpu = p.second.size();
    occs_symfpu_cnt.insert(p.second.size());
  }
  // one entry > 1 for NaN, rest should be unique
  ASSERT_EQ(occs_symfpu_cnt.size(), 2);
  ASSERT_TRUE(occs_symfpu_cnt.find(1) != occs_cnt.end());
  ASSERT_EQ(max_symfpu, n_nan);
}

TEST_F(TestFp, fp_is_value)
{
  for (const auto& f : d_all_formats)
  {
    Type type = d_nm.mk_fp_type(f.first, f.second);
    {
      FloatingPoint fp = FloatingPoint::fpzero(f.first, f.second, false);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());

      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_TRUE(fp_value.fpiszero());
      ASSERT_TRUE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointSymFPU fp_symfpu = FloatingPointSymFPU::fpzero(type, false);
      ASSERT_TRUE(fp_symfpu.fpiszero());
      ASSERT_TRUE(fp_symfpu.fpispos());
      ASSERT_FALSE(fp_symfpu.fpisneg());
      ASSERT_FALSE(fp_symfpu.fpisinf());
      ASSERT_FALSE(fp_symfpu.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpzero(f.first, f.second, true);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_TRUE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_TRUE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointSymFPU fp_symfpu = FloatingPointSymFPU::fpzero(type, true);
      ASSERT_TRUE(fp_symfpu.fpiszero());
      ASSERT_FALSE(fp_symfpu.fpispos());
      ASSERT_TRUE(fp_symfpu.fpisneg());
      ASSERT_FALSE(fp_symfpu.fpisinf());
      ASSERT_FALSE(fp_symfpu.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpinf(f.first, f.second, false);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_TRUE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_TRUE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointSymFPU fp_symfpu = FloatingPointSymFPU::fpinf(type, false);
      ASSERT_FALSE(fp_symfpu.fpiszero());
      ASSERT_TRUE(fp_symfpu.fpispos());
      ASSERT_FALSE(fp_symfpu.fpisneg());
      ASSERT_TRUE(fp_symfpu.fpisinf());
      ASSERT_FALSE(fp_symfpu.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpinf(f.first, f.second, true);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_TRUE(fp_value.fpisneg());
      ASSERT_TRUE(fp_value.fpisinf());
      ASSERT_FALSE(fp_value.fpisnan());

      FloatingPointSymFPU fp_symfpu = FloatingPointSymFPU::fpinf(type, true);
      ASSERT_FALSE(fp_symfpu.fpiszero());
      ASSERT_FALSE(fp_symfpu.fpispos());
      ASSERT_TRUE(fp_symfpu.fpisneg());
      ASSERT_TRUE(fp_symfpu.fpisinf());
      ASSERT_FALSE(fp_symfpu.fpisnan());
    }
    {
      FloatingPoint fp = FloatingPoint::fpnan(f.first, f.second);
      Node value       = d_nm.mk_value(fp);
      ASSERT_TRUE(value.is_value());
      FloatingPoint fp_value = value.value<FloatingPoint>();
      ASSERT_FALSE(fp_value.fpiszero());
      ASSERT_FALSE(fp_value.fpispos());
      ASSERT_FALSE(fp_value.fpisneg());
      ASSERT_FALSE(fp_value.fpisinf());
      ASSERT_TRUE(fp_value.fpisnan());

      FloatingPointSymFPU fp_symfpu = FloatingPointSymFPU::fpnan(type);
      ASSERT_FALSE(fp_symfpu.fpiszero());
      ASSERT_FALSE(fp_symfpu.fpispos());
      ASSERT_FALSE(fp_symfpu.fpisneg());
      ASSERT_FALSE(fp_symfpu.fpisinf());
      ASSERT_TRUE(fp_symfpu.fpisnan());
    }
  }
}

TEST_F(TestFp, assignment)
{
  for (size_t i = 0; i < N_TESTS; ++i)
  {
    FpFormat format1 = pick_format(d_all_formats);
    FpFormat format2 = pick_format(d_all_formats);
    Type type1       = d_nm.mk_fp_type(format1.first, format1.second);
    Type type2       = d_nm.mk_fp_type(format2.first, format2.second);
    BitVector bv1(format1.first + format1.second, *d_rng);
    BitVector bv2(format2.first + format2.second, *d_rng);

    {
      FloatingPoint fp1(format1.first, format1.second, bv1);
      FloatingPoint fp2(format2.first, format2.second, bv2);
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
      FloatingPointSymFPU fp1(type1, bv1);
      FloatingPointSymFPU fp2(type2, bv2);
      FloatingPointSymFPU _fp1 = fp1;
      FloatingPointSymFPU _fp2 = fp2;
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
  }
}

TEST_F(TestFp, str_as_bv)
{
  auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {
    uint64_t exp_size = bvexp.size();
    uint64_t sig_size = bvsig.size() + 1;

    Type type_sign = d_nm.mk_bv_type(1);
    Type type_exp  = d_nm.mk_bv_type(exp_size);
    Type type_sig  = d_nm.mk_bv_type(sig_size - 1);
    Type type_fp   = d_nm.mk_fp_type(exp_size, sig_size);

    for (const auto& bv :
         {BitVector::mk_false().bvconcat(bvexp).ibvconcat(bvsig),
          BitVector::mk_true().bvconcat(bvexp).ibvconcat(bvsig)})
    {
      BitVector bvsign =
          bv.msb() ? BitVector::mk_true() : BitVector::mk_false();
      // test constructor and str()
      FloatingPoint fp(exp_size, sig_size, bv);
      FloatingPointSymFPU fp_symfpu(type_fp, bv);
      if (fp.fpisnan())
      {
        ASSERT_TRUE(fp == FloatingPoint::fpnan(exp_size, sig_size));
        std::string str = "(fp #b" + BitVector::mk_false().str() + " #b"
                          + BitVector::mk_ones(exp_size).str() + " #b"
                          + BitVector::mk_min_signed(sig_size - 1).str() + ")";
        ASSERT_EQ(fp.str(), str);
        ASSERT_TRUE(fp_symfpu == FloatingPointSymFPU::fpnan(type_fp));
        ASSERT_EQ(fp_symfpu.str(), str);
      }
      else
      {
        std::string str = "(fp #b" + bvsign.str() + " #b" + bvexp.str() + " #b"
                          + bvsig.str() + ")";
        ASSERT_EQ(fp.str(), str);
        ASSERT_EQ(fp_symfpu.str(), str);
      }
      ASSERT_EQ(fp.str(), fp_symfpu.str());

      // test as_bv() via fpfp() and Node
      FloatingPoint fpfp = FloatingPoint::fpfp(
          bv.msb() ? BitVector::mk_true() : BitVector::mk_false(),
          bvexp,
          bvsig);
      ASSERT_EQ(fp.str(), fpfp.str());
      Node node_fp    = d_nm.mk_value(fpfp);
      fpfp            = node_fp.value<FloatingPoint>();
      BitVector as_bv = fpfp.as_bv();
      BitVector as_bvsign, as_bvexp, as_bvsig;
      FloatingPointSymFPU::ieee_bv_as_bvs(
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

      // only via fpfp() for SymFPU implementation
      FloatingPointSymFPU fpfp_symfpu =
          FloatingPointSymFPU::fpfp(d_nm, bvsign, bvexp, bvsig);
      ASSERT_EQ(fp.str(), fpfp_symfpu.str());
      BitVector as_bv_symfpu = fpfp_symfpu.as_bv();
      BitVector as_bvsign_symfpu, as_bvexp_symfpu, as_bvsig_symfpu;
      FloatingPointSymFPU::ieee_bv_as_bvs(type_fp,
                                          as_bv_symfpu,
                                          as_bvsign_symfpu,
                                          as_bvexp_symfpu,
                                          as_bvsig_symfpu);
      if (bvexp.is_ones() && !bvsig.is_zero())
      {
        // we use a single nan representation
        ASSERT_EQ(
            as_bv_symfpu,
            BitVector(bv.size(),
                      "0" + BitVector::mk_ones(exp_size).str()
                          + BitVector::mk_min_signed(sig_size - 1).str()));
      }
      else
      {
        ASSERT_EQ(as_bv_symfpu.compare(bv), 0);
      }
      ASSERT_EQ(as_bv_symfpu.compare(as_bvsign_symfpu.bvconcat(as_bvexp_symfpu)
                                         .ibvconcat(as_bvsig_symfpu)),
                0);
    }
  };

  test_for_float16(fun);
  test_for_formats(d_formats_32_128, N_TESTS, fun);
}

TEST_F(TestFp, to_real_str)
{
  ASSERT_EQ(FloatingPoint::fpnan(d_fp16.first, d_fp16.second).to_real_str(),
            "(fp.to_real (_ NaN 5 11))");
  ASSERT_EQ(
      FloatingPoint::fpinf(d_fp16.first, d_fp16.second, false).to_real_str(),
      "(fp.to_real (_ +oo 5 11))");
  ASSERT_EQ(
      FloatingPoint::fpinf(d_fp16.first, d_fp16.second, true).to_real_str(),
      "(fp.to_real (_ -oo 5 11))");
  ASSERT_EQ(
      FloatingPoint::fpzero(d_fp16.first, d_fp16.second, false).to_real_str(),
      "0.0");
  ASSERT_EQ(
      FloatingPoint::fpzero(d_fp16.first, d_fp16.second, true).to_real_str(),
      "0.0");
  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-12.11328125")
                .to_real_str(),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNA, "-12.11328125")
                .to_real_str());

  ASSERT_EQ(FloatingPointSymFPU::fpnan(d_typefp16).to_real_str(),
            "(fp.to_real (_ NaN 5 11))");
  ASSERT_EQ(FloatingPointSymFPU::fpinf(d_typefp16, false).to_real_str(),
            "(fp.to_real (_ +oo 5 11))");
  ASSERT_EQ(FloatingPointSymFPU::fpinf(d_typefp16, true).to_real_str(),
            "(fp.to_real (_ -oo 5 11))");
  ASSERT_EQ(FloatingPointSymFPU::fpzero(d_typefp16, false).to_real_str(),
            "0.0");
  ASSERT_EQ(FloatingPointSymFPU::fpzero(d_typefp16, true).to_real_str(), "0.0");
  ASSERT_NE(FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-12.11328125")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNA, "-12.11328125")
                .to_real_str());

  ASSERT_EQ(
      FloatingPoint::from_real(
          d_fp16.first, d_fp16.second, RoundingMode::RNE, "0.1")
          .to_real_str(),
      FloatingPointSymFPU::from_real(d_nm, d_typefp16, RoundingMode::RNE, "0.1")
          .to_real_str());
  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-0.1")
                .to_real_str(),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-0.1")
                .to_real_str());
  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-0.1")
                .to_real_str(),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "0.1")
                .to_real_str());

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-5.17777")
                .to_real_str());
  ASSERT_NE(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-5.17777")
                .to_real_str(),
            FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RTZ, "-5.17777")
                .to_real_str());

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-8.8")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-8.8")
                .to_real_str());

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "3.27")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "3.27")
                .to_real_str());

  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNE, "-12.11328125")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNE, "-12.11328125")
                .to_real_str());
  ASSERT_EQ(FloatingPoint::from_real(
                d_fp16.first, d_fp16.second, RoundingMode::RNA, "-12.11328125")
                .to_real_str(),
            FloatingPointSymFPU::from_real(
                d_nm, d_typefp16, RoundingMode::RNA, "-12.11328125")
                .to_real_str());

  // comprehensive tests for all values in Float16
  auto fun = [this](const BitVector& bvexp, const BitVector& bvsig) {
    {
      BitVector bv = BitVector::mk_false().ibvconcat(bvexp).ibvconcat(bvsig);
      FloatingPoint fp(d_fp16.first, d_fp16.second, bv);
      FloatingPointSymFPU fp_symfpu(d_typefp16, bv);
      ASSERT_EQ(fp.to_real_str(), fp_symfpu.to_real_str());
    }
    {
      BitVector bv = BitVector::mk_true().ibvconcat(bvexp).ibvconcat(bvsig);
      FloatingPoint fp(d_fp16.first, d_fp16.second, bv);
      FloatingPointSymFPU fp_symfpu(d_typefp16, bv);
      ASSERT_EQ(fp.to_real_str(), fp_symfpu.to_real_str());
    }
  };
  test_for_float16(fun);

  // random tests for Float32, Float64, Float128
  for (const auto& f : d_formats_32_128)
  {
    uint64_t bv_size = f.first + f.second;
    Type type        = d_nm.mk_fp_type(f.first, f.second);
    for (uint32_t i = 0; i < N_TESTS; ++i)
    {
      BitVector bv = BitVector(bv_size, *d_rng);
      FloatingPoint fp(f.first, f.second, bv);
      FloatingPointSymFPU fp_symfpu(type, bv);
      ASSERT_EQ(fp.to_real_str(), fp_symfpu.to_real_str());
    }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
