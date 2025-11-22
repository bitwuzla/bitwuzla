/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2019 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <sys/types.h>

#include <cstdint>

#include "bv/bitvector.h"
#include "node/node_manager.h"
#include "rng/rng.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/floating_point_symfpu.h"
#include "solver/fp/symfpu_nm.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace node;

/* -------------------------------------------------------------------------- */

class TestFp : public TestCommon
{
  using FpFormat = std::pair<uint64_t, uint64_t>;

  TestFp() : snm(d_nm) {}

 protected:
  static constexpr uint32_t N_TESTS = 1000;

  void SetUp() override
  {
    TestCommon::SetUp();
    d_rng.reset(new RNG(1234));
    d_fp16     = {5, 11};
    d_fp32     = {8, 24};
    d_fp64     = {11, 53};
    d_fp128    = {15, 113};
    d_typefp16 = d_nm.mk_fp_type(5, 11);
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

  FpFormat pick_format(const std::vector<FpFormat>& formats) const
  {
    return d_rng->pick_from_set<std::vector<FpFormat>, FpFormat>(formats);
  }

  bool bv_is_fpnan(uint64_t exp_size,
                   uint64_t sig_size,
                   const BitVector& bv) const
  {
    BitVector bvsign, bvexp, bvsig;
    FloatingPoint::ieee_bv_as_bvs(exp_size, sig_size, bv, bvsign, bvexp, bvsig);
    return bvexp.is_ones() && !bvsig.is_zero();
  }

  void test_for_format(
      uint64_t exp_size,
      uint64_t sig_size,
      std::function<void(const BitVector& bvexp, const BitVector& bvsig)> fun);

  void test_for_float16(
      std::function<void(const BitVector&, const BitVector&)> fun);

  void test_for_formats(
      const std::vector<FpFormat>& formats,
      uint64_t n_tests,
      std::function<void(const BitVector&, const BitVector&)> fun);

  NodeManager d_nm;
  fp::SymFpuNM snm;

  std::unique_ptr<RNG> d_rng;

  FpFormat d_fp16;
  FpFormat d_fp32;
  FpFormat d_fp64;
  FpFormat d_fp128;

  Type d_typefp16;

  std::vector<FpFormat> d_all_formats;
  std::vector<FpFormat> d_formats_32_128;
  std::vector<RoundingMode> d_all_rms;
};

/* -------------------------------------------------------------------------- */

void
TestFp::test_for_format(
    uint64_t exp_size,
    uint64_t sig_size,
    std::function<void(const BitVector& bvexp, const BitVector& bvsig)> fun)
{
  sig_size -= 1;
  for (uint64_t i = 0; i < (1u << exp_size); ++i)
  {
    BitVector bvexp = BitVector::from_ui(exp_size, i);
    for (uint64_t j = 0; j < (1u << sig_size); ++j)
    {
      BitVector bvsig = BitVector::from_ui(sig_size, j);
      fun(bvexp, bvsig);
    }
  }
}

void
TestFp::test_for_float16(
    std::function<void(const BitVector& bvexp, const BitVector& bvsig)> fun)
{
  test_for_format(5, 11, fun);
}

void
TestFp::test_for_formats(
    const std::vector<FpFormat>& formats,
    uint64_t n_tests,
    std::function<void(const BitVector&, const BitVector&)> fun)
{
  for (const auto& f : formats)
  {
    uint64_t bvexp_size = f.first;
    uint64_t bvsig_size = f.second - 1;
    for (uint32_t i = 0; i < n_tests; ++i)
    {
      BitVector bvexp, bvsig;
      if (d_rng->flip_coin())
      {
        // normals
        bvexp = BitVector(bvexp_size,
                          *d_rng,
                          BitVector::mk_one(bvexp_size),
                          BitVector::mk_ones(bvexp_size).ibvdec());
        bvsig = BitVector(bvsig_size, *d_rng);
      }
      else
      {
        if (d_rng->pick_with_prob(600))
        {
          // zero exponent
          bvexp = BitVector::mk_zero(bvexp_size);
          bvsig = BitVector(bvsig_size, *d_rng);
        }
        else
        {
          // ones exponent
          bvexp = BitVector::mk_ones(bvexp_size);
          if (d_rng->pick_with_prob(100))
          {
            // inf
            bvsig = BitVector::mk_zero(bvsig_size);
          }
          else
          {
            // nan
            bvsig = BitVector(bvsig_size, *d_rng);
          }
        }
      }
      fun(bvexp, bvsig);
    }
  }
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::test
