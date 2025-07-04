/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/floating_point.h"

#include <gmp.h>
#include <gmpxx.h>

#include "node/node_manager.h"
#include "util/gmp_utils.h"
#include "util/hash.h"

namespace {
int64_t
ieee_exp_max(uint64_t exp_size)
{
  assert(exp_size < 63);
  // TODO we need to make this robust wrt to underlying impl (64 vs 32 bit)
  uint64_t one = 1;
  return (one << (exp_size - one)) - one;
}
int64_t
ieee_exp_min(uint64_t exp_size)
{
  return 1 - ieee_exp_max(exp_size);
}
int64_t
mpfr_exp_max(uint64_t exp_size)
{
  return ieee_exp_max(exp_size) + 1;
}
int64_t
mpfr_exp_min(uint64_t exp_size, uint64_t sig_size)
{
  return ieee_exp_min(exp_size) - sig_size + 2;
}
int64_t
exp_bias(uint64_t exp_size)
{
  return ieee_exp_max(exp_size);
}
mpfr_exp_t
exp2mpfr(uint64_t exp_size, uint64_t exp)
{
  // Remove bias and account for MPFR's hidden bit.
  return exp - exp_bias(exp_size) + 1;
}
int64_t
mpfr2exp(uint64_t exp_size, mpfr_exp_t exp)
{
  // Add bias and remove MPFR's hidden bit.
  return exp + exp_bias(exp_size) - 1;
}
void
mpfr_set_eminmax_for_format(uint64_t exp_size, uint64_t sig_size)
{
  // TODO make robust with respect to MPFR implementation size of exponent
  assert(sizeof(mpfr_exp_t) == sizeof(uint64_t));
  mpfr_set_emax(mpfr_exp_max(exp_size));
  mpfr_set_emin(mpfr_exp_min(exp_size, sig_size));
}
void
mpfr_set_eminmax_for_format(bzla::Type type)
{
  mpfr_set_eminmax_for_format(type.fp_exp_size(), type.fp_sig_size());
}
void
mpfr_reset_format()
{
  mpfr_set_emax(mpfr_get_emax_max());
  mpfr_set_emin(mpfr_get_emin_min());
}
int64_t
sub_threshold(uint64_t exp_size)
{
  return -static_cast<int64_t>(exp_bias(exp_size) - 1);
}
mpfr_rnd_t
rm2mpfr(bzla::RoundingMode rm)
{
  switch (rm)
  {
    case bzla::RoundingMode::RNA: return MPFR_RNDNA;
    case bzla::RoundingMode::RNE: return MPFR_RNDN;
    case bzla::RoundingMode::RTN: return MPFR_RNDD;
    case bzla::RoundingMode::RTP: return MPFR_RNDU;
    default: assert(rm == bzla::RoundingMode::RTZ); return MPFR_RNDZ;
  }
}
}  // namespace

namespace bzla {
using namespace node;

/* --- FloatingPoint public static ------------------------------------------ */

void
FloatingPoint::ieee_bv_as_bvs(const Type &type,
                              const BitVector &bv,
                              BitVector &sign,
                              BitVector &exp,
                              BitVector &sig)
{
  uint32_t bw     = bv.size();
  uint32_t bw_exp = type.fp_exp_size();
  uint32_t bw_sig = type.fp_sig_size();
  sign            = bv.bvextract(bw - 1, bw - 1);
  exp             = bv.bvextract(bw - 2, bw - 1 - bw_exp);
  sig             = bv.bvextract(bw_sig - 2, 0);
}

FloatingPoint
FloatingPoint::from_real(NodeManager &nm,
                         const Type &type,
                         const RoundingMode rm,
                         const std::string &real)
{
  (void) nm;
  FloatingPoint res(type);
  mpfr_set_eminmax_for_format(type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  mpq_t mpq;
  util::mpq_from_dec_string(mpq, real.c_str());
  int32_t i = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_set_q, res.d_mpfr, mpq);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, res.d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set_q(res.d_mpfr, mpq, rm_mpfr);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_check_range((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
    }
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  mpq_clear(mpq);
  return res;
}

FloatingPoint
FloatingPoint::from_rational(NodeManager &nm,
                             const Type &type,
                             const RoundingMode rm,
                             const std::string &num,
                             const std::string &den)
{
  (void) nm;
  FloatingPoint res(type);
  mpfr_set_eminmax_for_format(type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  mpq_t mpq;
  util::mpq_from_rat_string(mpq, num.c_str(), den.c_str());
  int32_t i = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_set_q, res.d_mpfr, mpq);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, res.d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set_q(res.d_mpfr, mpq, rm_mpfr);
    if (mpfr_regular_p(res.d_mpfr))
    {
      i = mpfr_check_range((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
    }
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  mpq_clear(mpq);
  return res;
}

FloatingPoint
FloatingPoint::fpzero(const Type &type, bool sign)
{
  FloatingPoint res(type);
  mpfr_set_zero(res.d_mpfr, sign ? -1 : 1);
  return res;
}

FloatingPoint
FloatingPoint::fpinf(const Type &type, bool sign)
{
  FloatingPoint res(type);
  mpfr_set_inf(res.d_mpfr, sign ? -1 : 1);
  return res;
}

FloatingPoint
FloatingPoint::fpnan(const Type &type)
{
  FloatingPoint res(type);
  mpfr_set_nan(res.d_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fpfp(NodeManager &nm,
                    const BitVector &sign,
                    const BitVector &exp,
                    const BitVector &sig)
{
  FloatingPoint res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                    sign.bvconcat(exp).ibvconcat(sig));
  return res;
}

/* --- FloatingPoint public ------------------------------------------------- */

FloatingPoint::FloatingPoint(const Type& type) : d_type(type)
{
  mpfr_reset_format();
  // MPFR precision includes the hidden bit (not the sign bit), we can use
  // significand size (which is also +1 because of the sign bit).
  mpfr_init2(d_mpfr, type.fp_sig_size());
}

FloatingPoint::FloatingPoint(const Type &type, const BitVector &bv)
    : FloatingPoint(type)
{
  assert(type.fp_ieee_bv_size() == bv.size());

  mpfr_set_eminmax_for_format(d_type);

  BitVector bvsign, bvexp, bvsig;
  ieee_bv_as_bvs(type, bv, bvsign, bvexp, bvsig);
  int32_t sign = bvsign.is_true() ? -1 : 1;
  if (bvexp.is_ones())
  {
    if (bvsig.is_zero())
    {
      mpfr_set_inf(d_mpfr, sign);
    }
    else
    {
      mpfr_set_nan(d_mpfr);
    }
  }
  else if (bvexp.is_zero())
  {
    if (bvsig.is_zero())
    {
      mpfr_set_zero(d_mpfr, sign);
    }
    else
    {
      // subnormals
      std::string sign_str = sign < 0 ? "-" : "";
      std::string s        = sign_str + "0." + bvsig.str();
      mpfr_set_str(d_mpfr, s.c_str(), 2, MPFR_RNDN);
      mpfr_exp_t exp = mpfr_get_exp(d_mpfr);
      mpfr_set_exp(d_mpfr, exp + exp2mpfr(bvexp.size(), 0));
      assert(fpissubnormal());
    }
  }
  else
  {
    // normals
    std::string sign_str = sign < 0 ? "-" : "";
    std::string s        = sign_str + "1." + bvsig.str();
    mpfr_set_str(d_mpfr, s.c_str(), 2, MPFR_RNDN);
    mpfr_set_exp(d_mpfr, exp2mpfr(bvexp.size(), bvexp.to_uint64()));
  }
}

FloatingPoint::FloatingPoint(const Type &type,
                             const RoundingMode rm,
                             const FloatingPoint &fp)
    : FloatingPoint(type)
{
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_set, d_mpfr, fp.d_mpfr);
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set(d_mpfr, fp.d_mpfr, rm_mpfr);
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_check_range((mpfr_ptr) d_mpfr, i, rm_mpfr);
    }
  }
  mpfr_subnormalize((mpfr_ptr) d_mpfr, i, rm_mpfr);
}

FloatingPoint::FloatingPoint(const Type &type,
                             const RoundingMode rm,
                             const BitVector &bv,
                             bool sign)
    : FloatingPoint(type)
{
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  mpz_class bv_mpz   = bv.to_mpz(sign);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_set_z, d_mpfr, bv_mpz.get_mpz_t());
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_round_nearest_away(mpfr_check_range, d_mpfr, i);
    }
  }
  else
  {
    i = mpfr_set_z(d_mpfr, bv_mpz.get_mpz_t(), rm_mpfr);
    if (mpfr_regular_p(d_mpfr))
    {
      i = mpfr_check_range((mpfr_ptr) d_mpfr, i, rm_mpfr);
    }
  }
  mpfr_subnormalize((mpfr_ptr) d_mpfr, i, rm_mpfr);
}

FloatingPoint::FloatingPoint(const FloatingPoint& other)
    : FloatingPoint(other.d_type)
{
  mpfr_set_eminmax_for_format(d_type);
  mpfr_set(d_mpfr, other.d_mpfr, MPFR_RNDN);
}

FloatingPoint&
FloatingPoint::operator=(const FloatingPoint& other)
{
  assert(!other.d_type.is_null());
  if (d_type.is_null())
  {
    mpfr_reset_format();
    // MPFR precision includes the hidden bit (not the sign bit), we can use
    // significand size (which is also +1 because of the sign bit).
    mpfr_init2(d_mpfr, other.d_type.fp_sig_size());
  }
  else if (d_type.fp_sig_size() != other.d_type.fp_sig_size())
  {
    mpfr_set_prec(d_mpfr, other.d_type.fp_sig_size());
  }
  d_type = other.d_type;
  mpfr_set_eminmax_for_format(d_type);
  mpfr_set(d_mpfr, other.d_mpfr, MPFR_RNDN);
  return *this;
}

FloatingPoint::~FloatingPoint() { mpfr_clear(d_mpfr); }

uint64_t
FloatingPoint::get_exponent_size() const
{
  return d_type.fp_exp_size();
}

uint64_t
FloatingPoint::get_significand_size() const
{
  return d_type.fp_sig_size();
}

const Type&
FloatingPoint::type() const
{
  return d_type;
}

size_t
FloatingPoint::hash() const
{
  int32_t sign = fpisneg() ? -1 : 1;

  uint64_t i, j = 0, n, res = 0;
  uint64_t x, p0, p1;

  uint64_t exp_size = d_type.fp_exp_size();
  uint64_t sig_size = d_type.fp_sig_size();
  res               = (exp_size + sig_size) * util::hash::s_hash_primes[j++];

  if (fpisinf())
  {
    return util::hash::fnv1a_64(
        std::hash<std::string>{}(sign < 0 ? "-oo" : "+oo"), res);
  }
  if (fpisnan())
  {
    return util::hash::fnv1a_64(std::hash<std::string>{}("NaN"), res);
  }
  if (fpiszero())
  {
    return util::hash::fnv1a_64(
        std::hash<std::string>{}(sign < 0 ? "-zero" : "+zero") * sign, res);
  }

  // limbs for significand
  uint64_t nlimbs = (sig_size + mp_bits_per_limb - 1) / mp_bits_per_limb;

  // hash for significand, least significant limb is at index 0
  mp_limb_t limb;
  for (i = 0, j = 1, n = nlimbs; i < n; ++i)
  {
    p0 = s_hash_primes[j++];
    if (j == util::hash::s_n_primes) j = 0;
    p1 = util::hash::s_hash_primes[j++];
    if (j == util::hash::s_n_primes) j = 0;
    limb = d_mpfr->_mpfr_d[i];
    if (mp_bits_per_limb == 64)
    {
      uint64_t lo = limb;
      uint64_t hi = (limb >> 32);
      x           = lo ^ res;
      x           = ((x >> 16) ^ x) * p0;
      x           = ((x >> 16) ^ x) * p1;
      x           = ((x >> 16) ^ x);
      p0          = s_hash_primes[j++];
      if (j == util::hash::s_n_primes) j = 0;
      p1 = s_hash_primes[j++];
      if (j == util::hash::s_n_primes) j = 0;
      x = x ^ hi;
    }
    else
    {
      assert(mp_bits_per_limb == 32);
      x = res ^ limb;
    }
    x   = ((x >> 16) ^ x) * p0;
    x   = ((x >> 16) ^ x) * p1;
    res = ((x >> 16) ^ x);
  }
  res = util::hash::fnv1a_64(
      ((sign >> 16) ^ sign) * util::hash::s_hash_primes[j], res);
  res = util::hash::fnv1a_64(static_cast<uint64_t>(mpfr_get_exp(d_mpfr)), res);
  return res;
}

std::string
FloatingPoint::str(uint8_t bv_format) const
{
  assert(bv_format == 2 || bv_format == 10);
  std::stringstream ss;
  BitVector sign, exp, sig;
  FloatingPoint::ieee_bv_as_bvs(d_type, as_bv(), sign, exp, sig);
  ss << "(fp ";
  if (bv_format == 2)
  {
    ss << "#b" << sign.str(2) << " #b" << exp.str(2) << " #b" << sig.str(2);
  }
  else
  {
    ss << "(_ bv" << sign.str(10) << " 1) (_ bv" << exp.str(10) << " "
       << exp.size() << ") (_ bv" << sig.str(10) << " " << sig.size() << ")";
  }
  ss << ")";
  return ss.str();
}

std::string
FloatingPoint::to_real_str() const
{
  if (fpisnan())
  {
    return "(fp.to_real (_ NaN " + std::to_string(d_type.fp_exp_size()) + " "
           + std::to_string(d_type.fp_sig_size()) + "))";
  }

  if (fpisinf())
  {
    if (fpisneg())
    {
      return "(fp.to_real (_ -oo " + std::to_string(d_type.fp_exp_size()) + " "
             + std::to_string(d_type.fp_sig_size()) + "))";
    }
    return "(fp.to_real (_ +oo " + std::to_string(d_type.fp_exp_size()) + " "
           + std::to_string(d_type.fp_sig_size()) + "))";
  }
  if (fpiszero())
  {
    return "0.0";
  }

  mpq_class mpq;
  mpfr_get_q(mpq.get_mpq_t(), d_mpfr);
  std::string res = mpq.get_str();
  if (res.find('/') == std::string::npos && res.find('.') == std::string::npos)
  {
    res += ".0";
  }
  return res;
}

bool
FloatingPoint::operator==(const FloatingPoint &other) const
{
  if (d_type != other.d_type)
  {
    return false;
  }
  bool isnan1 = fpisnan();
  bool isnan2 = other.fpisnan();
  if (isnan1 || isnan2)
  {
    return isnan1 == isnan2;
  }
  bool iszero1 = fpiszero();
  bool iszero2 = other.fpiszero();
  if (iszero1 || iszero2)
  {
    return iszero1 == iszero2 && fpisneg() == other.fpisneg();
  }
  return mpfr_equal_p(d_mpfr, other.d_mpfr) > 0;
}

bool
FloatingPoint::operator!=(const FloatingPoint &other) const
{
  return !(*this == other);
}

bool
FloatingPoint::fpiszero() const
{
  return mpfr_zero_p(d_mpfr) > 0;
}

bool
FloatingPoint::fpisnormal() const
{
  return mpfr_regular_p(d_mpfr)
         && mpfr_get_exp(d_mpfr) > sub_threshold(d_type.fp_exp_size());
}

bool
FloatingPoint::fpissubnormal() const
{
  return mpfr_regular_p(d_mpfr)
         && mpfr_get_exp(d_mpfr) <= sub_threshold(d_type.fp_exp_size());
}

bool
FloatingPoint::fpisnan() const
{
  return mpfr_nan_p(d_mpfr) > 0;
}

bool
FloatingPoint::fpisinf() const
{
  return mpfr_inf_p(d_mpfr) > 0;
}

bool
FloatingPoint::fpisneg() const
{
  return !fpisnan() && mpfr_signbit(d_mpfr) != 0;
}

bool
FloatingPoint::fpispos() const
{
  return !fpisnan() && mpfr_signbit(d_mpfr) == 0;
}

bool
FloatingPoint::fpeq(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  return mpfr_equal_p(d_mpfr, fp.d_mpfr);
}

bool
FloatingPoint::fplt(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  return mpfr_less_p(d_mpfr, fp.d_mpfr);
}

bool
FloatingPoint::fple(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  return mpfr_lessequal_p(d_mpfr, fp.d_mpfr);
}

bool
FloatingPoint::fpgt(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  return mpfr_greater_p(d_mpfr, fp.d_mpfr);
}

bool
FloatingPoint::fpge(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  return mpfr_greaterequal_p(d_mpfr, fp.d_mpfr);
}

FloatingPoint
FloatingPoint::fpmin(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_min(res.d_mpfr, d_mpfr, fp.d_mpfr, MPFR_RNDN);
  return res;
}

FloatingPoint
FloatingPoint::fpmax(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_max(res.d_mpfr, d_mpfr, fp.d_mpfr, MPFR_RNDN);
  return res;
}

FloatingPoint
FloatingPoint::fpabs() const
{
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_abs(res.d_mpfr, d_mpfr, MPFR_RNDN);
  return res;
}

FloatingPoint
FloatingPoint::fpneg() const
{
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_neg(res.d_mpfr, d_mpfr, MPFR_RNDN);
  return res;
}

FloatingPoint
FloatingPoint::fpsqrt(const RoundingMode rm) const
{
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_sqrt, res.d_mpfr, d_mpfr);
  }
  else
  {
    i = mpfr_sqrt(res.d_mpfr, d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fprti(const RoundingMode rm) const
{
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round(res.d_mpfr, d_mpfr);
  }
  else
  {
    i = mpfr_rint(res.d_mpfr, d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fprem(const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  int32_t i = mpfr_remainder(res.d_mpfr, d_mpfr, fp.d_mpfr, MPFR_RNDN);
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, MPFR_RNDN);
  return res;
}

FloatingPoint
FloatingPoint::fpadd(const RoundingMode rm, const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_add, res.d_mpfr, d_mpfr, fp.d_mpfr);
  }
  else
  {
    i = mpfr_add(res.d_mpfr, d_mpfr, fp.d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fpmul(const RoundingMode rm, const FloatingPoint &fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_mul, res.d_mpfr, d_mpfr, fp.d_mpfr);
  }
  else
  {
    i = mpfr_mul(res.d_mpfr, d_mpfr, fp.d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fpdiv(const RoundingMode rm, const FloatingPoint& fp) const
{
  assert(d_type == fp.d_type);
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(mpfr_div, res.d_mpfr, d_mpfr, fp.d_mpfr);
  }
  else
  {
    i = mpfr_div(res.d_mpfr, d_mpfr, fp.d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

FloatingPoint
FloatingPoint::fpfma(const RoundingMode rm,
                     const FloatingPoint& fp0,
                     const FloatingPoint& fp1) const
{
  assert(d_type == fp0.d_type);
  assert(d_type == fp1.d_type);
  FloatingPoint res(d_type);
  mpfr_set_eminmax_for_format(d_type);
  mpfr_rnd_t rm_mpfr = rm2mpfr(rm);
  int32_t i          = 0;
  if (rm == RoundingMode::RNA)
  {
    i = mpfr_round_nearest_away(
        mpfr_fma, res.d_mpfr, d_mpfr, fp0.d_mpfr, fp1.d_mpfr);
  }
  else
  {
    i = mpfr_fma(res.d_mpfr, d_mpfr, fp0.d_mpfr, fp1.d_mpfr, rm_mpfr);
  }
  mpfr_subnormalize((mpfr_ptr) res.d_mpfr, i, rm_mpfr);
  return res;
}

BitVector
FloatingPoint::as_bv() const
{
  uint64_t exp_size = d_type.fp_exp_size();
  uint64_t sig_size = d_type.fp_sig_size();
  if (fpisnan())
  {
    // We use single representation for NaN, the same as SymFPU uses.
    return BitVector::mk_false()
        .ibvconcat(BitVector::mk_ones(exp_size))
        .ibvconcat(BitVector::mk_min_signed(sig_size - 1));
  }
  uint64_t sign = fpisneg();
  if (fpiszero())
  {
    return sign ? BitVector::mk_min_signed(exp_size + sig_size)
                : BitVector::mk_zero(exp_size + sig_size);
  }
  BitVector bvsign = sign ? BitVector::mk_true() : BitVector::mk_false();
  if (fpisinf())
  {
    return bvsign.ibvconcat(BitVector::mk_ones(exp_size))
        .ibvconcat(BitVector::mk_zero(sig_size - 1));
  }
  mpfr_set_eminmax_for_format(exp_size, sig_size);
  mpfr_exp_t exp;
  char* str = mpfr_get_str(0, &exp, 2, sig_size, d_mpfr, MPFR_RNDN);
  assert(strlen(str) > 1 && (str[0] != '-' || strlen(str) > 2));
  assert(strlen(str[0] == '-' ? str + 1 : str) == sig_size);
  BitVector bvexp = BitVector::mk_zero(exp_size);
  BitVector bvsig;
  if (!fpissubnormal())
  {
    std::string sig_str = str[0] == '-' ? str + 2 : str + 1;
    bvexp               = BitVector::from_si(exp_size,
                               static_cast<int64_t>(mpfr2exp(exp_size, exp)));
    bvsig               = BitVector(sig_size - 1, sig_str);
  }
  else
  {
    std::string sig_str = str[0] == '-' ? str + 1 : str;
    sig_str.resize(sig_size - 1);
    assert(mpfr2exp(exp_size, exp) <= 0);
    bvsig =
        BitVector(sig_size - 1, sig_str, 2).ibvshr(-mpfr2exp(exp_size, exp));
  }
  mpfr_free_str(str);
  assert(bvexp.size() == exp_size);
  assert(bvsig.size() == sig_size - 1);
  return bvsign.ibvconcat(bvexp).ibvconcat(bvsig);
}

/* -------------------------------------------------------------------------- */

std::ostream &
operator<<(std::ostream &out, const FloatingPoint &fp)
{
  out << fp.str();
  return out;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla

namespace std {

size_t
hash<bzla::FloatingPoint>::operator()(const bzla::FloatingPoint &fp) const
{
  return fp.hash();
}

}  // namespace std
