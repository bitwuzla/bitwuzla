/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/floating_point_mpfr.h"

#include <gmp.h>
#include <gmpxx.h>

#include "node/node_manager.h"
#include "solver/fp/symfpu_nm.h"
#include "util/gmp_utils.h"

namespace {
uint64_t
exp_max(uint64_t exp_size)
{
  assert(exp_size < 64);
  // TODO we need to make this robust wrt to underlying impl (64 vs 32 bit)
  uint64_t one = 1;
  return one << (exp_size - one);
}
uint64_t
exp_bias(uint64_t exp_size)
{
  return exp_max(exp_size) - 1;
}
mpfr_exp_t
exp2mpfr(uint64_t exp_size, uint64_t exp)
{
  // Remove bias and account for MPFR's hidden bit.
  return exp - exp_bias(exp_size) + 1;
}
uint64_t
mpfr2exp(uint64_t exp_size, mpfr_exp_t exp)
{
  // Add bias and remove MPFR's hidden bit.
  return exp + exp_bias(exp_size) - 1;
}
void
mpfr_set_format(uint64_t exp_size, uint64_t sig_size)
{
  uint64_t emax = exp_max(exp_size);
  assert(emax < INT64_MAX);
  mpfr_set_emax(emax);
  mpfr_set_emin(-emax - sig_size + 2);
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

void
make_mpq_from_dec_string(mpq_t &res, std::string str)
{
  std::string::size_type decimal_point(str.find("."));
  mpq_init(res);

  if (decimal_point == std::string::npos)
  {
#ifndef NDEBUG
    assert(mpq_set_str(res, str.c_str(), 10) == 0);
#else
    mpq_set_str(res, str.c_str(), 10);
#endif
  }
  else
  {
    /* We represent nnn.mmm as nnnmmm / 10^(number of m). */
    str.erase(decimal_point, 1);
    mpz_t num, den;
    /* nnnmmm */
#ifndef NDEBUG
    assert(mpz_init_set_str(num, str.c_str(), 10) == 0);
#else
    mpz_init_set_str(num, str.c_str(), 10);
#endif
    /* 10^(number of m */
    mpz_init_set_ui(den, 10);
    mpz_pow_ui(den, den, str.size() - decimal_point);

    mpz_set(mpq_numref(res), num);
    mpz_set(mpq_denref(res), den);

    mpz_clear(num);
    mpz_clear(den);
  }

  mpq_canonicalize(res);
}

static void
make_mpq_from_rat_string(mpq_t &res, const char *str_num, const char *str_den)
{
  mpq_init(res);

  bool num_is_dec = std::string(str_num).find(".") != std::string::npos;
  bool den_is_dec = std::string(str_den).find(".") != std::string::npos;

  if (num_is_dec || den_is_dec)
  {
    mpq_t num, den;

    if (num_is_dec)
    {
      make_mpq_from_dec_string(num, str_num);
    }
    else
    {
      mpq_init(num);
      mpz_t znum;
      mpz_init_set_str(znum, str_num, 10);
      mpq_set_z(num, znum);
      mpz_clear(znum);
    }
    if (den_is_dec)
    {
      make_mpq_from_dec_string(den, str_den);
    }
    else
    {
      mpq_init(den);
      mpz_t zden;
      mpz_init_set_str(zden, str_den, 10);
      mpq_set_z(den, zden);
      mpz_clear(zden);
    }

    mpq_div(res, num, den);
    mpq_clear(num);
    mpq_clear(den);
  }
  else
  {
    mpz_t num, den;
    mpz_init_set_str(num, str_num, 10);
    mpz_init_set_str(den, str_den, 10);
    mpz_set(mpq_numref(res), num);
    mpz_set(mpq_denref(res), den);
    mpz_clear(num);
    mpz_clear(den);
  }

  mpq_canonicalize(res);
}

static void
make_mpq_from_ui(mpq_t &res, uint32_t n, uint32_t d)
{
  mpq_init(res);
  mpq_set_ui(res, n, d);
  mpq_canonicalize(res);
}

}  // namespace

namespace bzla {
using namespace node;

/* --- FloatingPointMPFR public static -------------------------------------- */

void
FloatingPointMPFR::ieee_bv_as_bvs(const Type &type,
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

FloatingPointMPFR
FloatingPointMPFR::from_real(NodeManager &nm,
                             const Type &type,
                             const RoundingMode rm,
                             const std::string &real)
{
  (void) nm;
  FloatingPointMPFR res(type);
  mpfr_set_str(res.d_mpfr, real.c_str(), 0, rm2mpfr(rm));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::from_rational(NodeManager &nm,
                                 const Type &type,
                                 const RoundingMode rm,
                                 const std::string &num,
                                 const std::string &den)
{
  (void) nm;
  FloatingPointMPFR res(type);
  mpq_t mpq;
  make_mpq_from_rat_string(mpq, num.c_str(), den.c_str());
  mpfr_set_q(res.d_mpfr, mpq, rm2mpfr(rm));
  mpq_clear(mpq);
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpzero(const Type &type, bool sign)
{
  FloatingPointMPFR res(type);
  mpfr_set_zero(res.d_mpfr, sign ? -1 : 1);
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpinf(const Type &type, bool sign)
{
  FloatingPointMPFR res(type);
  mpfr_set_inf(res.d_mpfr, sign ? -1 : 1);
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpnan(const Type &type)
{
  FloatingPointMPFR res(type);
  mpfr_set_nan(res.d_mpfr);
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpfp(NodeManager &nm,
                        const BitVector &sign,
                        const BitVector &exp,
                        const BitVector &sig)
{
  FloatingPointMPFR res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                        sign.bvconcat(exp).ibvconcat(sig));
  return res;
}

/* --- FloatingPointMPFR public --------------------------------------------- */

FloatingPointMPFR::FloatingPointMPFR(const Type &type)
{
  d_size.reset(new FloatingPointTypeInfo(type));
  // MPFR precision includes the hidden bit (not the sign bit), we can use
  // significand size (which is also +1 because of the sign bit).
  mpfr_init2(d_mpfr, type.fp_sig_size());
}

FloatingPointMPFR::FloatingPointMPFR(const FloatingPointTypeInfo &size)
    : FloatingPointMPFR(size.type())
{
}

// FloatingPointMPFR::FloatingPointMPFR(const Type &type, const UnpackedFloat
// &uf)
// {
//   d_size.reset(new FloatingPointTypeInfo(type));
//   // d_uf.reset(new UnpackedFloat(uf));
// }

FloatingPointMPFR::FloatingPointMPFR(const Type &type, const BitVector &bv)
    : FloatingPointMPFR(type)
{
  assert(type.fp_ieee_bv_size() == bv.size());
  mpfr_reset_format();

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
      std::string s        = sign_str + "0.1" + bvsig.str();
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

FloatingPointMPFR::FloatingPointMPFR(const Type &type,
                                     const RoundingMode rm,
                                     const FloatingPointMPFR &fp)
    : FloatingPointMPFR(type)
{
  // d_uf.reset(new UnpackedFloat(symfpu::convertFloatToFloat<fp::SymFpuTraits>(
  //     *fp.size(), *d_size, rm, *fp.unpacked())));
}

FloatingPointMPFR::FloatingPointMPFR(const Type &type,
                                     const RoundingMode rm,
                                     const BitVector &bv,
                                     bool sign)
    : FloatingPointMPFR(type)
{
  // if (sign)
  // {
  //   if (bv.size() == 1)
  //   {
  //     /* Note: We must copy the bv here, because 1) the corresponding
  //      * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
  //      * constructor is matched (const bool &val). */
  //     UnpackedFloat uf =
  //         symfpu::convertUBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv);
  //     /* We need special handling for bit-vectors of size one since symFPU
  //     does
  //      * not allow conversions from signed bit-vectors of size one.  */
  //     if (bv.is_one())
  //     {
  //       d_uf.reset(
  //           new UnpackedFloat(symfpu::negate<fp::SymFpuTraits>(*d_size,
  //           uf)));
  //     }
  //     else
  //     {
  //       d_uf.reset(new UnpackedFloat(uf));
  //     }
  //   }
  //   else
  //   {
  //     /* Note: We must copy the bv here, because 1) the corresponding
  //      * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
  //      * constructor is matched (const bool &val). */
  //     d_uf.reset(new UnpackedFloat(
  //         symfpu::convertSBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv)));
  //   }
  // }
  // else
  // {
  //   d_uf.reset(new UnpackedFloat(
  //       symfpu::convertUBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv)));
  // }
}

FloatingPointMPFR::FloatingPointMPFR(const FloatingPointMPFR &other)
    : FloatingPointMPFR(*other.size())
{
  // d_uf.reset(new UnpackedFloat(*other.unpacked()));
}

FloatingPointMPFR &
FloatingPointMPFR::operator=(const FloatingPointMPFR &other)

{
  d_size.reset(new FloatingPointTypeInfo(*other.size()));
  // d_uf.reset(new UnpackedFloat(*other.unpacked()));
  return *this;
}

FloatingPointMPFR::~FloatingPointMPFR() { mpfr_clear(d_mpfr); }

uint64_t
FloatingPointMPFR::get_exponent_size() const
{
  return d_size->exponentWidth();
}

uint64_t
FloatingPointMPFR::get_significand_size() const
{
  return d_size->significandWidth();
}

FloatingPointTypeInfo *
FloatingPointMPFR::size() const
{
  return d_size.get();
}

size_t
FloatingPointMPFR::hash() const
{
  uint32_t hash = 0;
  // hash += d_uf->getNaN() * s_hash_primes[0];
  // hash += d_uf->getInf() * s_hash_primes[1];
  // hash += d_uf->getZero() * s_hash_primes[2];
  // hash += d_uf->getSign() * s_hash_primes[3];
  // hash += d_uf->getExponent().getBv().hash() * s_hash_primes[4];
  // hash += d_uf->getSignificand().getBv().hash() * s_hash_primes[5];
  return hash;
}

std::string
FloatingPointMPFR::str(uint8_t bv_format) const
{
  assert(bv_format == 2 || bv_format == 10);
  std::stringstream ss;
  BitVector sign, exp, sig;
  FloatingPointMPFR::ieee_bv_as_bvs(d_size->type(), as_bv(), sign, exp, sig);
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
FloatingPointMPFR::to_real_str() const
{
  uint64_t size_exp = get_exponent_size();
  uint64_t size_sig = get_significand_size();

  if (fpisnan())
  {
    return "(fp.to_real (_ NaN " + std::to_string(size_exp) + " "
           + std::to_string(size_sig) + "))";
  }

  if (fpisinf())
  {
    if (fpisneg())
    {
      return "(fp.to_real (_ -oo " + std::to_string(size_exp) + " "
             + std::to_string(size_sig) + "))";
    }
    return "(fp.to_real (_ +oo " + std::to_string(size_exp) + " "
           + std::to_string(size_sig) + "))";
  }
  if (fpiszero())
  {
    return "0.0";
  }

  BitVector bv_sign, bv_exp, bv_sig;
  FloatingPointMPFR::ieee_bv_as_bvs(
      d_size->type(), as_bv(), bv_sign, bv_exp, bv_sig);

  // UnpackedFloat *uf  = unpacked();
  // const auto &uf_exp = uf->getExponent();
  // const auto &uf_sig = uf->getSignificand();
  //
  // const BitVector &exp = uf_exp.getBv();
  // mpz_class gmp_exp(exp.msb() ? -exp.bvneg().to_mpz() : exp.to_mpz());
  // gmp_exp -= util::uint64_to_mpz_class(size_sig - 1);
  //
  // mpz_class gmp_sig = uf_sig.getBv().to_mpz();
  // if (bv_sign.is_one())
  // {
  //   gmp_sig = -gmp_sig;
  // }
  //
  // mpz_class one(1);
  // mpq_class q_res;
  // if (gmp_exp >= 0)
  // {
  //   q_res = gmp_sig * (one << gmp_exp.get_ui());
  // }
  // else
  // {
  //   gmp_exp = -gmp_exp;
  //   q_res   = mpq_class(gmp_sig, one << gmp_exp.get_ui());
  // }
  // q_res.canonicalize();
  std::string res;  // = q_res.get_str(10);
  // if (res.find('/') == std::string::npos && res.find('.') ==
  // std::string::npos)
  // {
  //   res += ".0";
  // }
  return res;
}

bool
FloatingPointMPFR::operator==(const FloatingPointMPFR &other) const
{
  if (d_size->type() != other.d_size->type())
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
FloatingPointMPFR::operator!=(const FloatingPointMPFR &other) const
{
  return !(*this == other);
}

// UnpackedFloat *
// FloatingPointMPFR::unpacked() const
// {
//   return d_uf.get();
// }
//
// void
// FloatingPointMPFR::set_unpacked(const UnpackedFloat &uf)
// {
//   d_uf.reset(new UnpackedFloat(uf));
// }

bool
FloatingPointMPFR::fpiszero() const
{
  return mpfr_zero_p(d_mpfr) > 0;
}

bool
FloatingPointMPFR::fpisnormal() const
{
  return mpfr_regular_p(d_mpfr)
         && mpfr_get_exp(d_mpfr) > sub_threshold(d_size->type().fp_exp_size());
}

bool
FloatingPointMPFR::fpissubnormal() const
{
  return mpfr_regular_p(d_mpfr)
         && mpfr_get_exp(d_mpfr) <= sub_threshold(d_size->type().fp_exp_size());
}

bool
FloatingPointMPFR::fpisnan() const
{
  return mpfr_nan_p(d_mpfr) > 0;
}

bool
FloatingPointMPFR::fpisinf() const
{
  return mpfr_inf_p(d_mpfr) > 0;
}

bool
FloatingPointMPFR::fpisneg() const
{
  return !fpisnan() && mpfr_signbit(d_mpfr) != 0;
}

bool
FloatingPointMPFR::fpispos() const
{
  return !fpisnan() && mpfr_signbit(d_mpfr) == 0;
}

bool
FloatingPointMPFR::fpeq(const FloatingPointMPFR &fp) const
{
  // return symfpu::smtlibEqual<fp::SymFpuTraits>(*d_size, *d_uf,
  // *fp.unpacked());
  return false;
}

bool
FloatingPointMPFR::fplt(const FloatingPointMPFR &fp) const
{
  // return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked());
  return false;
}

bool
FloatingPointMPFR::fple(const FloatingPointMPFR &fp) const
{
  // return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
  //     *d_size, *d_uf, *fp.unpacked());
  return false;
}

bool
FloatingPointMPFR::fpgt(const FloatingPointMPFR &fp) const
{
  // return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *fp.unpacked(), *d_uf);
  return false;
}

bool
FloatingPointMPFR::fpge(const FloatingPointMPFR &fp) const
{
  // return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
  //     *d_size, *fp.unpacked(), *d_uf);
  return false;
}

FloatingPointMPFR
FloatingPointMPFR::fpabs() const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(
  //     symfpu::absolute<fp::SymFpuTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpneg() const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(
  //     new UnpackedFloat(symfpu::negate<fp::SymFpuTraits>(*res.size(),
  //     *d_uf)));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpsqrt(const RoundingMode rm) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(
  //     symfpu::sqrt<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fprti(const RoundingMode rm) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(
  //     symfpu::roundToIntegral<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fprem(const FloatingPointMPFR &fp) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(
  //     symfpu::remainder<fp::SymFpuTraits>(*res.size(), *d_uf,
  //     *fp.unpacked())));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpadd(const RoundingMode rm,
                         const FloatingPointMPFR &fp) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(symfpu::add<fp::SymFpuTraits>(
  //     *res.size(), rm, *d_uf, *fp.unpacked(), true)));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpmul(const RoundingMode rm,
                         const FloatingPointMPFR &fp) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(symfpu::multiply<fp::SymFpuTraits>(
  //     *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpdiv(const RoundingMode rm,
                         const FloatingPointMPFR &fp) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(symfpu::divide<fp::SymFpuTraits>(
  //     *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPointMPFR
FloatingPointMPFR::fpfma(const RoundingMode rm,
                         const FloatingPointMPFR &fp0,
                         const FloatingPointMPFR &fp1) const
{
  FloatingPointMPFR res(*d_size);
  // res.d_uf.reset(new UnpackedFloat(symfpu::fma<fp::SymFpuTraits>(
  //     *res.size(), rm, *d_uf, *fp0.unpacked(), *fp1.unpacked())));
  return res;
}

BitVector
FloatingPointMPFR::as_bv() const
{
  uint64_t exp_size = d_size->type().fp_exp_size();
  uint64_t sig_size = d_size->type().fp_sig_size();
  if (fpisnan())
  {
    // We use single representation for NaN, same as SymFPU uses.
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
  mpfr_set_format(exp_size, sig_size);
  mpfr_exp_t exp;
  char *str = mpfr_get_str(0, &exp, 2, sig_size, d_mpfr, MPFR_RNDN);
  assert(strlen(str) > 1 && (str[0] != '-' || strlen(str) > 2));
  assert(strlen(str[0] == '-' ? str + 1 : str) == sig_size);
  std::string sig_str = str[0] == '-' ? str + 2 : str + 1;
  BitVector bvexp     = BitVector::mk_zero(exp_size);
  BitVector bvsig;
  if (!fpissubnormal())
  {
    bvexp = BitVector::from_si(exp_size,
                               static_cast<int64_t>(mpfr2exp(exp_size, exp)));
    bvsig = BitVector(sig_size - 1, sig_str);
  }
  else
  {
    std::string s = std::string(sub_threshold(exp_size) - exp, '0') + sig_str;
    s.resize(sig_size - 1);
    bvsig = BitVector(sig_size - 1, s, 2);
  }
  mpfr_free_str(str);
  assert(bvexp.size() == exp_size);
  assert(bvsig.size() == sig_size - 1);
  return bvsign.ibvconcat(bvexp).ibvconcat(bvsig);
}

/* --- FloatingPointMPFR private -------------------------------------------- */

FloatingPointMPFR
FloatingPointMPFR::from_unpacked(NodeManager &nm,
                                 const BitVector &sign,
                                 const BitVector &exp,
                                 const BitVector &sig)
{
  // FloatingPointMPFR res(nm.mk_fp_type(exp.size(), sig.size() + 1),
  //                   UnpackedFloat(sign.is_one(), exp, sig));
  // return res;
}

FloatingPointMPFR
FloatingPointMPFR::convert_from_rational_aux(NodeManager &nm,
                                             const Type &type,
                                             const RoundingMode rm,
                                             const char *num,
                                             const char *den)
{
  assert(num);

  mpq_t r;
  if (den == nullptr)
  {
    make_mpq_from_dec_string(r, num);
  }
  else
  {
    make_mpq_from_rat_string(r, num, den);
  }

  int32_t sgn = mpq_sgn(r);
  if (sgn == 0)
  {
    mpq_clear(r);
    return FloatingPointMPFR::fpzero(type, false);
  }

  /* r = abs(r) */
  if (sgn < 0)
  {
    mpq_neg(r, r);
  }

  /* Exponent ---------------------------------------------------------- */

  mpq_t tmp_exp;
  mpz_t iexp, inc;
  make_mpq_from_ui(tmp_exp, 1, 1);
  mpz_init_set_ui(iexp, 0);
  mpz_init_set_ui(inc, 1);

  int32_t cmp = mpq_cmp(r, tmp_exp);
  if (cmp != 0)
  {
    if (cmp < 0)
    {
      while (mpq_cmp(r, tmp_exp) < 0)
      {
        mpz_sub(iexp, iexp, inc);
        mpq_div_2exp(tmp_exp, tmp_exp, 1);
      }
    }
    else
    {
      while (mpq_cmp(r, tmp_exp) >= 0)
      {
        mpz_add(iexp, iexp, inc);
        mpq_mul_2exp(tmp_exp, tmp_exp, 1);
      }
      mpz_sub(iexp, iexp, inc);
      mpq_div_2exp(tmp_exp, tmp_exp, 1);
    }
  }

  assert(mpq_cmp(tmp_exp, r) <= 0);
#ifndef NDEBUG
  mpq_t tmp_mul;
  mpq_init(tmp_mul);
  mpq_mul_2exp(tmp_mul, tmp_exp, 1);
  assert(mpq_cmp(r, tmp_mul) < 0);
  mpq_clear(tmp_mul);
#endif
  /* Determine number of bits required to represent the exponent for a
   * normal number. */
  uint32_t n_exp_bits = 2;
  int32_t esgn        = mpz_sgn(iexp);
  if (esgn > 0)
  {
    /* Not exactly representable with n_exp_bits, adjust. */
    mpz_t representable;
    mpz_init_set_ui(representable, 4);
    while (mpz_cmp(representable, iexp) <= 0)
    {
      mpz_mul_2exp(representable, representable, 1);
      n_exp_bits += 1;
    }
    mpz_clear(representable);
  }
  else if (esgn < 0)
  {
    /* Exactly representable with n_exp_bits + sign bit but -2^n and
     * -(2^n - 1) are both subnormal */
    mpz_t representable, rep_plus_two;
    mpz_init_set_si(representable, -4);
    mpz_init(rep_plus_two);
    mpz_add_ui(rep_plus_two, representable, 2);
    while (mpz_cmp(rep_plus_two, iexp) > 0)
    {
      mpz_mul_2exp(representable, representable, 1);
      mpz_add_ui(rep_plus_two, representable, 2);
      n_exp_bits += 1;
    }
    mpz_clear(rep_plus_two);
    mpz_clear(representable);
  }
  n_exp_bits += 1; /* for sign bit */
#ifndef NDEBUG
  char *exp_bin_str = mpz_get_str(nullptr, 2, iexp);
  assert(strlen(exp_bin_str) <= n_exp_bits);
  free(exp_bin_str);
#endif

  /* Significand ------------------------------------------------------- */

  /* sig bits of type + guard and sticky bits */
  uint32_t n_sig_bits = type.fp_sig_size() + 2;
  BitVector sig       = BitVector::mk_zero(n_sig_bits);
  mpq_t tmp_sig, mid;
  make_mpq_from_ui(tmp_sig, 0, 1);
  mpq_init(mid);
  for (uint32_t i = 0, n = n_sig_bits - 1; i < n; ++i)
  {
    mpq_add(mid, tmp_sig, tmp_exp);
    if (mpq_cmp(mid, r) <= 0)
    {
      sig.set_bit(0, 1);
      mpq_set(tmp_sig, mid);
    }
    sig.ibvshl(1);
    mpq_div_2exp(tmp_exp, tmp_exp, 1);
  }

  /* Sticky bit -------------------------------------------------------- */

  mpq_t remainder;
  mpq_init(remainder);
  mpq_sub(remainder, r, tmp_sig);
#ifndef NDEBUG
  mpq_t tmp01;
  make_mpq_from_ui(tmp01, 0, 1);
  assert(mpq_cmp(tmp01, remainder) <= 1);
  mpq_clear(tmp01);
#endif
  if (mpq_sgn(remainder) != 0)
  {
    sig.set_bit(0, 1);
  }

  /* Exact float ------------------------------------------------------- */

  FloatingPointTypeInfo exact_format(n_exp_bits, n_sig_bits);

  /* If the format has n_exp_bits, the unpacked format may have more to allow
   * subnormals to be normalised. */
  uint32_t extension =
      0;  // UnpackedFloat::exponentWidth(exact_format) - n_exp_bits;

  BitVector sign = sgn < 0 ? BitVector::mk_true() : BitVector::mk_false();
  char *str      = mpz_get_str(nullptr, 10, iexp);
  BitVector exp(n_exp_bits, str, 10);
  free(str);

  if (extension > 0)
  {
    exp.ibvsext(extension);
  }

  FloatingPointMPFR exact_float = from_unpacked(nm, sign, exp, sig);

  FloatingPointMPFR res(type);
  // res.d_uf.reset(
  //     new UnpackedFloat(symfpu::convertFloatToFloat<fp::SymFpuTraits>(
  //         exact_format, *res.size(), rm, *exact_float.unpacked())));

  mpq_clear(remainder);
  mpq_clear(tmp_sig);
  mpq_clear(mid);
  mpz_clear(iexp);
  mpz_clear(inc);
  mpq_clear(tmp_exp);
  mpq_clear(r);
  return res;
}

/* -------------------------------------------------------------------------- */

std::ostream &
operator<<(std::ostream &out, const FloatingPointMPFR &fp)
{
  out << fp.str();
  return out;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla

namespace std {

size_t
hash<bzla::FloatingPointMPFR>::operator()(
    const bzla::FloatingPointMPFR &fp) const
{
  return fp.hash();
}

}  // namespace std
