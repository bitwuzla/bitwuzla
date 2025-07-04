/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/floating_point_symfpu.h"

#include <gmp.h>
#include <gmpxx.h>
#include <symfpu/core/add.h>
#include <symfpu/core/classify.h>
#include <symfpu/core/compare.h>
#include <symfpu/core/convert.h>
#include <symfpu/core/divide.h>
#include <symfpu/core/fma.h>
#include <symfpu/core/multiply.h>
#include <symfpu/core/packing.h>
#include <symfpu/core/remainder.h>
#include <symfpu/core/sign.h>
#include <symfpu/core/sqrt.h>
#include <symfpu/core/unpackedFloat.h>

#include "node/node_manager.h"
#include "solver/fp/symfpu_wrapper.h"
#include "util/gmp_utils.h"

template <bool T>
class SymFpuSymBV;

namespace bzla {
using namespace node;

/* --- UnpackedFloat -------------------------------------------------------- */

std::ostream&
operator<<(std::ostream& out,
           const ::symfpu::unpackedFloat<fp::SymFpuTraits>& uf)
{
  out << std::to_string(uf);
  return out;
}
}  // namespace bzla

namespace std {
std::string
to_string(const bzla::UnpackedFloat& uf)
{
  std::stringstream ss;
  ss << "nan: " << uf.nan << " inf: " << uf.inf << " zero: " << uf.zero
     << " sign: " << uf.sign << " exponent: " << uf.exponent
     << " significand: " << uf.significand;
  return ss.str();
}
}  // namespace std

namespace bzla {

/* --- FloatingPointSymFPU public static
 * ------------------------------------------ */

void
FloatingPointSymFPU::ieee_bv_as_bvs(const Type& type,
                                    const BitVector& bv,
                                    BitVector& sign,
                                    BitVector& exp,
                                    BitVector& sig)
{
  uint32_t bw     = bv.size();
  uint32_t bw_exp = type.fp_exp_size();
  uint32_t bw_sig = type.fp_sig_size();
  sign            = bv.bvextract(bw - 1, bw - 1);
  exp             = bv.bvextract(bw - 2, bw - 1 - bw_exp);
  sig             = bv.bvextract(bw_sig - 2, 0);
}

FloatingPointSymFPU
FloatingPointSymFPU::from_real(NodeManager& nm,
                               const Type& type,
                               const RoundingMode rm,
                               const std::string& real)
{
  return convert_from_rational_aux(nm, type, rm, real.c_str(), nullptr);
}

FloatingPointSymFPU
FloatingPointSymFPU::from_rational(NodeManager& nm,
                                   const Type& type,
                                   const RoundingMode rm,
                                   const std::string& num,
                                   const std::string& den)
{
  return convert_from_rational_aux(nm, type, rm, num.c_str(), den.c_str());
}

FloatingPointSymFPU
FloatingPointSymFPU::fpzero(const Type& type, bool sign)
{
  FloatingPointSymFPU res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeZero(*res.size(), sign)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpinf(const Type& type, bool sign)
{
  FloatingPointSymFPU res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeInf(*res.size(), sign)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpnan(const Type& type)
{
  FloatingPointSymFPU res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeNaN(*res.size())));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpfp(NodeManager& nm,
                          const BitVector& sign,
                          const BitVector& exp,
                          const BitVector& sig)
{
  FloatingPointSymFPU res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                          sign.bvconcat(exp).ibvconcat(sig));
  return res;
}

/* --- FloatingPointSymFPU public
 * ------------------------------------------------- */

FloatingPointSymFPU::FloatingPointSymFPU(const Type& type)
{
  d_size.reset(new FloatingPointSymFPUTypeInfo(type));
}

FloatingPointSymFPU::FloatingPointSymFPU(
    const FloatingPointSymFPUTypeInfo& size)
{
  d_size.reset(new FloatingPointSymFPUTypeInfo(size));
}

FloatingPointSymFPU::FloatingPointSymFPU(const Type& type,
                                         const UnpackedFloat& uf)
{
  d_size.reset(new FloatingPointSymFPUTypeInfo(type));
  d_uf.reset(new UnpackedFloat(uf));
}

FloatingPointSymFPU::FloatingPointSymFPU(const Type& type, const BitVector& bv)
    : FloatingPointSymFPU(type)
{
  d_uf.reset(new UnpackedFloat(symfpu::unpack<fp::SymFpuTraits>(*d_size, bv)));
}

FloatingPointSymFPU::FloatingPointSymFPU(const Type& type,
                                         const RoundingMode rm,
                                         const FloatingPointSymFPU& fp)
    : FloatingPointSymFPU(type)
{
  d_uf.reset(new UnpackedFloat(symfpu::convertFloatToFloat<fp::SymFpuTraits>(
      *fp.size(), *d_size, rm, *fp.unpacked())));
}

FloatingPointSymFPU::FloatingPointSymFPU(const Type& type,
                                         const RoundingMode rm,
                                         const BitVector& bv,
                                         bool sign)
    : FloatingPointSymFPU(type)
{
  if (sign)
  {
    if (bv.size() == 1)
    {
      /* Note: We must copy the bv here, because 1) the corresponding
       * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
       * constructor is matched (const bool &val). */
      UnpackedFloat uf =
          symfpu::convertUBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv);
      /* We need special handling for bit-vectors of size one since symFPU does
       * not allow conversions from signed bit-vectors of size one.  */
      if (bv.is_one())
      {
        d_uf.reset(
            new UnpackedFloat(symfpu::negate<fp::SymFpuTraits>(*d_size, uf)));
      }
      else
      {
        d_uf.reset(new UnpackedFloat(uf));
      }
    }
    else
    {
      /* Note: We must copy the bv here, because 1) the corresponding
       * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
       * constructor is matched (const bool &val). */
      d_uf.reset(new UnpackedFloat(
          symfpu::convertSBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv)));
    }
  }
  else
  {
    d_uf.reset(new UnpackedFloat(
        symfpu::convertUBVToFloat<fp::SymFpuTraits>(*d_size, rm, bv)));
  }
}

FloatingPointSymFPU::FloatingPointSymFPU(const FloatingPointSymFPU& other)
    : FloatingPointSymFPU(*other.size())
{
  d_uf.reset(new UnpackedFloat(*other.unpacked()));
}

FloatingPointSymFPU&
FloatingPointSymFPU::operator=(const FloatingPointSymFPU& other)

{
  d_size.reset(new FloatingPointSymFPUTypeInfo(*other.size()));
  d_uf.reset(new UnpackedFloat(*other.unpacked()));
  return *this;
}

FloatingPointSymFPU::~FloatingPointSymFPU() {}

uint64_t
FloatingPointSymFPU::get_exponent_size() const
{
  return d_size->exponentWidth();
}

uint64_t
FloatingPointSymFPU::get_significand_size() const
{
  return d_size->significandWidth();
}

FloatingPointSymFPUTypeInfo*
FloatingPointSymFPU::size() const
{
  return d_size.get();
}

size_t
FloatingPointSymFPU::hash() const
{
  uint32_t hash = 0;
  hash += d_uf->getNaN() * s_hash_primes[0];
  hash += d_uf->getInf() * s_hash_primes[1];
  hash += d_uf->getZero() * s_hash_primes[2];
  hash += d_uf->getSign() * s_hash_primes[3];
  hash += d_uf->getExponent().getBv().hash() * s_hash_primes[4];
  hash += d_uf->getSignificand().getBv().hash() * s_hash_primes[5];
  return hash;
}

std::string
FloatingPointSymFPU::str(uint8_t bv_format) const
{
  assert(bv_format == 2 || bv_format == 10);
  std::stringstream ss;
  BitVector sign, exp, sig;
  FloatingPointSymFPU::ieee_bv_as_bvs(d_size->type(), as_bv(), sign, exp, sig);
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
FloatingPointSymFPU::to_real_str() const
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
  FloatingPointSymFPU::ieee_bv_as_bvs(
      d_size->type(), as_bv(), bv_sign, bv_exp, bv_sig);

  UnpackedFloat* uf  = unpacked();
  const auto& uf_exp = uf->getExponent();
  const auto& uf_sig = uf->getSignificand();

  const BitVector& exp = uf_exp.getBv();
  mpz_class gmp_exp(exp.msb() ? -exp.bvneg().to_mpz() : exp.to_mpz());
  gmp_exp -= util::uint64_to_mpz_class(size_sig - 1);

  mpz_class gmp_sig = uf_sig.getBv().to_mpz();
  if (bv_sign.is_one())
  {
    gmp_sig = -gmp_sig;
  }

  mpz_class one(1);
  mpq_class q_res;
  if (gmp_exp >= 0)
  {
    q_res = gmp_sig * (one << gmp_exp.get_ui());
  }
  else
  {
    gmp_exp = -gmp_exp;
    q_res   = mpq_class(gmp_sig, one << gmp_exp.get_ui());
  }
  q_res.canonicalize();
  std::string res = q_res.get_str(10);
  if (res.find('/') == std::string::npos && res.find('.') == std::string::npos)
  {
    res += ".0";
  }
  return res;
}

bool
FloatingPointSymFPU::operator==(const FloatingPointSymFPU& other) const
{
  UnpackedFloat* uf_a = d_uf.get();
  UnpackedFloat* uf_b = other.unpacked();
  if (uf_a->getNaN() == uf_b->getNaN() && uf_a->getInf() == uf_b->getInf()
      && uf_a->getZero() == uf_b->getZero()
      && uf_a->getSign() == uf_b->getSign()
      && uf_a->getExponent().getBv() == uf_b->getExponent().getBv()
      && uf_a->getSignificand().getBv() == uf_b->getSignificand().getBv())
  {
    return true;
  }
  return false;
}

bool
FloatingPointSymFPU::operator!=(const FloatingPointSymFPU& other) const
{
  return !(*this == other);
}

UnpackedFloat*
FloatingPointSymFPU::unpacked() const
{
  return d_uf.get();
}

void
FloatingPointSymFPU::set_unpacked(const UnpackedFloat& uf)
{
  d_uf.reset(new UnpackedFloat(uf));
}

bool
FloatingPointSymFPU::fpiszero() const
{
  return symfpu::isZero(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpisnormal() const
{
  return symfpu::isNormal(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpissubnormal() const
{
  return symfpu::isSubnormal(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpisnan() const
{
  return symfpu::isNaN(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpisinf() const
{
  return symfpu::isInfinite(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpisneg() const
{
  return symfpu::isNegative(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpispos() const
{
  return symfpu::isPositive(*d_size, *d_uf);
}

bool
FloatingPointSymFPU::fpeq(const FloatingPointSymFPU& fp) const
{
  return symfpu::smtlibEqual<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPointSymFPU::fplt(const FloatingPointSymFPU& fp) const
{
  return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPointSymFPU::fple(const FloatingPointSymFPU& fp) const
{
  return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
      *d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPointSymFPU::fpgt(const FloatingPointSymFPU& fp) const
{
  return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *fp.unpacked(), *d_uf);
}

bool
FloatingPointSymFPU::fpge(const FloatingPointSymFPU& fp) const
{
  return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
      *d_size, *fp.unpacked(), *d_uf);
}

FloatingPointSymFPU
FloatingPointSymFPU::fpmin(const FloatingPointSymFPU& fp) const
{
  if (fpiszero() && fp.fpiszero() && fpisneg() != fp.fpisneg())
  {
    return FloatingPointSymFPU::fpzero(d_size->type(), true);
  }
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::min<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked(), false)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpmax(const FloatingPointSymFPU& fp) const
{
  if (fpiszero() && fp.fpiszero() && fpisneg() != fp.fpisneg())
  {
    return FloatingPointSymFPU::fpzero(d_size->type(), false);
  }
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::max<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked(), false)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpabs() const
{
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::absolute<fp::SymFpuTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpneg() const
{
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::negate<fp::SymFpuTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpsqrt(const RoundingMode rm) const
{
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::sqrt<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fprti(const RoundingMode rm) const
{
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::roundToIntegral<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fprem(const FloatingPointSymFPU& fp) const
{
  assert(d_size->type() == fp.size()->type());
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::remainder<fp::SymFpuTraits>(*res.size(), *d_uf, *fp.unpacked())));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpadd(const RoundingMode rm,
                           const FloatingPointSymFPU& fp) const
{
  assert(d_size->type() == fp.size()->type());
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::add<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked(), true)));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpmul(const RoundingMode rm,
                           const FloatingPointSymFPU& fp) const
{
  assert(d_size->type() == fp.size()->type());
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::multiply<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpdiv(const RoundingMode rm,
                           const FloatingPointSymFPU& fp) const
{
  assert(d_size->type() == fp.size()->type());
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::divide<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::fpfma(const RoundingMode rm,
                           const FloatingPointSymFPU& fp0,
                           const FloatingPointSymFPU& fp1) const
{
  assert(d_size->type() == fp0.size()->type());
  assert(d_size->type() == fp1.size()->type());
  FloatingPointSymFPU res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::fma<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp0.unpacked(), *fp1.unpacked())));
  return res;
}

BitVector
FloatingPointSymFPU::as_bv() const
{
  return symfpu::pack(*d_size, *d_uf).getBv();
}

/* --- FloatingPointSymFPU private
 * ------------------------------------------------ */

FloatingPointSymFPU
FloatingPointSymFPU::from_unpacked(NodeManager& nm,
                                   const BitVector& sign,
                                   const BitVector& exp,
                                   const BitVector& sig)
{
  FloatingPointSymFPU res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                          UnpackedFloat(sign.is_one(), exp, sig));
  return res;
}

FloatingPointSymFPU
FloatingPointSymFPU::convert_from_rational_aux(NodeManager& nm,
                                               const Type& type,
                                               const RoundingMode rm,
                                               const char* num,
                                               const char* den)
{
  assert(num);

  mpq_t r;
  if (den == nullptr)
  {
    util::mpq_from_dec_string(r, num);
  }
  else
  {
    util::mpq_from_rat_string(r, num, den);
  }

  int32_t sgn = mpq_sgn(r);
  if (sgn == 0)
  {
    mpq_clear(r);
    return FloatingPointSymFPU::fpzero(type, false);
  }

  /* r = abs(r) */
  if (sgn < 0)
  {
    mpq_neg(r, r);
  }

  /* Exponent ---------------------------------------------------------- */

  mpq_t tmp_exp;
  mpz_t iexp, inc;
  util::mpq_from_ui(tmp_exp, 1, 1);
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
  char* exp_bin_str = mpz_get_str(nullptr, 2, iexp);
  assert(strlen(exp_bin_str) <= n_exp_bits);
  free(exp_bin_str);
#endif

  /* Significand ------------------------------------------------------- */

  /* sig bits of type + guard and sticky bits */
  uint32_t n_sig_bits = type.fp_sig_size() + 2;
  BitVector sig       = BitVector::mk_zero(n_sig_bits);
  mpq_t tmp_sig, mid;
  util::mpq_from_ui(tmp_sig, 0, 1);
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
  util::mpq_from_ui(tmp01, 0, 1);
  assert(mpq_cmp(tmp01, remainder) <= 1);
  mpq_clear(tmp01);
#endif
  if (mpq_sgn(remainder) != 0)
  {
    sig.set_bit(0, 1);
  }

  /* Exact float ------------------------------------------------------- */

  FloatingPointSymFPUTypeInfo exact_format(n_exp_bits, n_sig_bits);

  /* If the format has n_exp_bits, the unpacked format may have more to allow
   * subnormals to be normalised. */
  uint32_t extension = UnpackedFloat::exponentWidth(exact_format) - n_exp_bits;

  BitVector sign = sgn < 0 ? BitVector::mk_true() : BitVector::mk_false();
  char* str      = mpz_get_str(nullptr, 10, iexp);
  BitVector exp(n_exp_bits, str, 10);
  free(str);

  if (extension > 0)
  {
    exp.ibvsext(extension);
  }

  FloatingPointSymFPU exact_float = from_unpacked(nm, sign, exp, sig);

  FloatingPointSymFPU res(type);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::convertFloatToFloat<fp::SymFpuTraits>(
          exact_format, *res.size(), rm, *exact_float.unpacked())));

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

std::ostream&
operator<<(std::ostream& out, const FloatingPointSymFPU& fp)
{
  out << fp.str();
  return out;
}

/* --- FloatingPointSymFPUTypeInfo public
 * ----------------------------------------- */

FloatingPointSymFPUTypeInfo::FloatingPointSymFPUTypeInfo(const Type& type)
    : d_esize(type.fp_exp_size()), d_ssize(type.fp_sig_size())
{
  assert(type.is_fp());
  d_type = type;
}

FloatingPointSymFPUTypeInfo::FloatingPointSymFPUTypeInfo(uint32_t esize,
                                                         uint32_t ssize)
    : d_esize(esize), d_ssize(ssize)
{
  NodeManager& nm = fp::SymFpuNM::get();
  d_type          = nm.mk_fp_type(esize, ssize);
}

FloatingPointSymFPUTypeInfo::FloatingPointSymFPUTypeInfo(
    const FloatingPointSymFPUTypeInfo& other)
    : d_esize(other.d_esize), d_ssize(other.d_ssize)
{
  assert(other.d_type.is_fp());
  d_type = other.d_type;
}

FloatingPointSymFPUTypeInfo::~FloatingPointSymFPUTypeInfo() {}

const Type&
FloatingPointSymFPUTypeInfo::type() const
{
  return d_type;
}

std::string
FloatingPointSymFPUTypeInfo::str() const
{
  return d_type.str();
}

std::ostream&
operator<<(std::ostream& out, const FloatingPointSymFPUTypeInfo& type)
{
  out << type.str();
  return out;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla

namespace std {

size_t
hash<bzla::FloatingPointSymFPU>::operator()(
    const bzla::FloatingPointSymFPU& fp) const
{
  return fp.hash();
}

}  // namespace std
