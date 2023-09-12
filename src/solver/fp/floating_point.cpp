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

template <bool T>
class SymFpuSymBV;

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
FloatingPoint::from_real(const Type &type,
                         const RoundingMode rm,
                         const std::string &real)
{
  return convert_from_rational_aux(type, rm, real.c_str(), nullptr);
}

FloatingPoint
FloatingPoint::from_rational(const Type &type,
                             const RoundingMode rm,
                             const std::string &num,
                             const std::string &den)
{
  return convert_from_rational_aux(type, rm, num.c_str(), den.c_str());
}

FloatingPoint
FloatingPoint::fpzero(const Type &type, bool sign)
{
  FloatingPoint res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeZero(*res.size(), sign)));
  return res;
}

FloatingPoint
FloatingPoint::fpinf(const Type &type, bool sign)
{
  FloatingPoint res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeInf(*res.size(), sign)));
  return res;
}

FloatingPoint
FloatingPoint::fpnan(const Type &type)
{
  FloatingPoint res(type);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeNaN(*res.size())));
  return res;
}

FloatingPoint
FloatingPoint::fpfp(const BitVector &sign,
                    const BitVector &exp,
                    const BitVector &sig)
{
  NodeManager &nm = NodeManager::get();
  FloatingPoint res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                    sign.bvconcat(exp).ibvconcat(sig));
  return res;
}

/* --- FloatingPoint public ------------------------------------------------- */

FloatingPoint::FloatingPoint(const Type &type)
{
  d_size.reset(new FloatingPointTypeInfo(type));
}

FloatingPoint::FloatingPoint(const FloatingPointTypeInfo &size)
{
  d_size.reset(new FloatingPointTypeInfo(size));
}

FloatingPoint::FloatingPoint(const Type &type, const UnpackedFloat &uf)
{
  d_size.reset(new FloatingPointTypeInfo(type));
  d_uf.reset(new UnpackedFloat(uf));
}

FloatingPoint::FloatingPoint(const Type &type, const BitVector &bv)
    : FloatingPoint(type)
{
  d_uf.reset(new UnpackedFloat(symfpu::unpack<fp::SymFpuTraits>(*d_size, bv)));
}

FloatingPoint::FloatingPoint(const Type &type,
                             const RoundingMode rm,
                             const FloatingPoint &fp)
    : FloatingPoint(type)
{
  d_uf.reset(new UnpackedFloat(symfpu::convertFloatToFloat<fp::SymFpuTraits>(
      *fp.size(), *d_size, rm, *fp.unpacked())));
}

FloatingPoint::FloatingPoint(const Type &type,
                             const RoundingMode rm,
                             const BitVector &bv,
                             bool sign)
    : FloatingPoint(type)
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

FloatingPoint::FloatingPoint(const FloatingPoint &other)
    : FloatingPoint(*other.size())
{
  d_uf.reset(new UnpackedFloat(*other.unpacked()));
}

FloatingPoint::~FloatingPoint() {}

uint64_t
FloatingPoint::get_exponent_size() const
{
  return d_size->exponentWidth();
}

uint64_t
FloatingPoint::get_significand_size() const
{
  return d_size->significandWidth();
}

FloatingPointTypeInfo *
FloatingPoint::size() const
{
  return d_size.get();
}

size_t
FloatingPoint::hash() const
{
  uint32_t hash = 0;
  hash += d_uf->getNaN() * s_hash_primes[0];
  hash += d_uf->getInf() * s_hash_primes[1];
  hash += d_uf->getZero() * s_hash_primes[2];
  hash += d_uf->getSign() * s_hash_primes[3];
  hash += d_uf->getExponent().getBv()->hash() * s_hash_primes[4];
  hash += d_uf->getSignificand().getBv()->hash() * s_hash_primes[5];
  return hash;
}

std::string
FloatingPoint::str(uint8_t bv_format) const
{
  assert(bv_format == 2 || bv_format == 10);
  std::stringstream ss;
  BitVector sign, exp, sig;
  FloatingPoint::ieee_bv_as_bvs(d_size->get_type(), as_bv(), sign, exp, sig);
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

int32_t
FloatingPoint::compare(const FloatingPoint &fp) const
{
  UnpackedFloat *uf_a = d_uf.get();
  UnpackedFloat *uf_b = fp.unpacked();

  BitVector *exp_a = uf_a->getExponent().getBv();
  BitVector *sig_a = uf_a->getSignificand().getBv();

  BitVector *exp_b = uf_b->getExponent().getBv();
  BitVector *sig_b = uf_b->getSignificand().getBv();

  if (exp_a->size() != exp_b->size() || sig_a->size() != sig_b->size())
  {
    return -1;
  }

  if (uf_a->getNaN() == uf_b->getNaN() && uf_a->getInf() == uf_b->getInf()
      && uf_a->getZero() == uf_b->getZero()
      && uf_a->getSign() == uf_b->getSign() && exp_a->compare(*exp_b) == 0
      && sig_a->compare(*sig_b) == 0)
  {
    return 0;
  }
  return -1;
}

bool
FloatingPoint::operator==(const FloatingPoint &other) const
{
  return compare(other) == 0;
}

bool
FloatingPoint::operator!=(const FloatingPoint &other) const
{
  return compare(other) != 0;
}

UnpackedFloat *
FloatingPoint::unpacked() const
{
  return d_uf.get();
}

void
FloatingPoint::set_unpacked(const UnpackedFloat &uf)
{
  d_uf.reset(new UnpackedFloat(uf));
}

bool
FloatingPoint::fpiszero() const
{
  return symfpu::isZero(*d_size, *d_uf);
}

bool
FloatingPoint::fpisnormal() const
{
  return symfpu::isNormal(*d_size, *d_uf);
}

bool
FloatingPoint::fpissubnormal() const
{
  return symfpu::isSubnormal(*d_size, *d_uf);
}

bool
FloatingPoint::fpisnan() const
{
  return symfpu::isNaN(*d_size, *d_uf);
}

bool
FloatingPoint::fpisinf() const
{
  return symfpu::isInfinite(*d_size, *d_uf);
}

bool
FloatingPoint::fpisneg() const
{
  return symfpu::isNegative(*d_size, *d_uf);
}

bool
FloatingPoint::fpispos() const
{
  return symfpu::isPositive(*d_size, *d_uf);
}

bool
FloatingPoint::fpeq(const FloatingPoint &fp) const
{
  return symfpu::smtlibEqual<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPoint::fplt(const FloatingPoint &fp) const
{
  return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPoint::fple(const FloatingPoint &fp) const
{
  return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
      *d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPoint::fpgt(const FloatingPoint &fp) const
{
  return symfpu::lessThan<fp::SymFpuTraits>(*d_size, *fp.unpacked(), *d_uf);
}

bool
FloatingPoint::fpge(const FloatingPoint &fp) const
{
  return symfpu::lessThanOrEqual<fp::SymFpuTraits>(
      *d_size, *fp.unpacked(), *d_uf);
}

FloatingPoint
FloatingPoint::fpabs() const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::absolute<fp::SymFpuTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fpneg() const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::negate<fp::SymFpuTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fpsqrt(const RoundingMode rm) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::sqrt<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fprti(const RoundingMode rm) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::roundToIntegral<fp::SymFpuTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fprem(const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::remainder<fp::SymFpuTraits>(*res.size(), *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpadd(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::add<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked(), true)));
  return res;
}

FloatingPoint
FloatingPoint::fpmul(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::multiply<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpdiv(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::divide<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpfma(const RoundingMode rm,
                     const FloatingPoint &fp0,
                     const FloatingPoint &fp1) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::fma<fp::SymFpuTraits>(
      *res.size(), rm, *d_uf, *fp0.unpacked(), *fp1.unpacked())));
  return res;
}

BitVector
FloatingPoint::as_bv() const
{
  return *symfpu::pack(*d_size, *d_uf).getBv();
}

/* --- Floating private ----------------------------------------------------- */

FloatingPoint
FloatingPoint::from_unpacked(const BitVector &sign,
                             const BitVector &exp,
                             const BitVector &sig)
{
  NodeManager &nm = NodeManager::get();
  FloatingPoint res(nm.mk_fp_type(exp.size(), sig.size() + 1),
                    UnpackedFloat(sign.is_one(), exp, sig));
  return res;
}

namespace {
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

FloatingPoint
FloatingPoint::convert_from_rational_aux(const Type &type,
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
    return FloatingPoint::fpzero(type, false);
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
  uint32_t extension = UnpackedFloat::exponentWidth(exact_format) - n_exp_bits;

  BitVector sign = sgn < 0 ? BitVector::mk_true() : BitVector::mk_false();
  char *str      = mpz_get_str(nullptr, 10, iexp);
  BitVector exp(n_exp_bits, str, 10);
  free(str);

  if (extension > 0)
  {
    exp.ibvsext(extension);
  }

  FloatingPoint exact_float = from_unpacked(sign, exp, sig);

  FloatingPoint res(type);
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

/* --- FloatingPointTypeInfo public ----------------------------------------- */

FloatingPointTypeInfo::FloatingPointTypeInfo(const Type &type)
    : d_esize(type.fp_exp_size()), d_ssize(type.fp_sig_size())
{
  assert(type.is_fp());
  d_type = type;
}

FloatingPointTypeInfo::FloatingPointTypeInfo(uint32_t esize, uint32_t ssize)
    : d_esize(esize), d_ssize(ssize)
{
  NodeManager &nm = NodeManager::get();
  d_type          = nm.mk_fp_type(esize, ssize);
}

FloatingPointTypeInfo::FloatingPointTypeInfo(const FloatingPointTypeInfo &other)
    : d_esize(other.d_esize), d_ssize(other.d_ssize)
{
  assert(other.d_type.is_fp());
  d_type = other.d_type;
}

FloatingPointTypeInfo::~FloatingPointTypeInfo() {}

const Type &
FloatingPointTypeInfo::get_type(void) const
{
  return d_type;
}

/* --- Other ---------------------------------------------------------------- */

std::ostream &
operator<<(std::ostream &out, const FloatingPoint &fp)
{
  out << fp.str();
  return out;
}

}  // namespace bzla

namespace std {

size_t
hash<bzla::FloatingPoint>::operator()(const bzla::FloatingPoint &fp) const
{
  return fp.hash();
}

}  // namespace std
