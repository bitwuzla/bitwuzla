#include "solver/fp/floating_point.h"

#include "solver/fp/symfpu_wrapper.h"

extern "C" {
#include "bzlacore.h"
}

#include <gmpxx.h>

#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
#include "symfpu/core/unpackedFloat.h"

template <bool T>
class BzlaFPSymBV;

namespace bzla {
namespace fp {

/* --- Floating public ------------------------------------------------------ */

FloatingPoint::FloatingPoint(BzlaSortId sort)
{
  d_size.reset(new FloatingPointSortInfo(sort));
}

FloatingPoint::FloatingPoint(const FloatingPointSortInfo &size)
{
  d_size.reset(new FloatingPointSortInfo(size));
}

FloatingPoint::FloatingPoint(BzlaSortId sort, const UnpackedFloat &uf)
{
  d_size.reset(new FloatingPointSortInfo(sort));
  d_uf.reset(new UnpackedFloat(uf));
}

FloatingPoint::FloatingPoint(BzlaSortId sort, const BzlaBitVector *bv)
    : FloatingPoint(sort)
{
  assert(s_bzla);
  d_uf.reset(new UnpackedFloat(
      symfpu::unpack<BzlaFPTraits>(*d_size, bzla_bv_copy(s_bzla->mm, bv))));
}

FloatingPoint::FloatingPoint(BzlaSortId sort,
                             const RoundingMode rm,
                             const FloatingPoint &fp)
    : FloatingPoint(sort)
{
  d_uf.reset(new UnpackedFloat(symfpu::convertFloatToFloat<BzlaFPTraits>(
      *fp.size(), *d_size, rm, *fp.unpacked())));
}

FloatingPoint::FloatingPoint(BzlaSortId sort,
                             const RoundingMode rm,
                             const BzlaBitVector *bv,
                             bool sign)
    : FloatingPoint(sort)
{
  assert(s_bzla);
  if (sign)
  {
    if (bzla_bv_get_width(bv) == 1)
    {
      /* Note: We must copy the bv here, because 1) the corresponding
       * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
       * constructor is matched (const bool &val). */
      UnpackedFloat uf = symfpu::convertUBVToFloat<BzlaFPTraits>(
          *d_size, rm, bzla_bv_copy(s_bzla->mm, bv));
      /* We need special handling for bit-vectors of size one since symFPU does
       * not allow conversions from signed bit-vectors of size one.  */
      if (bzla_bv_is_one(bv))
      {
        uf = symfpu::negate<BzlaFPTraits>(*d_size, uf);
      }
      d_uf.reset(new UnpackedFloat(uf));
    }
    else
    {
      /* Note: We must copy the bv here, because 1) the corresponding
       * constructor doesn't copy it but sets d_bv = bv and 2) the wrong
       * constructor is matched (const bool &val). */
      d_uf.reset(new UnpackedFloat(symfpu::convertSBVToFloat<BzlaFPTraits>(
          *d_size, rm, bzla_bv_copy(s_bzla->mm, bv))));
    }
  }
  else
  {
    d_uf.reset(new UnpackedFloat(symfpu::convertUBVToFloat<BzlaFPTraits>(
        *d_size, rm, bzla_bv_copy(s_bzla->mm, bv))));
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

FloatingPointSortInfo *
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
  hash += bzla_bv_hash(d_uf->getExponent().getBv()) * s_hash_primes[4];
  hash += bzla_bv_hash(d_uf->getSignificand().getBv()) * s_hash_primes[5];
  return hash;
}

int32_t
FloatingPoint::compare(const FloatingPoint &fp) const
{
  UnpackedFloat *uf_a = d_uf.get();
  UnpackedFloat *uf_b = fp.unpacked();

  BzlaBitVector *exp_a = uf_a->getExponent().getBv();
  BzlaBitVector *sig_a = uf_a->getSignificand().getBv();

  BzlaBitVector *exp_b = uf_b->getExponent().getBv();
  BzlaBitVector *sig_b = uf_b->getSignificand().getBv();

  if (bzla_bv_get_width(exp_a) != bzla_bv_get_width(exp_b)
      || bzla_bv_get_width(sig_a) != bzla_bv_get_width(sig_b))
  {
    return -1;
  }

  if (uf_a->getNaN() == uf_b->getNaN() && uf_a->getInf() == uf_b->getInf()
      && uf_a->getZero() == uf_b->getZero()
      && uf_a->getSign() == uf_b->getSign()
      && bzla_bv_compare(exp_a, exp_b) == 0
      && bzla_bv_compare(sig_a, sig_b) == 0)
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

FloatingPoint
FloatingPoint::from_real(BzlaSortId sort,
                         const RoundingMode rm,
                         const std::string &real)
{
  return convert_from_rational_aux(sort, rm, real.c_str(), nullptr);
}

FloatingPoint
FloatingPoint::from_rational(BzlaSortId sort,
                             const RoundingMode rm,
                             const std::string &num,
                             const std::string &den)
{
  return convert_from_rational_aux(sort, rm, num.c_str(), den.c_str());
}

bool
FloatingPoint::is_zero() const
{
  return symfpu::isZero(*d_size, *d_uf);
}

bool
FloatingPoint::is_normal() const
{
  return symfpu::isNormal(*d_size, *d_uf);
}

bool
FloatingPoint::is_subnormal() const
{
  return symfpu::isSubnormal(*d_size, *d_uf);
}

bool
FloatingPoint::is_nan() const
{
  return symfpu::isNaN(*d_size, *d_uf);
}

bool
FloatingPoint::is_inf() const
{
  return symfpu::isInfinite(*d_size, *d_uf);
}

bool
FloatingPoint::is_neg() const
{
  return symfpu::isNegative(*d_size, *d_uf);
}

bool
FloatingPoint::is_pos() const
{
  return symfpu::isPositive(*d_size, *d_uf);
}

bool
FloatingPoint::is_eq(const FloatingPoint &fp) const
{
  return symfpu::smtlibEqual<BzlaFPTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPoint::is_lt(const FloatingPoint &fp) const
{
  return symfpu::lessThan<BzlaFPTraits>(*d_size, *d_uf, *fp.unpacked());
}

bool
FloatingPoint::is_le(const FloatingPoint &fp) const
{
  return symfpu::lessThanOrEqual<BzlaFPTraits>(*d_size, *d_uf, *fp.unpacked());
}

FloatingPoint
FloatingPoint::fpzero(BzlaSortId sort, bool sign)
{
  FloatingPoint res(sort);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeZero(*res.size(), sign)));
  return res;
}

FloatingPoint
FloatingPoint::fpinf(BzlaSortId sort, bool sign)
{
  FloatingPoint res(sort);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeInf(*res.size(), sign)));
  return res;
}

FloatingPoint
FloatingPoint::fpnan(BzlaSortId sort)
{
  FloatingPoint res(sort);
  res.d_uf.reset(new UnpackedFloat(UnpackedFloat::makeNaN(*res.size())));
  return res;
}

FloatingPoint
FloatingPoint::fpfp(BzlaBitVector *sign, BzlaBitVector *exp, BzlaBitVector *sig)
{
  assert(s_bzla);
  BzlaSortId sort =
      bzla_sort_fp(s_bzla, bzla_bv_get_width(exp), bzla_bv_get_width(sig) + 1);

  BzlaBitVector *tmp      = bzla_bv_concat(s_bzla->mm, sign, exp);
  BzlaBitVector *bv_const = bzla_bv_concat(s_bzla->mm, tmp, sig);

  FloatingPoint res(sort, bv_const);

  bzla_bv_free(s_bzla->mm, tmp);
  bzla_bv_free(s_bzla->mm, bv_const);
  bzla_sort_release(s_bzla, sort);
  return res;
}

FloatingPoint
FloatingPoint::fpabs() const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::absolute<BzlaFPTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fpneg() const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::negate<BzlaFPTraits>(*res.size(), *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fpsqrt(const RoundingMode rm) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(
      new UnpackedFloat(symfpu::sqrt<BzlaFPTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fprti(const RoundingMode rm) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::roundToIntegral<BzlaFPTraits>(*res.size(), rm, *d_uf)));
  return res;
}

FloatingPoint
FloatingPoint::fprem(const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::remainder<BzlaFPTraits>(*res.size(), *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpadd(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::add<BzlaFPTraits>(*res.size(), rm, *d_uf, *fp.unpacked(), true)));
  return res;
}

FloatingPoint
FloatingPoint::fpmul(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::multiply<BzlaFPTraits>(*res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpdiv(const RoundingMode rm, const FloatingPoint &fp) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(
      symfpu::divide<BzlaFPTraits>(*res.size(), rm, *d_uf, *fp.unpacked())));
  return res;
}

FloatingPoint
FloatingPoint::fpfma(const RoundingMode rm,
                     const FloatingPoint &fp0,
                     const FloatingPoint &fp1) const
{
  FloatingPoint res(*d_size);
  res.d_uf.reset(new UnpackedFloat(symfpu::fma<BzlaFPTraits>(
      *res.size(), rm, *d_uf, *fp0.unpacked(), *fp1.unpacked())));
  return res;
}

BzlaBitVector *
FloatingPoint::as_bv() const
{
  assert(s_bzla);
  return bzla_bv_copy(s_bzla->mm, symfpu::pack(*d_size, *d_uf).getBv());
}

void
FloatingPoint::as_bvs(BzlaBitVector **sign,
                      BzlaBitVector **exp,
                      BzlaBitVector **sig) const
{
  assert(s_bzla);
  uint32_t bw     = d_size->packedWidth();
  uint32_t bw_exp = d_size->exponentWidth();
  uint32_t bw_sig = d_size->significandWidth();
  BzlaBitVector *bv =
      bzla_bv_copy(s_bzla->mm, symfpu::pack(*d_size, *d_uf).getBv());
  *sign = bzla_bv_slice(s_bzla->mm, bv, bw - 1, bw - 1);
  *exp  = bzla_bv_slice(s_bzla->mm, bv, bw - 2, bw - 1 - bw_exp);
  *sig  = bzla_bv_slice(s_bzla->mm, bv, bw_sig - 2, 0);
  bzla_bv_free(s_bzla->mm, bv);
}

/* --- Floating private ----------------------------------------------------- */

FloatingPoint
FloatingPoint::from_unpacked(BzlaBitVector *sign,
                             BzlaBitVector *exp,
                             BzlaBitVector *sig)
{
  assert(s_bzla);
  BzlaSortId sort =
      bzla_sort_fp(s_bzla, bzla_bv_get_width(exp), bzla_bv_get_width(sig) + 1);
  FloatingPoint res(sort,
                    UnpackedFloat(bzla_bv_is_one(sign),
                                  bzla_bv_copy(s_bzla->mm, exp),
                                  bzla_bv_copy(s_bzla->mm, sig)));
  bzla_sort_release(s_bzla, sort);
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
FloatingPoint::convert_from_rational_aux(BzlaSortId sort,
                                         const RoundingMode rm,
                                         const char *num,
                                         const char *den)
{
  assert(s_bzla);
  assert(sort);
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
    return FloatingPoint::fpzero(sort, false);
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

  BzlaMemMgr *mm = s_bzla->mm;

  /* Significand ------------------------------------------------------- */

  /* sig bits of sort + guard and sticky bits */
  uint32_t n_sig_bits = bzla_sort_fp_get_sig_width(s_bzla, sort) + 2;
  BzlaBitVector *sig  = bzla_bv_zero(mm, n_sig_bits);
  mpq_t tmp_sig, mid;
  make_mpq_from_ui(tmp_sig, 0, 1);
  mpq_init(mid);
  for (uint32_t i = 0, n = n_sig_bits - 1; i < n; ++i)
  {
    mpq_add(mid, tmp_sig, tmp_exp);
    if (mpq_cmp(mid, r) <= 0)
    {
      bzla_bv_set_bit(sig, 0, 1);
      mpq_set(tmp_sig, mid);
    }
    BzlaBitVector *shl = bzla_bv_sll_uint64(mm, sig, 1);
    bzla_bv_free(mm, sig);
    sig = shl;
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
    bzla_bv_set_bit(sig, 0, 1);
  }

  /* Exact float ------------------------------------------------------- */

  bzla::fp::FloatingPointSortInfo exact_format(n_exp_bits, n_sig_bits);

  /* If the format has n_exp_bits, the unpacked format may have more to allow
   * subnormals to be normalised. */
  uint32_t extension = UnpackedFloat::exponentWidth(exact_format) - n_exp_bits;

  BzlaBitVector *sign = sgn < 0 ? bzla_bv_one(mm, 1) : bzla_bv_zero(mm, 1);
  char *str           = mpz_get_str(nullptr, 10, iexp);
  BzlaBitVector *exp  = bzla_bv_constd(mm, str, n_exp_bits);
  free(str);

  if (extension > 0)
  {
    BzlaBitVector *tmp = bzla_bv_sext(mm, exp, extension);
    bzla_bv_free(mm, exp);
    exp = tmp;
  }

  FloatingPoint exact_float = from_unpacked(sign, exp, sig);

  FloatingPoint res(sort);
  res.d_uf.reset(new UnpackedFloat(symfpu::convertFloatToFloat<BzlaFPTraits>(
      exact_format, *res.size(), rm, *exact_float.unpacked())));

  bzla_bv_free(mm, exp);
  bzla_bv_free(mm, sign);
  bzla_bv_free(mm, sig);

  mpq_clear(remainder);
  mpq_clear(tmp_sig);
  mpq_clear(mid);
  mpz_clear(iexp);
  mpz_clear(inc);
  mpq_clear(tmp_exp);
  mpq_clear(r);
  return res;
}

/* --- FloatingPointSortInfo public ----------------------------------------- */

FloatingPointSortInfo::FloatingPointSortInfo(const BzlaSortId sort)
    : d_esize(bzla_sort_fp_get_exp_width(s_bzla, sort)),
      d_ssize(bzla_sort_fp_get_sig_width(s_bzla, sort))
{
  assert(s_bzla);
  assert(bzla_sort_is_fp(s_bzla, sort));
  d_sort = bzla_sort_copy(s_bzla, sort);
}

FloatingPointSortInfo::FloatingPointSortInfo(uint32_t esize, uint32_t ssize)
    : d_esize(esize), d_ssize(ssize)
{
  assert(s_bzla);
  d_sort = bzla_sort_fp(s_bzla, esize, ssize);
}

FloatingPointSortInfo::FloatingPointSortInfo(const FloatingPointSortInfo &other)
    : d_esize(other.d_esize), d_ssize(other.d_ssize)
{
  assert(s_bzla);
  assert(other.d_sort);
  assert(bzla_sort_is_fp(s_bzla, other.d_sort));
  d_sort = bzla_sort_copy(s_bzla, other.d_sort);
}

FloatingPointSortInfo::~FloatingPointSortInfo()
{
  assert(s_bzla);
  bzla_sort_release(s_bzla, d_sort);
}

BzlaSortId
FloatingPointSortInfo::get_sort(void) const
{
  assert(d_sort);
  return d_sort;
}
}  // namespace fp
}  // namespace bzla

namespace std {

size_t
hash<bzla::fp::FloatingPoint>::operator()(
    const bzla::fp::FloatingPoint &fp) const
{
  return fp.hash();
}

}  // namespace std
