/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019-2020 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <sstream>
#include <unordered_map>
#include <vector>

extern "C" {
#include "bzlaabort.h"
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlanode.h"
#include "bzlarm.h"
#include "bzlasort.h"
}

#ifdef BZLA_USE_SYMFPU
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/unpackedFloat.h"
#endif

template <bool is_signed>
class BzlaFPSymBV;
class BzlaFPWordBlaster;
class BzlaFloatingPointSize;

/* ========================================================================== */
/* Glue for SymFPU: concrete.                                                 */
/* ========================================================================== */

/* Mapping between sorts. */
template <bool T>
struct signedToLiteralType;
template <>
struct signedToLiteralType<true>
{
  using literalType = int32_t;
};
template <>
struct signedToLiteralType<false>
{
  using literalType = uint32_t;
};

/* -------------------------------------------------------------------------- */
/* Wrapper for BzlaBitVector.                                                 */
/* -------------------------------------------------------------------------- */

/**
 * The template parameter distinguishes signed and unsigned bit-vectors, a
 * distinction symfpu uses.
 */
template <bool is_signed>
class BzlaFPBV
{
  friend BzlaFPSymBV<true>;
  friend BzlaFPSymBV<false>;
  friend BzlaFPWordBlaster;

 protected:
  using literalType = typename signedToLiteralType<is_signed>::literalType;

  friend BzlaFPBV<!is_signed>; /* Allow conversion between the types. */
#if BZLA_USE_SYMFPU
  friend ::symfpu::ite<bool, BzlaFPBV<is_signed> >; /* For ite. */
#endif

 public:
  BzlaFPBV(const uint32_t bw, const uint32_t val);
  BzlaFPBV(const bool &val);
  BzlaFPBV(const BzlaFPBV<is_signed> &other);
  BzlaFPBV(const BzlaFPBV<!is_signed> &other);
  BzlaFPBV(BzlaBitVector *bv);
  ~BzlaFPBV();

  uint32_t getWidth(void) const;
  BzlaBitVector *getBv(void) const { return d_bv; }

  static BzlaFPBV<is_signed> one(const uint32_t &bw);
  static BzlaFPBV<is_signed> zero(const uint32_t &bw);
  static BzlaFPBV<is_signed> allOnes(const uint32_t &bw);

  bool isAllOnes() const;
  bool isAllZeros() const;

  static BzlaFPBV<is_signed> maxValue(const uint32_t &bw);
  static BzlaFPBV<is_signed> minValue(const uint32_t &bw);

  /*** Operators ***/
  BzlaFPBV<is_signed> operator<<(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator>>(const BzlaFPBV<is_signed> &op) const;

  BzlaFPBV<is_signed> operator|(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator&(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator+(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator-(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator*(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator/(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator%(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> operator-(void) const;
  BzlaFPBV<is_signed> operator~(void) const;

  BzlaFPBV<is_signed> increment() const;
  BzlaFPBV<is_signed> decrement() const;
  BzlaFPBV<is_signed> signExtendRightShift(const BzlaFPBV<is_signed> &op) const;

  /*** Modular operations ***/
  // No overflow checking so these are the same as other operations
  BzlaFPBV<is_signed> modularLeftShift(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> modularRightShift(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> modularIncrement() const;
  BzlaFPBV<is_signed> modularDecrement() const;
  BzlaFPBV<is_signed> modularAdd(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> modularNegate() const;

  /*** Comparisons ***/
  bool operator==(const BzlaFPBV<is_signed> &op) const;
  bool operator<=(const BzlaFPBV<is_signed> &op) const;
  bool operator>=(const BzlaFPBV<is_signed> &op) const;
  bool operator<(const BzlaFPBV<is_signed> &op) const;
  bool operator>(const BzlaFPBV<is_signed> &op) const;

  /*** Type conversion ***/
  BzlaFPBV<true> toSigned(void) const;
  BzlaFPBV<false> toUnsigned(void) const;

  /*** Bit hacks ***/
  BzlaFPBV<is_signed> extend(uint32_t extension) const;
  BzlaFPBV<is_signed> contract(uint32_t reduction) const;
  BzlaFPBV<is_signed> resize(uint32_t newSize) const;
  BzlaFPBV<is_signed> matchWidth(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> append(const BzlaFPBV<is_signed> &op) const;
  BzlaFPBV<is_signed> extract(uint32_t upper, uint32_t lower) const;

 private:
  BzlaBitVector *d_bv = nullptr;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

template <>
Bzla *BzlaFPBV<true>::s_bzla = nullptr;
template <>
Bzla *BzlaFPBV<false>::s_bzla = nullptr;

template <bool is_signed>
BzlaFPBV<is_signed>::BzlaFPBV(const uint32_t bw, const uint32_t val)
{
  assert(s_bzla);
  assert(bw);
  d_bv = bzla_bv_uint64_to_bv(s_bzla->mm, val, bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>::BzlaFPBV(const bool &val)
{
  assert(s_bzla);
  d_bv = val ? bzla_bv_one(s_bzla->mm, 1) : bzla_bv_zero(s_bzla->mm, 1);
}

template <bool is_signed>
BzlaFPBV<is_signed>::BzlaFPBV(const BzlaFPBV<is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_bv);
  d_bv = bzla_bv_copy(s_bzla->mm, other.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>::BzlaFPBV(const BzlaFPBV<!is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_bv);
  d_bv = bzla_bv_copy(s_bzla->mm, other.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>::BzlaFPBV(BzlaBitVector *bv)
{
  assert(s_bzla);
  assert(bv);
  d_bv = bv;
}

template <bool is_signed>
BzlaFPBV<is_signed>::~BzlaFPBV()
{
  assert(s_bzla);
  assert(d_bv);
  bzla_bv_free(s_bzla->mm, d_bv);
}

template <bool is_signed>
uint32_t
BzlaFPBV<is_signed>::getWidth(void) const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_get_width(d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::one(const uint32_t &bw)
{
  assert(s_bzla);
  assert(bw);
  return bzla_bv_one(s_bzla->mm, bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::zero(const uint32_t &bw)
{
  assert(s_bzla);
  assert(bw);
  return bzla_bv_zero(s_bzla->mm, bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::allOnes(const uint32_t &bw)
{
  assert(s_bzla);
  assert(bw);
  return bzla_bv_ones(s_bzla->mm, bw);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::isAllOnes() const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_is_ones(d_bv);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::isAllZeros() const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_is_zero(d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::maxValue(const uint32_t &bw)
{
  assert(s_bzla);
  assert(bw);
  return is_signed ? bzla_bv_max_signed(s_bzla->mm, bw)
                   : bzla_bv_ones(s_bzla->mm, bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::minValue(const uint32_t &bw)
{
  assert(s_bzla);
  assert(bw);
  return is_signed ? bzla_bv_min_signed(s_bzla->mm, bw)
                   : bzla_bv_zero(s_bzla->mm, bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator<<(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_sll(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator>>(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_sra(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_srl(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator|(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_or(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator&(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_and(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator+(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_add(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator-(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_sub(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator*(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_mul(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator/(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_sdiv(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_udiv(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator%(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_srem(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_urem(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator-(void) const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_neg(s_bzla->mm, d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::operator~(void) const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_not(s_bzla->mm, d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::increment() const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_inc(s_bzla->mm, d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::decrement() const
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_dec(s_bzla->mm, d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::signExtendRightShift(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_sra(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularLeftShift(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return *this << op;
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularRightShift(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return *this >> op;
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularIncrement() const
{
  assert(s_bzla);
  assert(d_bv);
  return this->increment();
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  assert(d_bv);
  return this->decrement();
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularAdd(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return *this + op;
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularNegate() const
{
  assert(s_bzla);
  assert(d_bv);
  return -(*this);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator==(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  BzlaBitVector *res_bv = bzla_bv_eq(s_bzla->mm, d_bv, op.d_bv);
  bool res              = bzla_bv_is_true(res_bv);
  bzla_bv_free(s_bzla->mm, res_bv);
  return res;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator<=(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  BzlaBitVector *res_bv = is_signed ? bzla_bv_slte(s_bzla->mm, d_bv, op.d_bv)
                                    : bzla_bv_ulte(s_bzla->mm, d_bv, op.d_bv);
  bool res = bzla_bv_is_true(res_bv);
  bzla_bv_free(s_bzla->mm, res_bv);
  return res;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>=(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  BzlaBitVector *res_bv = is_signed ? bzla_bv_sgte(s_bzla->mm, d_bv, op.d_bv)
                                    : bzla_bv_ugte(s_bzla->mm, d_bv, op.d_bv);
  bool res = bzla_bv_is_true(res_bv);
  bzla_bv_free(s_bzla->mm, res_bv);
  return res;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator<(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  BzlaBitVector *res_bv = is_signed ? bzla_bv_slt(s_bzla->mm, d_bv, op.d_bv)
                                    : bzla_bv_ult(s_bzla->mm, d_bv, op.d_bv);
  bool res = bzla_bv_is_true(res_bv);
  bzla_bv_free(s_bzla->mm, res_bv);
  return res;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  BzlaBitVector *res_bv = is_signed ? bzla_bv_sgt(s_bzla->mm, d_bv, op.d_bv)
                                    : bzla_bv_ugt(s_bzla->mm, d_bv, op.d_bv);
  bool res = bzla_bv_is_true(res_bv);
  bzla_bv_free(s_bzla->mm, res_bv);
  return res;
}

template <bool is_signed>
BzlaFPBV<true>
BzlaFPBV<is_signed>::toSigned(void) const
{
  assert(s_bzla);
  assert(d_bv);
  return BzlaFPBV<true>(*this);
}

template <bool is_signed>
BzlaFPBV<false>
BzlaFPBV<is_signed>::toUnsigned(void) const
{
  assert(s_bzla);
  assert(d_bv);
  return BzlaFPBV<false>(*this);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::extend(uint32_t extension) const
{
  assert(s_bzla);
  assert(d_bv);
  return is_signed ? bzla_bv_sext(s_bzla->mm, d_bv, extension)
                   : bzla_bv_uext(s_bzla->mm, d_bv, extension);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::contract(uint32_t reduction) const
{
  assert(s_bzla);
  assert(d_bv);
  uint32_t bw = this->getWidth();
  assert(bw - 1 - reduction < bw);
  return bzla_bv_slice(s_bzla->mm, d_bv, bw - 1 - reduction, 0);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::resize(uint32_t newSize) const
{
  assert(s_bzla);
  assert(d_bv);
  uint32_t bw = this->getWidth();
  if (newSize > bw)
  {
    return this->extend(newSize - bw);
  }
  if (newSize < bw)
  {
    return this->contract(bw - newSize);
  }
  return *this;
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::matchWidth(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  uint32_t bw = this->getWidth();
  assert(bw <= op.getWidth());
  return this->extend(op.getWidth() - bw);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::append(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return bzla_bv_concat(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(upper >= lower);
  return bzla_bv_slice(s_bzla->mm, d_bv, upper, lower);
}

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class BzlaFPTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = BzlaRoundingMode;
  using fpt  = BzlaFloatingPointSize;
  using prop = bool;
  using sbv  = BzlaFPBV<true>;
  using ubv  = BzlaFPBV<false>;

  /* Give concrete instances of each rounding mode, mainly for comparisons. */
  static BzlaRoundingMode RNE(void);
  static BzlaRoundingMode RNA(void);
  static BzlaRoundingMode RTP(void);
  static BzlaRoundingMode RTN(void);
  static BzlaRoundingMode RTZ(void);

  /* Properties used by Symfpu. */
  static void precondition(const bool &p);
  static void postcondition(const bool &p);
  static void invariant(const bool &p);
};

/* -------------------------------------------------------------------------- */

BzlaRoundingMode
BzlaFPTraits::RNE(void)
{
  return BZLA_RM_RNE;
}

BzlaRoundingMode
BzlaFPTraits::RNA(void)
{
  return BZLA_RM_RNA;
}

BzlaRoundingMode
BzlaFPTraits::RTP(void)
{
  return BZLA_RM_RTP;
}

BzlaRoundingMode
BzlaFPTraits::RTN(void)
{
  return BZLA_RM_RTN;
}

BzlaRoundingMode
BzlaFPTraits::RTZ(void)
{
  return BZLA_RM_RTZ;
}

void
BzlaFPTraits::precondition(const bool &p)
{
  assert(p);
}

void
BzlaFPTraits::postcondition(const bool &p)
{
  assert(p);
}

void
BzlaFPTraits::invariant(const bool &p)
{
  assert(p);
}

/* ========================================================================== */
/* Floating-Point constants.                                                  */
/* ========================================================================== */

class BzlaFloatingPointSize
{
 public:
  BzlaFloatingPointSize(uint32_t e, uint32_t s) : d_ewidth(e), d_swidth(s) {}
  BzlaFloatingPointSize(const BzlaFloatingPointSize &other)
      : d_ewidth(other.d_ewidth), d_swidth(other.d_swidth)
  {
  }
  /* symFPU interface */
  uint32_t exponentWidth() const { return d_ewidth; }
  uint32_t significandWidth() const { return d_swidth; }
  uint32_t packedWidth() const { return d_ewidth + d_swidth; }
  uint32_t packedExponentWidth() const { return d_ewidth; }
  uint32_t packedSignificandWidth() const { return d_swidth - 1; }

 protected:
  uint32_t d_ewidth; /* size of exponent */
  uint32_t d_swidth; /* size of significand */
};

using BzlaUnpackedFloat = ::symfpu::unpackedFloat<BzlaFPTraits>;

struct BzlaFloatingPoint
{
  BzlaFloatingPointSize *size;
#ifdef BZLA_USE_SYMFPU
  ::symfpu::unpackedFloat<BzlaFPTraits> *fp;
#endif
};

/* ========================================================================== */
/* Glue for SymFPU: symbolic.                                                 */
/* ========================================================================== */

class BzlaFPSymRM;
class BzlaFPSortInfo;
class BzlaFPSymProp;
template <bool T>
class BzlaFPSymBV;

/* Mapping between sorts. */
template <bool T>
struct BzlaSignedToLitSort;
template <>
struct BzlaSignedToLitSort<true>
{
  using BzlaLitSort = int32_t;
};
template <>
struct BzlaSignedToLitSort<false>
{
  using BzlaLitSort = uint32_t;
};

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for floating-point sorts.                                */
/* -------------------------------------------------------------------------- */

class BzlaFPSortInfo : public BzlaFloatingPointSize
{
  friend BzlaFPWordBlaster;

 public:
  BzlaFPSortInfo(const BzlaSortId sort);
  BzlaFPSortInfo(uint32_t ewidth, uint32_t swidth);
  BzlaFPSortInfo(const BzlaFPSortInfo &other);
  ~BzlaFPSortInfo();

  BzlaSortId getSort(void) const;

 private:
  BzlaSortId d_sort;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

Bzla *BzlaFPSortInfo::s_bzla = nullptr;

BzlaFPSortInfo::BzlaFPSortInfo(const BzlaSortId sort)
    : BzlaFloatingPointSize(bzla_sort_fp_get_exp_width(s_bzla, sort),
                            bzla_sort_fp_get_sig_width(s_bzla, sort))
{
  assert(s_bzla);
  assert(bzla_sort_is_fp(s_bzla, sort));
  d_sort = bzla_sort_copy(s_bzla, sort);
}

BzlaFPSortInfo::BzlaFPSortInfo(uint32_t ewidth, uint32_t swidth)
    : BzlaFloatingPointSize(ewidth, swidth)
{
  assert(s_bzla);
  d_sort = bzla_sort_fp(s_bzla, ewidth, swidth);
}

BzlaFPSortInfo::BzlaFPSortInfo(const BzlaFPSortInfo &other)
    : BzlaFloatingPointSize(other.d_ewidth, other.d_swidth)
{
  assert(s_bzla);
  assert(other.d_sort);
  assert(bzla_sort_is_fp(s_bzla, other.d_sort));
  d_sort = bzla_sort_copy(s_bzla, other.d_sort);
}

BzlaFPSortInfo::~BzlaFPSortInfo()
{
  assert(s_bzla);
  bzla_sort_release(s_bzla, d_sort);
}

BzlaSortId
BzlaFPSortInfo::getSort(void) const
{
  assert(d_sort);
  return d_sort;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for propositions.                                        */
/* -------------------------------------------------------------------------- */

class BzlaFPSymProp
{
  friend BzlaFPWordBlaster;
  friend BzlaFPSymBV<true>;
  friend BzlaFPSymBV<false>;
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaFPSymProp, BzlaFPSymProp>;
#endif

 public:
  BzlaFPSymProp(BzlaNode *node);
  BzlaFPSymProp(bool v);
  BzlaFPSymProp(const BzlaFPSymProp &other);
  ~BzlaFPSymProp();

  BzlaNode *getNode() const { return d_node; }

  BzlaFPSymProp &operator=(const BzlaFPSymProp &other);

  BzlaFPSymProp operator!(void) const;
  BzlaFPSymProp operator&&(const BzlaFPSymProp &op) const;
  BzlaFPSymProp operator||(const BzlaFPSymProp &op) const;
  BzlaFPSymProp operator==(const BzlaFPSymProp &op) const;
  BzlaFPSymProp operator^(const BzlaFPSymProp &op) const;

 protected:
  bool checkNode(const BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

Bzla *BzlaFPSymProp::s_bzla = nullptr;

BzlaFPSymProp::BzlaFPSymProp(BzlaNode *node)
{
  assert(s_bzla);
  assert(checkNode(node));
  d_node = bzla_node_copy(s_bzla, node);
}

BzlaFPSymProp::BzlaFPSymProp(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

BzlaFPSymProp::BzlaFPSymProp(const BzlaFPSymProp &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

BzlaFPSymProp::~BzlaFPSymProp()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

BzlaFPSymProp &
BzlaFPSymProp::operator=(const BzlaFPSymProp &other)
{
  assert(d_node);
  assert(other.d_node);
  assert(s_bzla == bzla_node_real_addr(d_node)->bzla);
  assert(s_bzla == bzla_node_real_addr(other.d_node)->bzla);
  BzlaNode *n = bzla_node_copy(s_bzla, other.d_node);
  bzla_node_release(s_bzla, d_node);
  d_node = n;
  return *this;
}

BzlaFPSymProp
BzlaFPSymProp::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_bv_not(s_bzla, d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator&&(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(checkNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator||(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(checkNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator==(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(checkNode(op.d_node));
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator^(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(checkNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

bool
BzlaFPSymProp::checkNode(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node))
         && bzla_node_bv_get_width(s_bzla, node) == 1;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for bit-vector terms.                                    */
/* -------------------------------------------------------------------------- */

template <bool is_signed>
class BzlaFPSymBV;

template <bool is_signed>
class BzlaFPSymBV
{
  friend BzlaFPWordBlaster;
  friend BzlaFPSymBV<!is_signed>; /* Allow conversion between the sorts. */
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaFPSymProp, BzlaFPSymBV<is_signed> >;
#endif

 public:
  /** Constructors for bit-vector nodes. */
  BzlaFPSymBV(BzlaNode *node);
  BzlaFPSymBV(const uint32_t w, const uint32_t val);
  BzlaFPSymBV(const BzlaFPSymProp &p);
  BzlaFPSymBV(const BzlaFPSymBV<is_signed> &other);
  BzlaFPSymBV(const BzlaFPSymBV<!is_signed> &other);
  BzlaFPSymBV(const BzlaBitVector *bv);
  BzlaFPSymBV(const BzlaFPBV<is_signed> &bv);
  /** Constructors for Boolean nodes. */
  BzlaFPSymBV(bool v);
  /** Destructor. */
  ~BzlaFPSymBV();

  BzlaFPSymBV<is_signed> &operator=(const BzlaFPSymBV<is_signed> &other);

  uint32_t getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }

  /** Constant creation and test */
  static BzlaFPSymBV<is_signed> one(const uint32_t &w);
  static BzlaFPSymBV<is_signed> zero(const uint32_t &w);
  static BzlaFPSymBV<is_signed> allOnes(const uint32_t &w);

  BzlaFPSymProp isAllOnes() const;
  BzlaFPSymProp isAllZeros() const;

  static BzlaFPSymBV<is_signed> maxValue(const uint32_t &w);
  static BzlaFPSymBV<is_signed> minValue(const uint32_t &w);

  /** Operators */
  BzlaFPSymBV<is_signed> operator<<(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator>>(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator|(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator&(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator+(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator-(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator*(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator/(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator%(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> operator-(void) const;
  BzlaFPSymBV<is_signed> operator~(void) const;
  BzlaFPSymBV<is_signed> increment() const;
  BzlaFPSymBV<is_signed> decrement() const;
  BzlaFPSymBV<is_signed> signExtendRightShift(
      const BzlaFPSymBV<is_signed> &op) const;

  /** Modular operations */
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  BzlaFPSymBV<is_signed> modularLeftShift(
      const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> modularRightShift(
      const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> modularIncrement() const;
  BzlaFPSymBV<is_signed> modularDecrement() const;
  BzlaFPSymBV<is_signed> modularAdd(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> modularNegate() const;

  /** Operators for Boolean nodes */
  BzlaFPSymProp operator!(void) const;
  BzlaFPSymProp operator&&(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator||(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator^(const BzlaFPSymBV<is_signed> &op) const;

  /** Comparisons */
  BzlaFPSymProp operator==(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator<=(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator>=(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator<(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator>(const BzlaFPSymBV<is_signed> &op) const;

  /** Type conversion */
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  BzlaFPSymBV<true> toSigned(void) const;
  BzlaFPSymBV<false> toUnsigned(void) const;

  /** Bit hacks */
  BzlaFPSymBV<is_signed> extend(uint32_t extension) const;
  BzlaFPSymBV<is_signed> contract(uint32_t reduction) const;
  BzlaFPSymBV<is_signed> resize(uint32_t newSize) const;
  BzlaFPSymBV<is_signed> matchWidth(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> append(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymBV<is_signed> extract(uint32_t upper, uint32_t lower) const;

 protected:
  using literalType = typename BzlaSignedToLitSort<is_signed>::BzlaLitSort;

  // BzlaNode* boolNodeToBV(BzlaNode* node) const;
  // BzlaNode* BVToBoolNode(BzlaNode* node) const;

  bool checkNode(const BzlaNode *node) const;
  bool checkBooleanNode(const BzlaNode *node) const;
  // BzlaNode *fromProposition (BzlaNode *node) const;
  // BzlaNode *toProposition (BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

template <>
Bzla *BzlaFPSymBV<true>::s_bzla = nullptr;
template <>
Bzla *BzlaFPSymBV<false>::s_bzla = nullptr;

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(BzlaNode *node)
{
  assert(s_bzla);
  assert(checkNode(node));
  d_node = bzla_node_copy(s_bzla, node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const uint32_t w, const uint32_t val)
{
  assert(s_bzla);
  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  d_node       = is_signed ? bzla_exp_bv_int(s_bzla, val, s)
                     : bzla_exp_bv_unsigned(s_bzla, val, s);
  bzla_sort_release(s_bzla, s);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaFPSymProp &p)
{
  assert(s_bzla);
  assert(p.d_node);
  assert(bzla_sort_bv_get_width(s_bzla, bzla_node_get_sort_id(p.d_node)));
  d_node = bzla_node_copy(s_bzla, p.d_node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaFPSymBV<is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaFPSymBV<!is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaBitVector *bv)
{
  assert(s_bzla);
  d_node = bzla_exp_bv_const(s_bzla, bv);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaFPBV<is_signed> &bv)
{
  assert(s_bzla);
  assert(bv.d_bv);
  d_node = bzla_exp_bv_const(s_bzla, bv.d_bv);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::~BzlaFPSymBV()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

template <bool is_signed>
uint32_t
BzlaFPSymBV<is_signed>::getWidth(void) const
{
  assert(s_bzla);
  return bzla_node_bv_get_width(s_bzla, d_node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::one(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_one(s_bzla, s);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::zero(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_zero(s_bzla, s);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::allOnes(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_ones(s_bzla, s);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::isAllOnes() const
{
  return *this == BzlaFPSymBV<is_signed>::allOnes(this->getWidth());
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::isAllZeros() const
{
  return *this == BzlaFPSymBV<is_signed>::zero(this->getWidth());
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::maxValue(const uint32_t &w)
{
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_max_signed(s_bzla, s)
                          : bzla_exp_bv_ones(s_bzla, s);

  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::minValue(const uint32_t &w)
{
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_min_signed(s_bzla, s)
                          : bzla_exp_bv_zero(s_bzla, s);

  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator<<(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sll(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator>>(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sra(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_srl(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator|(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator&(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator+(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_add(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator-(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sub(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator*(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_mul(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator/(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sdiv(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_udiv(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator%(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_srem(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_urem(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator-(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_neg(s_bzla, d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::operator~(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_not(s_bzla, d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::increment() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_inc(s_bzla, d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::decrement() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_dec(s_bzla, d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::signExtendRightShift(
    const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sra(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularLeftShift(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this << op;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularRightShift(
    const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this >> op;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularIncrement() const
{
  assert(s_bzla);
  return this->increment();
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  return this->decrement();
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularAdd(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this + op;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularNegate() const
{
  assert(s_bzla);
  return -(*this);
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_bv_not(s_bzla, d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator||(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(checkBooleanNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator^(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(checkNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator==(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator<=(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_slte(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ulte(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator>=(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sgte(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ugte(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator<(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_slt(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ult(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::operator>(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sgt(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ugt(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<true>
BzlaFPSymBV<is_signed>::toSigned(void) const
{
  return BzlaFPSymBV<true>(*this);
}

template <bool is_signed>
BzlaFPSymBV<false>
BzlaFPSymBV<is_signed>::toUnsigned(void) const
{
  return BzlaFPSymBV<false>(*this);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::extend(uint32_t extension) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sext(s_bzla, d_node, extension)
                          : bzla_exp_bv_uext(s_bzla, d_node, extension);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::contract(uint32_t reduction) const
{
  assert(s_bzla);
  assert(this->getWidth() > reduction);
  BzlaNode *n =
      bzla_exp_bv_slice(s_bzla, d_node, this->getWidth() - 1 - reduction, 0);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::resize(uint32_t newSize) const
{
  uint32_t bw = this->getWidth();
  if (newSize > bw) return this->extend(newSize - bw);
  if (newSize < bw) return this->contract(bw - newSize);
  return *this;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::matchWidth(const BzlaFPSymBV<is_signed> &op) const
{
  assert(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::append(const BzlaFPSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_concat(s_bzla, d_node, op.d_node);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(s_bzla);
  assert(upper >= lower);
  BzlaNode *n                = bzla_exp_bv_slice(s_bzla, d_node, upper, lower);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
bool
BzlaFPSymBV<is_signed>::checkNode(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node));
}

template <bool is_signed>
bool
BzlaFPSymBV<is_signed>::checkBooleanNode(const BzlaNode *node) const
{
  assert(checkNode(node));
  return bzla_node_bv_get_width(s_bzla, node) == 1;
}

// BzlaNode* BzlaFPSymBV::boolNodeToBV(BzlaNode* node) const;
// BzlaNode* BzlaFPSymBV::BVToBoolNode(BzlaNode* node) const;

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for rounding modes.                                      */
/* -------------------------------------------------------------------------- */

class BzlaFPSymRM
{
  friend BzlaFPWordBlaster;
#ifdef BZLA_USE_SYMFPU
  friend symfpu::ite<BzlaFPSymProp, BzlaFPSymRM>;
#endif

 public:
  /* Constructors. */
  BzlaFPSymRM(BzlaNode *node);
  BzlaFPSymRM(const uint32_t val);
  BzlaFPSymRM(const BzlaFPSymRM &other);
  /* Destructor. */
  ~BzlaFPSymRM();

  BzlaNode *getNode() const { return d_node; }

  BzlaFPSymProp valid(void) const;
  BzlaFPSymProp operator==(const BzlaFPSymRM &other) const;

 protected:
  bool checkNode(const BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

Bzla *BzlaFPSymRM::s_bzla = nullptr;

BzlaFPSymRM::BzlaFPSymRM(BzlaNode *node)
{
  assert(s_bzla);
  assert(checkNode(node));
  d_node = bzla_node_copy(s_bzla, node);
}

BzlaFPSymRM::BzlaFPSymRM(const uint32_t val)
{
  assert(s_bzla);
  assert(bzla_rm_is_valid(val));
  BzlaMemMgr *mm    = s_bzla->mm;
  BzlaBitVector *rm = bzla_bv_uint64_to_bv(mm, val, BZLA_RM_BW);
  d_node            = bzla_exp_bv_const(s_bzla, rm);
  bzla_bv_free(mm, rm);
  assert(checkNode(d_node));
}

BzlaFPSymRM::BzlaFPSymRM(const BzlaFPSymRM &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

BzlaFPSymRM::~BzlaFPSymRM()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

BzlaFPSymProp
BzlaFPSymRM::valid(void) const
{
  assert(d_node);
  BzlaNode *max =
      bzla_exp_bv_unsigned(s_bzla, BZLA_RM_MAX, bzla_node_get_sort_id(d_node));
  BzlaNode *valid = bzla_exp_bv_ult(s_bzla, d_node, max);
  BzlaFPSymProp res(valid);
  bzla_node_release(s_bzla, max);
  bzla_node_release(s_bzla, valid);
  return res;
}

BzlaFPSymProp
BzlaFPSymRM::operator==(const BzlaFPSymRM &other) const
{
  assert(d_node);
  assert(other.d_node);
  BzlaNode *eq = bzla_exp_eq(s_bzla, d_node, other.d_node);
  BzlaFPSymProp res(eq);
  bzla_node_release(s_bzla, eq);
  return res;
}

bool
BzlaFPSymRM::checkNode(const BzlaNode *node) const
{
  assert(s_bzla);
  assert(node);

  if (!bzla_node_is_bv(s_bzla, node))
  {
    return false;
  }
#ifdef BZLA_USE_SYMFPU
  assert((((uint32_t) 1u) << BZLA_RM_BW) >= SYMFPU_NUMBER_OF_ROUNDING_MODES);
  return bzla_node_bv_get_width(s_bzla, node) == BZLA_RM_BW;
#else
  return false;
#endif
}

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class BzlaFPSymTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = BzlaFPSymRM;
  using fpt  = BzlaFPSortInfo;
  using prop = BzlaFPSymProp;
  using sbv  = BzlaFPSymBV<true>;
  using ubv  = BzlaFPSymBV<false>;

  /* Give concrete instances (wrapped nodes) for each rounding mode. */
  static BzlaFPSymRM RNE(void);
  static BzlaFPSymRM RNA(void);
  static BzlaFPSymRM RTP(void);
  static BzlaFPSymRM RTN(void);
  static BzlaFPSymRM RTZ(void);

  /* Properties used by Symfpu. */
  static void precondition(const bool b);
  static void postcondition(const bool b);
  static void invariant(const bool b);
  static void precondition(const prop &p);
  static void postcondition(const prop &p);
  static void invariant(const prop &p);
};

/* -------------------------------------------------------------------------- */

BzlaFPSymRM
BzlaFPSymTraits::RNE(void)
{
  return BZLA_RM_RNE;
}

BzlaFPSymRM
BzlaFPSymTraits::RNA(void)
{
  return BZLA_RM_RNA;
}

BzlaFPSymRM
BzlaFPSymTraits::RTP(void)
{
  return BZLA_RM_RTP;
}

BzlaFPSymRM
BzlaFPSymTraits::RTN(void)
{
  return BZLA_RM_RTN;
}

BzlaFPSymRM
BzlaFPSymTraits::RTZ(void)
{
  return BZLA_RM_RTZ;
}

void
BzlaFPSymTraits::precondition(const bool b)
{
  assert(b);
  (void) b;
}

void
BzlaFPSymTraits::postcondition(const bool b)
{
  assert(b);
  (void) b;
}

void
BzlaFPSymTraits::invariant(const bool b)
{
  assert(b);
  (void) b;
}

void
BzlaFPSymTraits::precondition(const prop &p)
{
  (void) p;
}

void
BzlaFPSymTraits::postcondition(const prop &p)
{
  (void) p;
}

void
BzlaFPSymTraits::invariant(const prop &p)
{
  (void) p;
}

/* -------------------------------------------------------------------------- */
/* ITE specializations.                                                       */
/* -------------------------------------------------------------------------- */

#ifdef BZLA_USE_SYMFPU
namespace symfpu {

#define BZLA_FP_ITE(T)                                              \
  template <>                                                       \
  struct ite<bool, T>                                               \
  {                                                                 \
    static const T &iteOp(const bool &_c, const T &_t, const T &_e) \
    {                                                               \
      return _c ? _t : _e;                                          \
    }                                                               \
  };
BZLA_FP_ITE(BzlaFPTraits::rm);
BZLA_FP_ITE(BzlaFPTraits::prop);
BZLA_FP_ITE(BzlaFPTraits::sbv);
BZLA_FP_ITE(BzlaFPTraits::ubv);
#undef BZLA_FP_ITE

template <class T>
struct ite<BzlaFPSymProp, T>
{
  static const T iteOp(const BzlaFPSymProp &_c, const T &_t, const T &_e)
  {
    BzlaNode *c = _c.getNode();
    BzlaNode *t = _t.getNode();
    BzlaNode *e = _e.getNode();
    assert(c);
    assert(t);
    assert(e);
    Bzla *bzla = T::s_bzla;
    assert(bzla);
    assert(bzla == bzla_node_real_addr(c)->bzla);
    assert(bzla == bzla_node_real_addr(t)->bzla);
    assert(bzla == bzla_node_real_addr(e)->bzla);
    BzlaNode *ite = bzla_exp_cond(bzla, c, t, e);
    T res(ite);
    bzla_node_release(bzla, ite);
    return res;
  }
};

}  // namespace symfpu
#endif

/* ========================================================================== */

/* ========================================================================== */
/* Word blaster.                                                              */
/* ========================================================================== */

struct BzlaSortHashFunction
{
  size_t operator()(BzlaSortId sort) const { return sort; }
};

struct BzlaNodeHashFunction
{
  size_t operator()(BzlaNode *exp) const { return bzla_node_hash_by_id(exp); }
};

class BzlaFPWordBlaster
{
 public:
  BzlaFPWordBlaster(Bzla *bzla) : d_bzla(bzla) {}

  BzlaNode *word_blast(BzlaNode *node);
  BzlaNode *get_word_blasted_node(BzlaNode *node);

  BzlaFPWordBlaster *clone(Bzla *cbzla, BzlaNodeMap *exp_map);

  Bzla *get_bzla() { return d_bzla; }

  static void set_s_bzla(Bzla *bzla)
  {
    BzlaFPSortInfo::s_bzla     = bzla;
    BzlaFPBV<true>::s_bzla     = bzla;
    BzlaFPBV<false>::s_bzla    = bzla;
    BzlaFPSymRM::s_bzla        = bzla;
    BzlaFPSymProp::s_bzla      = bzla;
    BzlaFPSymBV<true>::s_bzla  = bzla;
    BzlaFPSymBV<false>::s_bzla = bzla;
  }

  static void unset_s_bzla(void)
  {
    BzlaFPSortInfo::s_bzla     = nullptr;
    BzlaFPBV<true>::s_bzla     = nullptr;
    BzlaFPBV<false>::s_bzla    = nullptr;
    BzlaFPSymRM::s_bzla        = nullptr;
    BzlaFPSymProp::s_bzla      = nullptr;
    BzlaFPSymBV<true>::s_bzla  = nullptr;
    BzlaFPSymBV<false>::s_bzla = nullptr;
  }

 private:
  using BzlaSymUnpackedFloat = ::symfpu::unpackedFloat<BzlaFPSymTraits>;
  using BzlaFPSortInfoMap =
      std::unordered_map<BzlaSortId, BzlaFPSortInfo, BzlaSortHashFunction>;
  using BzlaFPSymRMMap =
      std::unordered_map<BzlaNode *, BzlaFPSymRM, BzlaNodeHashFunction>;
  using BzlaFPSymPropMap =
      std::unordered_map<BzlaNode *, BzlaFPSymProp, BzlaNodeHashFunction>;
  using BzlaFPUnpackedFloatMap = std::
      unordered_map<BzlaNode *, BzlaSymUnpackedFloat, BzlaNodeHashFunction>;
  using BzlaFPPackedFloatMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<false>, BzlaNodeHashFunction>;
  // using BzlaFPSymSBVMap =
  //    std::unordered_map<BzlaNode *, BzlaFPSymBV<true>, BzlaNodeHashFunction>;

  BzlaFPSortInfoMap d_sort_map;
  BzlaFPSymRMMap d_rm_map;
  BzlaFPSymPropMap d_prop_map;
  // BzlaFPSymUBVMap d_ubv_map;
  // BzlaFPSymSBVMap d_sbv_map;
  BzlaFPUnpackedFloatMap d_unpacked_float_map;
  BzlaFPPackedFloatMap d_packed_float_map;

  Bzla *d_bzla;
};

/* -------------------------------------------------------------------------- */

static BzlaUnpackedFloat *
fp_get_unpacked_float(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<BzlaUnpackedFloat *>(bzla_fp_get_fp(node)->fp);
}

static std::string
create_component_symbol(BzlaNode *node, const char *s)
{
  assert(node);
  assert(s);
  std::stringstream ss;
  ss << "_fp_" << s << "_"
     << bzla_node_get_symbol(bzla_node_real_addr(node)->bzla, node);
  return ss.str();
}

BzlaNode *
BzlaFPWordBlaster::word_blast(BzlaNode *node)
{
  assert(d_bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(d_bzla == bzla_node_real_addr(node)->bzla);
  assert((bzla_sort_is_bool(d_bzla, bzla_node_get_sort_id(node)) && node->arity
          && (bzla_node_is_fp(d_bzla, node->e[0])
              || bzla_node_is_rm(d_bzla, node->e[0])))
         || bzla_node_is_fp(d_bzla, node) || bzla_node_is_rm(d_bzla, node));

  BzlaNode *res = nullptr;

#ifdef BZLA_USE_SYMFPU
  BzlaNode *cur;
  std::vector<BzlaNode *> to_visit;
  std::unordered_map<BzlaNode *, uint32_t, BzlaNodeHashFunction> visited;

  to_visit.push_back(node);

  while (!to_visit.empty())
  {
    cur = to_visit.back();
    to_visit.pop_back();
    assert(bzla_node_is_regular(cur));

    if (d_prop_map.find(cur) != d_prop_map.end()
        || d_unpacked_float_map.find(cur) != d_unpacked_float_map.end())
    {
      continue;
    }

    if (visited.find(cur) == visited.end())
    {
      visited.emplace(cur, 0);
      to_visit.push_back(cur);

      for (uint32_t i = 0; i < cur->arity; ++i)
      {
        to_visit.push_back(cur->e[i]);
      }
    }
    else if (visited.at(cur) == 0)
    {
      if (bzla_node_is_rm_const(cur))
      {
        d_rm_map.emplace(cur, BzlaFPSymRM(bzla_node_rm_const_get_rm(cur)));
      }
      else if (bzla_node_is_fp_const(cur))
      {
        d_unpacked_float_map.emplace(
            cur, BzlaSymUnpackedFloat(*fp_get_unpacked_float(cur)));
      }
      else if (bzla_node_is_fp_var(cur))
      {
        BzlaSortId sort   = bzla_node_get_sort_id(cur);
        BzlaSortId sort_1 = bzla_sort_bv(d_bzla, 1);
        BzlaSortId sort_exp =
            bzla_sort_bv(d_bzla, BzlaSymUnpackedFloat::exponentWidth(sort));
        BzlaSortId sort_sig =
            bzla_sort_bv(d_bzla, BzlaSymUnpackedFloat::significandWidth(sort));

        BzlaNode *inf = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "inf").c_str());
        BzlaNode *nan = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "nan").c_str());
        BzlaNode *sign = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "sign").c_str());
        BzlaNode *zero = bzla_exp_var(
            d_bzla, sort_1, create_component_symbol(cur, "zero").c_str());
        BzlaNode *exp = bzla_exp_var(
            d_bzla, sort_exp, create_component_symbol(cur, "exp").c_str());
        BzlaNode *sig = bzla_exp_var(
            d_bzla, sort_sig, create_component_symbol(cur, "sig").c_str());

        BzlaSymUnpackedFloat uf(nan, inf, zero, sign, exp, sig);
        d_unpacked_float_map.emplace(cur, uf);
        BzlaFPSymProp assertion = uf.valid(sort);
        bzla_assert_exp(d_bzla, assertion.getNode());

        bzla_node_release(d_bzla, sig);
        bzla_node_release(d_bzla, exp);
        bzla_node_release(d_bzla, zero);
        bzla_node_release(d_bzla, sign);
        bzla_node_release(d_bzla, nan);
        bzla_node_release(d_bzla, inf);
        bzla_sort_release(d_bzla, sort_sig);
        bzla_sort_release(d_bzla, sort_exp);
        bzla_sort_release(d_bzla, sort_1);
      }
      else if (bzla_node_is_fp_eq(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(cur,
                           symfpu::smtlibEqual<BzlaFPSymTraits>(
                               BzlaFPSortInfo(bzla_node_get_sort_id(cur->e[0])),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_rm_eq(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_rm_map.find(cur->e[1]) != d_rm_map.end());
        d_prop_map.emplace(cur,
                           d_rm_map.at(cur->e[0]) == d_rm_map.at(cur->e[1]));
      }
      else if (bzla_node_is_fp_abs(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(cur,
                                     symfpu::absolute<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_neg(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(cur,
                                     symfpu::negate<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_normal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(cur,
                           symfpu::isNormal<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_subnormal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(cur,
                           symfpu::isSubnormal<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_zero(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(cur,
                           symfpu::isZero<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_inf(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(cur,
                           symfpu::isInfinite<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_nan(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(
            cur,
            symfpu::isNaN<BzlaFPSymTraits>(bzla_node_get_sort_id(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[0])));
      }
      visited.at(cur) = 1;
    }
    else
    {
      assert(visited.at(cur) == 1);
      continue;
    }
  }

  if (d_prop_map.find(node) != d_prop_map.end())
  {
    assert(bzla_sort_is_bool(d_bzla, bzla_node_get_sort_id(node)));
    res = d_prop_map.at(node).getNode();
  }
  else
  {
    assert(d_unpacked_float_map.find(node) != d_unpacked_float_map.end());
    d_packed_float_map.emplace(node,
                               symfpu::pack(bzla_node_get_sort_id(node),
                                            d_unpacked_float_map.at(node)));
    res = d_packed_float_map.at(node).getNode();
  }
  assert(res);
#endif
  return res;
}

BzlaNode *
BzlaFPWordBlaster::get_word_blasted_node(BzlaNode *node)
{
  assert(d_bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(d_bzla == node->bzla);

  if (d_packed_float_map.find(node) != d_packed_float_map.end())
  {
    return d_packed_float_map.at(node).getNode();
  }

  if (bzla_sort_is_bool(d_bzla, bzla_node_get_sort_id(node))
      && d_prop_map.find(node) != d_prop_map.end())
  {
    return d_prop_map.at(node).getNode();
  }

  if (bzla_node_is_rm(d_bzla, node) && d_rm_map.find(node) != d_rm_map.end())
  {
    return d_rm_map.at(node).getNode();
  }

  if (d_unpacked_float_map.find(node) != d_unpacked_float_map.end())
  {
    d_packed_float_map.emplace(node,
                               symfpu::pack(bzla_node_get_sort_id(node),
                                            d_unpacked_float_map.at(node)));
    return d_packed_float_map.at(node).getNode();
  }

  return word_blast(node);
}

BzlaFPWordBlaster *
BzlaFPWordBlaster::clone(Bzla *cbzla, BzlaNodeMap *exp_map)
{
  BzlaNode *exp, *cexp;
  BzlaFPWordBlaster *res = new BzlaFPWordBlaster(cbzla);
  res->d_sort_map        = BzlaFPSortInfoMap(d_sort_map);

  for (const auto &r : d_rm_map)
  {
    exp = r.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_rm_map.find(cexp) == res->d_rm_map.end());

    BzlaNode *sexp  = d_rm_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_rm_map.emplace(exp, BzlaFPSymRM(scexp));
  }
  for (const auto &p : d_prop_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_prop_map.find(cexp) == res->d_prop_map.end());

    BzlaNode *sexp  = d_prop_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_prop_map.emplace(exp, BzlaFPSymProp(scexp));
  }
  for (const auto &p : d_unpacked_float_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_unpacked_float_map.find(cexp)
           == res->d_unpacked_float_map.end());

    BzlaNode *nan = p.second.getNaN().getNode();
    assert(nan);
    BzlaNode *cnan = bzla_nodemap_mapped(exp_map, nan);
    assert(cnan);

    BzlaNode *inf = p.second.getInf().getNode();
    assert(inf);
    BzlaNode *cinf = bzla_nodemap_mapped(exp_map, inf);
    assert(cinf);

    BzlaNode *zero = p.second.getZero().getNode();
    assert(zero);
    BzlaNode *czero = bzla_nodemap_mapped(exp_map, zero);
    assert(czero);

    BzlaNode *sign = p.second.getSign().getNode();
    assert(sign);
    BzlaNode *csign = bzla_nodemap_mapped(exp_map, sign);
    assert(csign);

    BzlaNode *expo = p.second.getExponent().getNode();
    assert(expo);
    BzlaNode *cexpo = bzla_nodemap_mapped(exp_map, expo);
    assert(cexpo);

    BzlaNode *sig = p.second.getSignificand().getNode();
    assert(sig);
    BzlaNode *csig = bzla_nodemap_mapped(exp_map, sig);
    assert(csig);

    res->d_unpacked_float_map.emplace(
        cexp,
        BzlaSymUnpackedFloat(BzlaFPSymProp(cnan),
                             BzlaFPSymProp(cinf),
                             BzlaFPSymProp(czero),
                             BzlaFPSymProp(csign),
                             BzlaFPSymBV<true>(cexpo),
                             BzlaFPSymBV<false>(csig)));
  }
  return res;
}

/* ========================================================================== */

BzlaFloatingPoint *
bzla_fp_new(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
  uint32_t ewidth = bzla_sort_fp_get_exp_width(bzla, sort);
  uint32_t swidth = bzla_sort_fp_get_sig_width(bzla, sort);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(ewidth, swidth);
  return res;
}

void
bzla_fp_free(Bzla *bzla, BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  delete fp->size;
  delete fp->fp;
  BZLA_DELETE(bzla->mm, fp);
  BzlaFPWordBlaster::unset_s_bzla();
}

BzlaFloatingPoint *
bzla_fp_copy(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
  BzlaSortId sort;

  BzlaFPWordBlaster::set_s_bzla(bzla);
  sort = bzla_sort_fp(
      bzla, fp->size->exponentWidth(), fp->size->significandWidth());
  res     = bzla_fp_new(bzla, sort);
  res->fp = new BzlaUnpackedFloat(*fp->fp);
  bzla_sort_release(bzla, sort);
  BzlaFPWordBlaster::unset_s_bzla();
  return res;
}

uint32_t
bzla_fp_get_exp_width(const BzlaFloatingPoint *fp)
{
  return fp->size->exponentWidth();
}

uint32_t
bzla_fp_get_sig_width(const BzlaFloatingPoint *fp)
{
  return fp->size->significandWidth();
}

BzlaFloatingPoint *
bzla_fp_get_fp(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<BzlaFloatingPoint *>(((BzlaFPConstNode *) node)->fp);
}

size_t
bzla_fp_get_bytes(BzlaNode *node)
{
  assert(bzla_node_is_fp_const(node));
  BzlaFloatingPoint *fp = bzla_fp_get_fp(node);
  BzlaUnpackedFloat *uf = fp->fp;
  BzlaBitVector *bv_exp = uf->getExponent().getBv();
  BzlaBitVector *bv_sig = uf->getSignificand().getBv();
  return sizeof(BzlaFloatingPoint) + bzla_bv_size(bv_exp)
         + bzla_bv_size(bv_sig);
}

static uint32_t hash_primes[] = {
    333444569u, 111130391u, 22237357u, 33355519u, 456790003u, 76891121u};

uint32_t
bzla_fp_hash(const BzlaFloatingPoint *fp)
{
  assert(fp);
  uint32_t hash = 0;

  BzlaUnpackedFloat *uf = fp->fp;

  hash += uf->getNaN() * hash_primes[0];
  hash += uf->getInf() * hash_primes[1];
  hash += uf->getZero() * hash_primes[2];
  hash += uf->getSign() * hash_primes[3];
  hash += bzla_bv_hash(uf->getExponent().getBv()) * hash_primes[4];
  hash += bzla_bv_hash(uf->getSignificand().getBv()) * hash_primes[5];
  return hash;
}

int32_t
bzla_fp_compare(const BzlaFloatingPoint *a, const BzlaFloatingPoint *b)
{
  assert(a);
  assert(b);

  BzlaUnpackedFloat *uf_a, *uf_b;
  BzlaBitVector *exp_a, *sig_a, *exp_b, *sig_b;

  uf_a = a->fp;
  uf_b = b->fp;

  exp_a = uf_a->getExponent().getBv();
  sig_a = uf_a->getSignificand().getBv();

  exp_b = uf_b->getExponent().getBv();
  sig_b = uf_b->getSignificand().getBv();

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

BzlaFloatingPoint *
bzla_fp_make_zero(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = bzla_fp_new(bzla, sort);
  res->fp =
      new BzlaUnpackedFloat(BzlaUnpackedFloat::makeZero(*res->size, sign));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_make_inf(Bzla *bzla, BzlaSortId sort, bool sign)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res     = bzla_fp_new(bzla, sort);
  res->fp = new BzlaUnpackedFloat(BzlaUnpackedFloat::makeInf(*res->size, sign));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_make_nan(Bzla *bzla, BzlaSortId sort)
{
  assert(bzla);
  assert(sort);
  assert(bzla_sort_is_fp(bzla, sort));

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res     = bzla_fp_new(bzla, sort);
  res->fp = new BzlaUnpackedFloat(BzlaUnpackedFloat::makeNaN(*res->size));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_make_const(Bzla *bzla, BzlaSortId sort, BzlaBitVector *bv_const)
{
  assert(bzla);
  assert(sort);
  assert(bv_const);
  assert(bzla_sort_is_fp(bzla, sort));
  assert(bzla_sort_fp_get_exp_width(bzla, sort)
             + bzla_sort_fp_get_sig_width(bzla, sort)
         == bzla_bv_get_width(bv_const));
  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res     = bzla_fp_new(bzla, sort);
  res->fp = new BzlaUnpackedFloat(symfpu::unpack<BzlaFPTraits>(
      *res->size, bzla_bv_copy(bzla->mm, bv_const)));
#else
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

/* ========================================================================== */

void *
bzla_fp_word_blaster_new(Bzla *bzla)
{
  return new BzlaFPWordBlaster(bzla);
}

void *
bzla_fp_word_blaster_clone(Bzla *bzla, Bzla *clone, BzlaNodeMap *exp_map)
{
  assert(bzla);
  assert(bzla->word_blaster);
  assert(clone);
  assert(exp_map);
  BzlaFPWordBlaster::set_s_bzla(clone);
  return static_cast<BzlaFPWordBlaster *>(bzla->word_blaster)
      ->clone(clone, exp_map);
  BzlaFPWordBlaster::unset_s_bzla();
}

void
bzla_fp_word_blaster_delete(Bzla *bzla)
{
  assert(bzla);
  if (!bzla->word_blaster) return;
  BzlaFPWordBlaster *wb = static_cast<BzlaFPWordBlaster *>(bzla->word_blaster);
  BzlaFPWordBlaster::set_s_bzla(wb->get_bzla());
  delete wb;
  bzla->word_blaster = nullptr;
  BzlaFPWordBlaster::unset_s_bzla();
}

BzlaNode *
bzla_fp_word_blast(Bzla *bzla, BzlaNode *node)
{
  assert(bzla);
  assert(bzla->word_blaster);
  assert(node);
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BzlaNode *res = static_cast<BzlaFPWordBlaster *>(bzla->word_blaster)
                      ->get_word_blasted_node(node);
  BzlaFPWordBlaster::unset_s_bzla();
  return bzla_simplify_exp(bzla, res);
}

/* -------------------------------------------------------------------------- */
