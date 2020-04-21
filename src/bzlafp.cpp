/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019-2020 Aina Niemetz.
 *  Copyright (C) 2020 Mathias Preiner.
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
#include "utils/bzlamem.h"
#include "utils/bzlautil.h"
}

#ifdef BZLA_USE_SYMFPU
#include "symfpu/core/add.h"
#include "symfpu/core/classify.h"
#include "symfpu/core/compare.h"
#include "symfpu/core/convert.h"
#include "symfpu/core/divide.h"
#include "symfpu/core/fma.h"
#include "symfpu/core/ite.h"
#include "symfpu/core/multiply.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/remainder.h"
#include "symfpu/core/sign.h"
#include "symfpu/core/sqrt.h"
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

  BzlaFPBV<is_signed> operator=(const BzlaFPBV<is_signed> &other);

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
BzlaFPBV<is_signed>::operator=(const BzlaFPBV<is_signed> &other)
{
  assert(s_bzla);
  assert(d_bv);
  return bzla_bv_copy(s_bzla->mm, other.d_bv);
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

#ifdef BZLA_USE_SYMFPU
using BzlaUnpackedFloat = ::symfpu::unpackedFloat<BzlaFPTraits>;
#endif

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
  bool check_node(const BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

Bzla *BzlaFPSymProp::s_bzla = nullptr;

BzlaFPSymProp::BzlaFPSymProp(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
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
  assert(check_node(other.d_node));
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
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator||(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator==(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaFPSymProp
BzlaFPSymProp::operator^(const BzlaFPSymProp &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  BzlaFPSymProp res = BzlaFPSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

bool
BzlaFPSymProp::check_node(const BzlaNode *node) const
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

  bool check_node(const BzlaNode *node) const;
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
  assert(check_node(node));
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
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
BzlaFPSymBV<is_signed>::BzlaFPSymBV(const BzlaFPSymBV<!is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
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
BzlaFPSymBV<is_signed> &
BzlaFPSymBV<is_signed>::operator=(const BzlaFPSymBV<is_signed> &other)
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
  assert(check_node(op.d_node));
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
BzlaFPSymBV<is_signed>::check_node(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node));
}

template <bool is_signed>
bool
BzlaFPSymBV<is_signed>::checkBooleanNode(const BzlaNode *node) const
{
  assert(check_node(node));
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
  bool check_node(const BzlaNode *node) const;

 private:
  BzlaNode *init_const(const uint32_t val);
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

Bzla *BzlaFPSymRM::s_bzla = nullptr;

BzlaNode *
BzlaFPSymRM::init_const(const uint32_t val)
{
  assert(s_bzla);
  assert(bzla_rm_is_valid(val));
  BzlaMemMgr *mm    = s_bzla->mm;
  BzlaBitVector *rm = bzla_bv_uint64_to_bv(mm, val, BZLA_RM_BW);
  BzlaNode *res     = bzla_exp_bv_const(s_bzla, rm);
  bzla_bv_free(mm, rm);
  return res;
}

BzlaFPSymRM::BzlaFPSymRM(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
  if (bzla_node_is_bv(s_bzla, node))
  {
    d_node = bzla_node_copy(s_bzla, node);
  }
  else if (bzla_node_is_rm_const(node))
  {
    d_node = init_const(bzla_node_rm_const_get_rm(node));
  }
  else
  {
    assert(bzla_node_is_rm_var(node));
    BzlaSortId sort = bzla_sort_bv(s_bzla, BZLA_RM_BW);
    std::stringstream ss;
    ss << "_rm_var_" << bzla_node_get_id(node) << "_";
    d_node = bzla_exp_var(s_bzla, sort, ss.str().c_str());
    bzla_sort_release(s_bzla, sort);
  }
}

BzlaFPSymRM::BzlaFPSymRM(const uint32_t val)
{
  assert(s_bzla);
  d_node = init_const(val);
  assert(check_node(d_node));
}

BzlaFPSymRM::BzlaFPSymRM(const BzlaFPSymRM &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
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
BzlaFPSymRM::check_node(const BzlaNode *node) const
{
  assert(s_bzla);
  assert(node);
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
#ifdef BZLA_USE_SYMFPU
  assert((((uint32_t) 1u) << BZLA_RM_BW) >= SYMFPU_NUMBER_OF_ROUNDING_MODES);
  return (bzla_node_is_bv(s_bzla, node)
          && bzla_node_bv_get_width(s_bzla, node) == BZLA_RM_BW)
         || bzla_node_is_rm(s_bzla, node);
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

#define BZLA_FP_SYM_ITE(T)                                                  \
  template <>                                                               \
  struct ite<BzlaFPSymProp, T>                                              \
  {                                                                         \
    static const T iteOp(const BzlaFPSymProp &_c, const T &_t, const T &_e) \
    {                                                                       \
      BzlaNode *c = _c.getNode();                                           \
      BzlaNode *t = _t.getNode();                                           \
      BzlaNode *e = _e.getNode();                                           \
      assert(c);                                                            \
      assert(t);                                                            \
      assert(e);                                                            \
      Bzla *bzla = T::s_bzla;                                               \
      assert(bzla);                                                         \
      assert(bzla == bzla_node_real_addr(c)->bzla);                         \
      assert(bzla == bzla_node_real_addr(t)->bzla);                         \
      assert(bzla == bzla_node_real_addr(e)->bzla);                         \
      BzlaNode *ite = bzla_exp_cond(bzla, c, t, e);                         \
      T res(ite);                                                           \
      bzla_node_release(bzla, ite);                                         \
      return res;                                                           \
    }                                                                       \
  };
BZLA_FP_SYM_ITE(BzlaFPSymTraits::rm);
BZLA_FP_SYM_ITE(BzlaFPSymTraits::prop);
BZLA_FP_SYM_ITE(BzlaFPSymTraits::sbv);
BZLA_FP_SYM_ITE(BzlaFPSymTraits::ubv);
#undef BZLA_FP_SYM_ITE

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

struct BzlaSortPairHashFunction
{
  size_t operator()(const std::pair<BzlaSortId, BzlaSortId> &p) const
  {
    return p.first * 333444569u + p.second * 76891121u;
  }
};

struct BzlaNodeHashFunction
{
  size_t operator()(BzlaNode *exp) const { return bzla_node_hash_by_id(exp); }
};

class BzlaFPWordBlaster
{
 public:
  BzlaFPWordBlaster(Bzla *bzla) : d_bzla(bzla) {}
  ~BzlaFPWordBlaster();

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
  BzlaNode *min_max_uf(BzlaNode *node);
  BzlaNode *sbv_ubv_uf(BzlaNode *node);

#ifdef BZLA_USE_SYMFPU
  using BzlaSymUnpackedFloat   = ::symfpu::unpackedFloat<BzlaFPSymTraits>;
  using BzlaFPUnpackedFloatMap = std::
      unordered_map<BzlaNode *, BzlaSymUnpackedFloat, BzlaNodeHashFunction>;
#endif
  using BzlaFPSymRMMap =
      std::unordered_map<BzlaNode *, BzlaFPSymRM, BzlaNodeHashFunction>;
  using BzlaFPSymPropMap =
      std::unordered_map<BzlaNode *, BzlaFPSymProp, BzlaNodeHashFunction>;
  using BzlaFPPackedFloatMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<false>, BzlaNodeHashFunction>;
  using BzlaFPSymSBVMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<true>, BzlaNodeHashFunction>;
  using BzlaFPSymUBVMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<false>, BzlaNodeHashFunction>;

  BzlaFPSymRMMap d_rm_map;
  BzlaFPSymPropMap d_prop_map;
  BzlaFPSymUBVMap d_ubv_map;
  BzlaFPSymSBVMap d_sbv_map;
#ifdef BZLA_USE_SYMFPU
  BzlaFPUnpackedFloatMap d_unpacked_float_map;
#endif
  BzlaFPPackedFloatMap d_packed_float_map;

  std::unordered_map<BzlaSortId, BzlaNode *, BzlaSortHashFunction>
      d_min_max_uf_map;

  std::unordered_map<std::pair<BzlaSortId, BzlaSortId>,
                     BzlaNode *,
                     BzlaSortPairHashFunction>
      d_sbv_ubv_uf_map;

  std::unordered_map<BzlaNode *, BzlaNode *, BzlaNodeHashFunction> d_ite_map;
  Bzla *d_bzla;
};

/* -------------------------------------------------------------------------- */

#ifdef BZLA_USE_SYMFPU
static BzlaUnpackedFloat *
fp_get_unpacked_float(BzlaNode *node)
{
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_fp_const(node));
  return static_cast<BzlaUnpackedFloat *>(bzla_fp_get_fp(node)->fp);
}
#endif

#ifdef BZLA_USE_SYMFPU
static std::string
create_component_symbol(BzlaNode *node, const char *s)
{
  assert(node);
  assert(s);
  std::stringstream ss;
  ss << "_fp_var_" << bzla_node_get_id(node) << s << "_component_";
  return ss.str();
}
#endif

BzlaFPWordBlaster::~BzlaFPWordBlaster()
{
  for (const auto &p : d_min_max_uf_map)
  {
    bzla_sort_release(d_bzla, p.first);
    bzla_node_release(d_bzla, p.second);
  }
  for (const auto &p : d_sbv_ubv_uf_map)
  {
    bzla_sort_release(d_bzla, p.first.first);
    bzla_sort_release(d_bzla, p.first.second);
    bzla_node_release(d_bzla, p.second);
  }
  for (const auto &p : d_ite_map)
  {
    bzla_node_release(d_bzla, p.first);
    bzla_node_release(d_bzla, p.second);
  }
#ifdef BZLA_USE_SYMFPU
  for (const auto &p : d_unpacked_float_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
#endif
  for (const auto &p : d_rm_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_prop_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_ubv_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
  for (const auto &p : d_sbv_map)
  {
    bzla_node_release(d_bzla, p.first);
  }
}

BzlaNode *
BzlaFPWordBlaster::word_blast(BzlaNode *node)
{
  assert(d_bzla);
  assert(node);
  assert(bzla_node_is_regular(node));
  assert(d_bzla == bzla_node_real_addr(node)->bzla);
  assert((bzla_node_is_bv(d_bzla, node) && node->arity
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
    cur = bzla_node_real_addr(to_visit.back());
    assert(!cur->parameterized);
    to_visit.pop_back();

    if (d_prop_map.find(cur) != d_prop_map.end()
        || d_rm_map.find(cur) != d_rm_map.end()
        || d_sbv_map.find(cur) != d_sbv_map.end()
        || d_ubv_map.find(cur) != d_ubv_map.end()
        || d_unpacked_float_map.find(cur) != d_unpacked_float_map.end())
    {
      continue;
    }

    if (visited.find(cur) == visited.end())
    {
      visited.emplace(cur, 0);
      to_visit.push_back(cur);

      if (bzla_node_is_cond(cur)
          && (bzla_node_is_rm(d_bzla, cur->e[1])
              || bzla_node_is_fp(d_bzla, cur->e[1])))
      {
        std::stringstream ss;
        ss << "_fp_ite_" << bzla_node_get_id(cur) << "_";
        BzlaNode *var =
            bzla_exp_var(d_bzla, bzla_node_get_sort_id(cur), ss.str().c_str());
        to_visit.push_back(var);
        d_ite_map.emplace(bzla_node_copy(d_bzla, cur), var);
      }

      for (uint32_t i = 0; i < cur->arity; ++i)
      {
        to_visit.push_back(cur->e[i]);
      }
    }
    else if (visited.at(cur) == 0)
    {
      if (bzla_node_is_cond(cur)
          && (bzla_node_is_rm(d_bzla, cur->e[1])
              || bzla_node_is_fp(d_bzla, cur->e[1])))
      {
        assert(d_ite_map.find(cur) != d_ite_map.end());
        BzlaNode *var = d_ite_map.at(cur);

        if (bzla_node_is_rm(d_bzla, cur->e[1]))
        {
          assert(d_rm_map.find(var) != d_rm_map.end());
          d_rm_map.emplace(bzla_node_copy(d_bzla, cur), d_rm_map.at(var));
        }
        else
        {
          assert(d_unpacked_float_map.find(var) != d_unpacked_float_map.end());
          d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                       d_unpacked_float_map.at(var));
        }
        BzlaNode *then_eq  = bzla_exp_eq(d_bzla, var, cur->e[1]);
        BzlaNode *else_eq  = bzla_exp_eq(d_bzla, var, cur->e[2]);
        BzlaNode *then_imp = bzla_exp_implies(d_bzla, cur->e[0], then_eq);
        BzlaNode *else_imp =
            bzla_exp_implies(d_bzla, bzla_node_invert(cur->e[0]), else_eq);
        bzla_assert_exp(d_bzla, then_imp);
        bzla_assert_exp(d_bzla, else_imp);
        bzla_node_release(d_bzla, else_imp);
        bzla_node_release(d_bzla, then_imp);
        bzla_node_release(d_bzla, else_eq);
        bzla_node_release(d_bzla, then_eq);
      }
      else if (bzla_node_is_rm_const(cur))
      {
        d_rm_map.emplace(bzla_node_copy(d_bzla, cur), BzlaFPSymRM(cur));
      }
      else if (bzla_node_is_rm_var(cur)
               || (bzla_node_is_apply(cur) && bzla_node_is_rm(d_bzla, cur)))
      {
        BzlaFPSymRM var(cur);
        d_rm_map.emplace(bzla_node_copy(d_bzla, cur), var);
        BzlaFPSymProp assertion = var.valid();
        bzla_assert_exp(d_bzla, assertion.getNode());
      }
      else if (bzla_node_is_fp_const(cur))
      {
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            BzlaSymUnpackedFloat(*fp_get_unpacked_float(cur)));
      }
      else if (bzla_node_is_fp_var(cur)
               || (bzla_node_is_apply(cur) && bzla_node_is_fp(d_bzla, cur)))
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
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur), uf);
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
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::smtlibEqual<BzlaFPSymTraits>(
                               BzlaFPSortInfo(bzla_node_get_sort_id(cur->e[0])),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_rm_eq(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_rm_map.find(cur->e[1]) != d_rm_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           d_rm_map.at(cur->e[0]) == d_rm_map.at(cur->e[1]));
      }
      else if (bzla_node_is_fp_abs(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::absolute<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_neg(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::negate<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_normal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isNormal<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_subnormal(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isSubnormal<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_zero(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isZero<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_inf(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isInfinite<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_nan(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::isNaN<BzlaFPSymTraits>(bzla_node_get_sort_id(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_neg(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isNegative<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_is_pos(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::isPositive<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0])));
      }
      else if (bzla_node_is_fp_lte(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::lessThanOrEqual<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_lt(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_prop_map.emplace(bzla_node_copy(d_bzla, cur),
                           symfpu::lessThan<BzlaFPSymTraits>(
                               bzla_node_get_sort_id(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[0]),
                               d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_min(cur) || bzla_node_is_fp_max(cur))
      {
        assert(cur->arity == 2);
        BzlaNode *uf = min_max_uf(cur);
        BzlaNode *args[2];
        for (uint32_t i = 0; i < cur->arity; ++i)
        {
          assert(d_unpacked_float_map.find(cur->e[i])
                 != d_unpacked_float_map.end());
          if (d_packed_float_map.find(cur->e[i]) == d_packed_float_map.end())
          {
            d_packed_float_map.emplace(
                cur->e[i],
                symfpu::pack(bzla_node_get_sort_id(cur->e[i]),
                             d_unpacked_float_map.at(cur->e[i])));
          }
          args[i] = d_packed_float_map.at(cur->e[i]).getNode();
        }
        BzlaNode *apply_args = bzla_exp_args(d_bzla, args, cur->arity);
        BzlaNode *apply      = bzla_exp_apply(d_bzla, uf, apply_args);
        if (bzla_node_is_fp_min(cur))
        {
          d_unpacked_float_map.emplace(
              bzla_node_copy(d_bzla, cur),
              symfpu::min<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                           d_unpacked_float_map.at(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[1]),
                                           apply));
        }
        else
        {
          d_unpacked_float_map.emplace(
              bzla_node_copy(d_bzla, cur),
              symfpu::max<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                           d_unpacked_float_map.at(cur->e[0]),
                                           d_unpacked_float_map.at(cur->e[1]),
                                           apply));
        }
        bzla_node_release(d_bzla, apply);
        bzla_node_release(d_bzla, apply_args);
      }
      else if (bzla_node_is_fp_rem(cur))
      {
        assert(d_unpacked_float_map.find(cur->e[0])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::remainder<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_unpacked_float_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_sqrt(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::sqrt<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                          d_rm_map.at(cur->e[0]),
                                          d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_rti(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::roundToIntegral<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_add(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::add<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2]),
                                         BzlaFPSymProp(true)));
      }
      else if (bzla_node_is_fp_mul(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::multiply<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2])));
      }
      else if (bzla_node_is_fp_div(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::divide<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2])));
      }
      else if (bzla_node_is_fp_fma(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[2])
               != d_unpacked_float_map.end());
        assert(d_unpacked_float_map.find(cur->e[3])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::fma<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         d_unpacked_float_map.at(cur->e[1]),
                                         d_unpacked_float_map.at(cur->e[2]),
                                         d_unpacked_float_map.at(cur->e[3])));
      }
      else if (bzla_node_is_fp_to_sbv(cur) || bzla_node_is_fp_to_ubv(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        uint32_t bw          = bzla_node_bv_get_width(d_bzla, cur);
        BzlaNode *uf         = sbv_ubv_uf(cur);
        BzlaNode *args[2]    = {cur->e[0], cur->e[1]};
        BzlaNode *apply_args = bzla_exp_args(d_bzla, args, cur->arity);
        BzlaNode *apply      = bzla_exp_apply(d_bzla, uf, apply_args);
        if (bzla_node_is_fp_to_sbv(cur))
        {
          d_sbv_map.emplace(bzla_node_copy(d_bzla, cur),
                            symfpu::convertFloatToSBV<BzlaFPSymTraits>(
                                bzla_node_get_sort_id(cur->e[1]),
                                d_rm_map.at(cur->e[0]),
                                d_unpacked_float_map.at(cur->e[1]),
                                bw,
                                BzlaFPSymBV<true>(apply)));
        }
        else
        {
          d_ubv_map.emplace(bzla_node_copy(d_bzla, cur),
                            symfpu::convertFloatToUBV<BzlaFPSymTraits>(
                                bzla_node_get_sort_id(cur->e[1]),
                                d_rm_map.at(cur->e[0]),
                                d_unpacked_float_map.at(cur->e[1]),
                                bw,
                                BzlaFPSymBV<false>(apply)));
        }
        bzla_node_release(d_bzla, apply);
        bzla_node_release(d_bzla, apply_args);
      }
      else if (bzla_node_is_fp_to_fp_from_bv(cur))
      {
        assert(bzla_node_is_bv(d_bzla, cur->e[0]));
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::unpack<BzlaFPSymTraits>(bzla_node_get_sort_id(cur),
                                            BzlaFPSymBV<false>(cur->e[0])));
      }
      else if (bzla_node_is_fp_to_fp_from_fp(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(d_unpacked_float_map.find(cur->e[1])
               != d_unpacked_float_map.end());
        d_unpacked_float_map.emplace(
            bzla_node_copy(d_bzla, cur),
            symfpu::convertFloatToFloat<BzlaFPSymTraits>(
                bzla_node_get_sort_id(cur->e[1]),
                bzla_node_get_sort_id(cur),
                d_rm_map.at(cur->e[0]),
                d_unpacked_float_map.at(cur->e[1])));
      }
      else if (bzla_node_is_fp_to_fp_from_int(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(bzla_node_is_bv(d_bzla, cur->e[1]));
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::convertSBVToFloat<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         BzlaFPSymBV<true>(cur->e[1])));
      }
      else if (bzla_node_is_fp_to_fp_from_uint(cur))
      {
        assert(d_rm_map.find(cur->e[0]) != d_rm_map.end());
        assert(bzla_node_is_bv(d_bzla, cur->e[1]));
        d_unpacked_float_map.emplace(bzla_node_copy(d_bzla, cur),
                                     symfpu::convertUBVToFloat<BzlaFPSymTraits>(
                                         bzla_node_get_sort_id(cur),
                                         d_rm_map.at(cur->e[0]),
                                         BzlaFPSymBV<false>(cur->e[1])));
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
  else if (d_rm_map.find(node) != d_rm_map.end())
  {
    assert(bzla_node_is_rm(d_bzla, node));
    res = d_rm_map.at(node).getNode();
  }
  else if (d_sbv_map.find(node) != d_sbv_map.end())
  {
    assert(bzla_node_is_fp_to_sbv(node));
    res = d_sbv_map.at(node).getNode();
  }
  else if (d_ubv_map.find(node) != d_ubv_map.end())
  {
    assert(bzla_node_is_fp_to_ubv(node));
    res = d_ubv_map.at(node).getNode();
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

#ifdef BZLA_USE_SYMFPU
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
#else
  return nullptr;
#endif
}

BzlaFPWordBlaster *
BzlaFPWordBlaster::clone(Bzla *cbzla, BzlaNodeMap *exp_map)
{
  BzlaNode *exp, *cexp;
  BzlaFPWordBlaster *res = new BzlaFPWordBlaster(cbzla);

  for (const auto &p : d_min_max_uf_map)
  {
    BzlaSortId s = p.first;
    exp          = p.second;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_min_max_uf_map.find(s) == res->d_min_max_uf_map.end());
    res->d_min_max_uf_map.emplace(s, cexp);
  }
  for (const auto &p : d_sbv_ubv_uf_map)
  {
    exp = p.second;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_sbv_ubv_uf_map.find(p.first) == res->d_sbv_ubv_uf_map.end());
    res->d_sbv_ubv_uf_map.emplace(p.first, cexp);
  }
  for (const auto &p : d_rm_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_rm_map.find(cexp) == res->d_rm_map.end());

    BzlaNode *sexp  = d_rm_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_rm_map.emplace(cexp, BzlaFPSymRM(scexp));
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
    res->d_prop_map.emplace(cexp, BzlaFPSymProp(scexp));
  }
  for (const auto &p : d_sbv_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_sbv_map.find(cexp) == res->d_sbv_map.end());

    BzlaNode *sexp  = d_sbv_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_sbv_map.emplace(cexp, BzlaFPSymBV<true>(scexp));
  }
  for (const auto &p : d_ubv_map)
  {
    exp = p.first;
    assert(bzla_node_is_regular(exp));
    cexp = bzla_nodemap_mapped(exp_map, exp);
    assert(cexp);
    assert(res->d_ubv_map.find(cexp) == res->d_ubv_map.end());

    BzlaNode *sexp  = d_ubv_map.at(exp).getNode();
    BzlaNode *scexp = bzla_nodemap_mapped(exp_map, sexp);
    assert(scexp);
    res->d_ubv_map.emplace(cexp, BzlaFPSymBV<false>(scexp));
  }
#ifdef BZLA_USE_SYMFPU
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
#endif
  return res;
}

BzlaNode *
BzlaFPWordBlaster::min_max_uf(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));

  BzlaSortId sort_fp = bzla_node_get_sort_id(node);

  if (d_min_max_uf_map.find(sort_fp) != d_min_max_uf_map.end())
    return d_min_max_uf_map.at(sort_fp);

  uint32_t arity      = node->arity;
  uint32_t bw         = bzla_sort_fp_get_bv_width(d_bzla, sort_fp);
  BzlaSortId sort_bv1 = bzla_sort_bv(d_bzla, 1);
  BzlaSortId sort_bv  = bzla_sort_bv(d_bzla, bw);
  BzlaSortId sorts[2];
  for (uint32_t i = 0; i < arity; ++i) sorts[i] = sort_bv;
  BzlaSortId sort_domain = bzla_sort_tuple(d_bzla, sorts, arity);
  BzlaSortId sort_fun    = bzla_sort_fun(d_bzla, sort_domain, sort_bv1);
  std::stringstream ss;
  ss << (bzla_node_is_fp_min(node) ? "_fp_min_uf_" : "_fp_max_uf_")
     << bzla_node_get_id(node) << "_";
  d_min_max_uf_map.emplace(bzla_sort_copy(d_bzla, sort_fp),
                           bzla_exp_uf(d_bzla, sort_fun, ss.str().c_str()));
  bzla_sort_release(d_bzla, sort_fun);
  bzla_sort_release(d_bzla, sort_domain);
  bzla_sort_release(d_bzla, sort_bv);
  bzla_sort_release(d_bzla, sort_bv1);
  return d_min_max_uf_map.at(sort_fp);
}

BzlaNode *
BzlaFPWordBlaster::sbv_ubv_uf(BzlaNode *node)
{
  assert(bzla_node_is_regular(node));
  assert(bzla_node_is_rm(d_bzla, node->e[0]));
  assert(bzla_node_is_fp(d_bzla, node->e[1]));

  BzlaSortId sort_bv = bzla_node_get_sort_id(node);
  BzlaSortId sort_fp = bzla_node_get_sort_id(node->e[1]);
  std::pair<BzlaSortId, BzlaSortId> p(sort_fp, sort_bv);

  if (d_sbv_ubv_uf_map.find(p) != d_sbv_ubv_uf_map.end())
    return d_sbv_ubv_uf_map.at(p);

  BzlaSortId sorts[2]    = {bzla_node_get_sort_id(node->e[0]), sort_fp};
  BzlaSortId sort_domain = bzla_sort_tuple(d_bzla, sorts, 2);
  BzlaSortId sort_fun    = bzla_sort_fun(d_bzla, sort_domain, sort_bv);

  std::stringstream ss;
  ss << (bzla_node_is_fp_to_sbv(node) ? "_fp_sbv_uf_" : "_fp_ubv_uf_")
     << bzla_node_get_id(node) << "_";
  (void) bzla_sort_copy(d_bzla, sort_fp);
  (void) bzla_sort_copy(d_bzla, sort_bv);
  d_sbv_ubv_uf_map.emplace(p, bzla_exp_uf(d_bzla, sort_fun, ss.str().c_str()));
  bzla_sort_release(d_bzla, sort_fun);
  bzla_sort_release(d_bzla, sort_domain);
  return d_sbv_ubv_uf_map.at(p);
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
#ifdef BZLA_USE_SYMFPU
  delete fp->fp;
#endif
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
  res = bzla_fp_new(bzla, sort);
#ifdef BZLA_USE_SYMFPU
  res->fp = new BzlaUnpackedFloat(*fp->fp);
#endif
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

uint32_t
bzla_fp_get_bv_width(const BzlaFloatingPoint *fp)
{
  return fp->size->exponentWidth() + fp->size->significandWidth();
}

void
bzla_fp_as_bv(Bzla *bzla,
              BzlaFloatingPoint *fp,
              BzlaBitVector **sign,
              BzlaBitVector **exp,
              BzlaBitVector **sig)
{
  assert(bzla);
  assert(fp);
  assert(sign);
  assert(exp);
  assert(sig);

  BzlaFPWordBlaster::set_s_bzla(bzla);
#ifdef BZLA_USE_SYMFPU
  uint32_t bw     = bzla_fp_get_bv_width(fp);
  uint32_t bw_exp = bzla_fp_get_exp_width(fp);
  uint32_t bw_sig = bzla_fp_get_sig_width(fp);
  BzlaBitVector *bv =
      bzla_bv_copy(bzla->mm, symfpu::pack(*fp->size, *fp->fp).getBv());
  *sign = bzla_bv_slice(bzla->mm, bv, bw - 1, bw - 1);
  *exp  = bzla_bv_slice(bzla->mm, bv, bw - 2, bw - 1 - bw_exp);
  *sig  = bzla_bv_slice(bzla->mm, bv, bw_sig - 2, 0);
  bzla_bv_free(bzla->mm, bv);
#endif
  BzlaFPWordBlaster::unset_s_bzla();
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
#ifdef BZLA_USE_SYMFPU
  BzlaFloatingPoint *fp = bzla_fp_get_fp(node);
  BzlaUnpackedFloat *uf = fp->fp;
  BzlaBitVector *bv_exp = uf->getExponent().getBv();
  BzlaBitVector *bv_sig = uf->getSignificand().getBv();
  return sizeof(BzlaFloatingPoint) + bzla_bv_size(bv_exp)
         + bzla_bv_size(bv_sig);
#else
  return 0;
#endif
}

#ifdef BZLA_USE_SYMFPU
static uint32_t hash_primes[] = {
    333444569u, 111130391u, 22237357u, 33355519u, 456790003u, 76891121u};
#endif

uint32_t
bzla_fp_hash(const BzlaFloatingPoint *fp)
{
  assert(fp);
  uint32_t hash = 0;

#ifdef BZLA_USE_SYMFPU
  BzlaUnpackedFloat *uf = fp->fp;

  hash += uf->getNaN() * hash_primes[0];
  hash += uf->getInf() * hash_primes[1];
  hash += uf->getZero() * hash_primes[2];
  hash += uf->getSign() * hash_primes[3];
  hash += bzla_bv_hash(uf->getExponent().getBv()) * hash_primes[4];
  hash += bzla_bv_hash(uf->getSignificand().getBv()) * hash_primes[5];
#endif
  return hash;
}

int32_t
bzla_fp_compare(const BzlaFloatingPoint *a, const BzlaFloatingPoint *b)
{
  assert(a);
  assert(b);

#ifdef BZLA_USE_SYMFPU
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
#endif
  return -1;
}

bool
bzla_fp_is_zero(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isZero(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_normal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isNormal(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_subnormal(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isSubnormal(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_nan(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isNaN(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_inf(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isNaN(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isNegative(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_is_pos(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(fp);
  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::isPositive(*fp->size, *fp->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_eq(Bzla *bzla,
           const BzlaFloatingPoint *fp0,
           const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::smtlibEqual<BzlaFPTraits>(*fp0->size, *fp0->fp, *fp1->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_lt(Bzla *bzla,
           const BzlaFloatingPoint *fp0,
           const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::lessThan<BzlaFPTraits>(*fp0->size, *fp0->fp, *fp1->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

bool
bzla_fp_lte(Bzla *bzla,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  bool res = false;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = symfpu::lessThanOrEqual<BzlaFPTraits>(*fp0->size, *fp0->fp, *fp1->fp);
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_zero(Bzla *bzla, BzlaSortId sort, bool sign)
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
  (void) bzla;
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_inf(Bzla *bzla, BzlaSortId sort, bool sign)
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
  (void) bzla;
  (void) sort;
  (void) sign;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_nan(Bzla *bzla, BzlaSortId sort)
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
  (void) bzla;
  (void) sort;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_from_bv(Bzla *bzla, BzlaSortId sort, BzlaBitVector *bv_const)
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
  (void) bzla;
  (void) sort;
  (void) bv_const;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_abs(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp->size->exponentWidth(),
                                        fp->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::absolute<BzlaFPTraits>(*res->size, *fp->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_neg(Bzla *bzla, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp->size->exponentWidth(),
                                        fp->size->significandWidth());
  res->fp =
      new BzlaUnpackedFloat(symfpu::negate<BzlaFPTraits>(*res->size, *fp->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_sqrt(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp->size->exponentWidth(),
                                        fp->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::sqrt<BzlaFPTraits>(*res->size, rm, *fp->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_rti(Bzla *bzla, const BzlaRoundingMode rm, const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(fp);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp->size->exponentWidth(),
                                        fp->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::roundToIntegral<BzlaFPTraits>(*res->size, rm, *fp->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_rem(Bzla *bzla,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp0->size->exponentWidth(),
                                        fp0->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::remainder<BzlaFPTraits>(*res->size, *fp0->fp, *fp1->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_add(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp0->size->exponentWidth(),
                                        fp0->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::add<BzlaFPTraits>(*res->size, rm, *fp0->fp, *fp1->fp, true));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp0;
  (void) fp1;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_mul(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp0->size->exponentWidth(),
                                        fp0->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::multiply<BzlaFPTraits>(*res->size, rm, *fp0->fp, *fp1->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp0;
  (void) fp1;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_div(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp0->size->exponentWidth(),
                                        fp0->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::divide<BzlaFPTraits>(*res->size, rm, *fp0->fp, *fp1->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp0;
  (void) fp1;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_fma(Bzla *bzla,
            const BzlaRoundingMode rm,
            const BzlaFloatingPoint *fp0,
            const BzlaFloatingPoint *fp1,
            const BzlaFloatingPoint *fp2)
{
  assert(bzla);
  assert(fp0);
  assert(fp1);
  assert(fp2);
  assert(fp0->size->exponentWidth() == fp1->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp1->size->significandWidth());
  assert(fp0->size->exponentWidth() == fp2->size->exponentWidth());
  assert(fp0->size->significandWidth() == fp2->size->significandWidth());

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  BZLA_CNEW(bzla->mm, res);
  res->size = new BzlaFloatingPointSize(fp0->size->exponentWidth(),
                                        fp0->size->significandWidth());
  res->fp   = new BzlaUnpackedFloat(
      symfpu::fma<BzlaFPTraits>(*res->size, rm, *fp0->fp, *fp1->fp, *fp2->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) fp0;
  (void) fp1;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert(Bzla *bzla,
                BzlaSortId sort,
                const BzlaRoundingMode rm,
                const BzlaFloatingPoint *fp)
{
  assert(bzla);
  assert(sort);
  assert(fp);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res     = bzla_fp_new(bzla, sort);
  res->fp = new BzlaUnpackedFloat(symfpu::convertFloatToFloat<BzlaFPTraits>(
      *fp->size, *res->size, rm, *fp->fp));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) rm;
  (void) bv;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_uint(Bzla *bzla,
                          BzlaSortId sort,
                          const BzlaRoundingMode rm,
                          const BzlaBitVector *bv)
{
  assert(bzla);
  assert(sort);
  assert(bv);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = bzla_fp_new(bzla, sort);
  /* Note: We must copy the bv here, because 1) the corresponding constructor
   *       doesn't copy it but sets d_bv = bv and 2) the wrong constructor is
   *       matched (const bool &val). */
  res->fp = new BzlaUnpackedFloat(symfpu::convertUBVToFloat<BzlaFPTraits>(
      *res->size, rm, bzla_bv_copy(bzla->mm, bv)));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) rm;
  (void) bv;
  res = nullptr;
#endif
  return res;
}

BzlaFloatingPoint *
bzla_fp_convert_from_int(Bzla *bzla,
                         BzlaSortId sort,
                         const BzlaRoundingMode rm,
                         const BzlaBitVector *bv)
{
  assert(bzla);
  assert(sort);
  assert(bv);

  BzlaFloatingPoint *res;
#ifdef BZLA_USE_SYMFPU
  BzlaFPWordBlaster::set_s_bzla(bzla);
  res = bzla_fp_new(bzla, sort);
  /* Note: We must copy the bv here, because 1) the corresponding constructor
   *       doesn't copy it but sets d_bv = bv and 2) the wrong constructor is
   *       matched (const bool &val). */
  res->fp = new BzlaUnpackedFloat(symfpu::convertSBVToFloat<BzlaFPTraits>(
      *res->size, rm, bzla_bv_copy(bzla->mm, bv)));
  BzlaFPWordBlaster::unset_s_bzla();
#else
  (void) bzla;
  (void) rm;
  (void) bv;
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
