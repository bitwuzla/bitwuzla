/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

#include <unordered_map>

extern "C" {
#include "bzlaabort.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlafp.h"
#include "bzlanode.h"
}

#ifdef BZLA_USE_SYMFPU
#include "symfpu/core/unpackedFloat.h"
#endif

#define BZLA_FP_RM_BW 3

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
  BzlaFPBV(const BzlaBitVector *bv);
  ~BzlaFPBV();

  uint32_t getWidth(void) const;

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
BzlaFPBV<is_signed>::BzlaFPBV(const BzlaBitVector *bv)
{
  assert(s_bzla);
  assert(bv);
  d_bv = bzla_bv_copy(s_bzla->mm, bv);
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
  return bzla_bv_eq(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator<=(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_slte(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_ulte(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>=(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_sgte(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_ugte(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator<(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_slt(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_ult(s_bzla->mm, d_bv, op.d_bv);
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_sgt(s_bzla->mm, d_bv, op.d_bv)
                   : bzla_bv_ugt(s_bzla->mm, d_bv, op.d_bv);
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
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::contract(uint32_t reduction) const
{
  assert(s_bzla);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::resize(uint32_t newSize) const
{
  assert(s_bzla);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::matchWidth(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::append(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(s_bzla);
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

/* ========================================================================== */
/* Floating-Point constants.                                                  */
/* ========================================================================== */

struct BzlaFloatingPointSize
{
  uint32_t ewidth; /* size of exponent */
  uint32_t swidth; /* size of significand */
};

struct BzlaFloatingPoint
{
  BzlaFloatingPointSize size;
#ifdef BZLA_USE_SYMFPU
  ::symfpu::unpackedFloat<BzlaFPTraits> fp;
#endif
};

/* ========================================================================== */
/* Glue for SymFPU: symbolic.                                                 */
/* ========================================================================== */

class BzlaFPWordBlaster;
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

class BzlaFPSortInfo
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
{
  assert(s_bzla);
  assert(bzla_sort_is_fp(s_bzla, sort));
  d_sort = bzla_sort_copy(s_bzla, sort);
}

BzlaFPSortInfo::BzlaFPSortInfo(uint32_t ewidth, uint32_t swidth)
{
  assert(s_bzla);
  d_sort = bzla_sort_fp(s_bzla, ewidth, swidth);
}

BzlaFPSortInfo::BzlaFPSortInfo(const BzlaFPSortInfo &other)
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
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

BzlaFPSymProp::~BzlaFPSymProp()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
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
  assert(checkNode(node));
  return bzla_sort_is_bv(node->bzla, bzla_node_get_sort_id(node))
         && bzla_node_bv_get_width(s_bzla, node) == 1;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for bit-vector terms.                                    */
/* -------------------------------------------------------------------------- */

template <bool is_signed>
class BzlaFPSymBV
{
  friend BzlaFPWordBlaster;
  friend BzlaFPSymBV<!is_signed>; /* Allow conversion between the sorts. */
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaFPSymProp, BzlaFPSymBV<is_signed> >;
#endif

 public:
  BzlaFPSymBV(BzlaNode *node);
  BzlaFPSymBV(const uint32_t w, const uint32_t val);
  BzlaFPSymBV(const BzlaFPSymProp &p);
  BzlaFPSymBV(const BzlaFPSymBV<is_signed> &other);
  BzlaFPSymBV(const BzlaBitVector *bv);
  ~BzlaFPSymBV();

  uint32_t getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }

  /*** Constant creation and test ***/
  static BzlaFPSymBV<is_signed> one(const uint32_t &w);
  static BzlaFPSymBV<is_signed> zero(const uint32_t &w);
  static BzlaFPSymBV<is_signed> allOnes(const uint32_t &w);

  BzlaFPSymProp isAllOnes() const;
  BzlaFPSymProp isAllZeros() const;

  static BzlaFPSymBV<is_signed> maxValue(const uint32_t &w);
  static BzlaFPSymBV<is_signed> minValue(const uint32_t &w);

  /*** Operators ***/
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

  /*** Modular operations ***/
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

  /*** Comparisons ***/
  BzlaFPSymProp operator==(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator<=(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator>=(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator<(const BzlaFPSymBV<is_signed> &op) const;
  BzlaFPSymProp operator>(const BzlaFPSymBV<is_signed> &op) const;

  /*** Type conversion ***/
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  BzlaFPSymBV<true> toSigned(void) const;
  BzlaFPSymBV<false> toUnsigned(void) const;

  /*** Bit hacks ***/
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
      bzla_exp_bv_slice(s_bzla, d_node, this->getWidth - 1 - reduction, 0);
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
  return bzla_sort_is_bv(node->bzla, bzla_node_get_sort_id(node));
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
  BzlaFPSymRM(BzlaNode *node);
  BzlaFPSymRM(const uint32_t val);
  BzlaFPSymRM(const BzlaFPSymRM &other);

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
  assert(val < BZLA_RM_MAX);
  d_node = bzla_exp_fp_rm(s_bzla, static_cast<BzlaRoundingMode>(val));
  assert(checkNode(d_node));
}

BzlaFPSymRM::BzlaFPSymRM(const BzlaFPSymRM &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

BzlaFPSymProp
BzlaFPSymRM::valid(void) const
{
  assert(d_node);
  BzlaNode *max;
  max =
      bzla_exp_bv_unsigned(s_bzla, BZLA_RM_MAX, bzla_node_get_sort_id(d_node));
  bzla_node_release(s_bzla, max);
  return bzla_exp_bv_ult(s_bzla, d_node, max);
}

BzlaFPSymProp
BzlaFPSymRM::operator==(const BzlaFPSymRM &other) const
{
  assert(d_node);
  assert(other.d_node);
  return bzla_exp_eq(s_bzla, d_node, other.d_node);
}

bool
BzlaFPSymRM::checkNode(const BzlaNode *node) const
{
  assert(s_bzla);
  assert(node);

  BzlaSortId sort = bzla_node_get_sort_id(node);
  if (!bzla_sort_is_bv(s_bzla, sort))
  {
    return false;
  }
#ifdef BZLA_USE_SYMFPU
  assert((((uint32_t) 1u) << BZLA_FP_RM_BW) >= SYMFPU_NUMBER_OF_ROUNDING_MODES);
  return bzla_sort_bv_get_width(s_bzla, sort) == BZLA_FP_RM_BW;
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
  BzlaFPWordBlaster(Bzla *bzla) : d_bzla(bzla)
  {
    BzlaFPSortInfo::s_bzla     = bzla;
    BzlaFPSymRM::s_bzla        = bzla;
    BzlaFPSymProp::s_bzla      = bzla;
    BzlaFPSymBV<true>::s_bzla  = bzla;
    BzlaFPSymBV<false>::s_bzla = bzla;
  }

  void word_blast();

  BzlaFPWordBlaster *clone()
  {
    // TODO
    return nullptr;
  }

 private:
  using BzlaFPSortInfoMap =
      std::unordered_map<BzlaSortId, BzlaFPSortInfo, BzlaSortHashFunction>;
  using BzlaFPSymRMMap =
      std::unordered_map<BzlaNode *, BzlaFPSymRM, BzlaNodeHashFunction>;
  using BzlaFPSymPropMap =
      std::unordered_map<BzlaNode *, BzlaFPSymProp, BzlaNodeHashFunction>;
  using BzlaFPSymUBVMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<false>, BzlaNodeHashFunction>;
  using BzlaFPSymSBVMap =
      std::unordered_map<BzlaNode *, BzlaFPSymBV<true>, BzlaNodeHashFunction>;

  BzlaFPSortInfoMap s_sort_map;
  BzlaFPSymRMMap d_rm_map;
  BzlaFPSymPropMap d_prop_map;
  BzlaFPSymUBVMap d_ubv_map;
  BzlaFPSymSBVMap d_sbv_map;
  Bzla *d_bzla;
};

void *
bzla_fp_word_blaster_new(Bzla *bzla)
{
  return new BzlaFPWordBlaster(bzla);
}

void *
bzla_fp_word_blaster_clone(Bzla *bzla)
{
  return static_cast<BzlaFPWordBlaster *>(bzla->word_blaster)->clone();
}

void
bzla_fp_word_blaster_delete(void *wblaster)
{
  delete static_cast<BzlaFPWordBlaster *>(wblaster);
}
