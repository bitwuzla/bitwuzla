#ifndef BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED
#define BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED

#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

extern "C" {
#include "bzlabv.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
}

#include <cstdint>

#include "symfpu/core/ite.h"
#include "symfpu/utils/numberOfRoundingModes.h"

namespace bzla {
namespace fp {

template <bool T>
class BzlaFPSymBV;
class WordBlaster;

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
  friend WordBlaster;

 protected:
  using literalType = typename signedToLiteralType<is_signed>::literalType;

  friend BzlaFPBV<!is_signed>; /* Allow conversion between the types. */
  friend ::symfpu::ite<bool, BzlaFPBV<is_signed> >; /* For ite. */

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
  static inline Bzla *s_bzla = nullptr;
  BzlaBitVector *d_bv        = nullptr;
};

/* --- BzlaFPBV public ------------------------------------------------------ */

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
  bzla_bv_free(s_bzla->mm, d_bv);
  d_bv = bzla_bv_copy(s_bzla->mm, other.d_bv);
  return *this;
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
  uint32_t bw   = bzla_bv_get_width(d_bv);
  uint32_t bwop = bzla_bv_get_width(op.d_bv);
  assert(bwop <= bw);
  BzlaBitVector *res, *bvop = op.d_bv;
  bvop = bzla_bv_sext(s_bzla->mm, op.d_bv, bw - bwop);
  res  = bzla_bv_sra(s_bzla->mm, d_bv, bvop);
  bzla_bv_free(s_bzla->mm, bvop);
  return res;
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
  return increment();
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  assert(d_bv);
  return decrement();
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
  return is_signed ? bzla_bv_signed_compare(d_bv, op.d_bv) <= 0
                   : bzla_bv_compare(d_bv, op.d_bv) <= 0;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>=(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_signed_compare(d_bv, op.d_bv) >= 0
                   : bzla_bv_compare(d_bv, op.d_bv) >= 0;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator<(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_signed_compare(d_bv, op.d_bv) < 0
                   : bzla_bv_compare(d_bv, op.d_bv) < 0;
}

template <bool is_signed>
bool
BzlaFPBV<is_signed>::operator>(const BzlaFPBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? bzla_bv_signed_compare(d_bv, op.d_bv) > 0
                   : bzla_bv_compare(d_bv, op.d_bv) > 0;
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
  uint32_t bw = getWidth();
  assert(bw - 1 - reduction < bw);
  return bzla_bv_slice(s_bzla->mm, d_bv, bw - 1 - reduction, 0);
}

template <bool is_signed>
BzlaFPBV<is_signed>
BzlaFPBV<is_signed>::resize(uint32_t newSize) const
{
  assert(s_bzla);
  assert(d_bv);
  uint32_t bw = getWidth();
  if (newSize > bw)
  {
    return extend(newSize - bw);
  }
  if (newSize < bw)
  {
    return contract(bw - newSize);
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
  uint32_t bw = getWidth();
  assert(bw <= op.getWidth());
  return extend(op.getWidth() - bw);
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
  using rm   = RoundingMode;
  using fpt  = FloatingPointSortInfo;
  using prop = bool;
  using sbv  = BzlaFPBV<true>;
  using ubv  = BzlaFPBV<false>;

  /* Give concrete instances of each rounding mode, mainly for comparisons. */
  static RoundingMode RNE(void);
  static RoundingMode RNA(void);
  static RoundingMode RTP(void);
  static RoundingMode RTN(void);
  static RoundingMode RTZ(void);

  /* Properties used by Symfpu. */
  static void precondition(const bool &p);
  static void postcondition(const bool &p);
  static void invariant(const bool &p);
};

/* ========================================================================== */
/* Glue for SymFPU: symbolic.                                                 */
/* ========================================================================== */

class BzlaFPSymRM;
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
/* Bitwuzla wrapper for propositions.                                        */
/* -------------------------------------------------------------------------- */

class BzlaFPSymProp
{
  friend WordBlaster;
  friend BzlaFPSymBV<true>;
  friend BzlaFPSymBV<false>;
  friend ::symfpu::ite<BzlaFPSymProp, BzlaFPSymProp>;

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
  static inline Bzla *s_bzla = nullptr;
  BzlaNode *d_node;
};

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for bit-vector terms.                                    */
/* -------------------------------------------------------------------------- */

template <bool is_signed>
class BzlaFPSymBV;

template <bool is_signed>
class BzlaFPSymBV
{
  friend WordBlaster;
  friend BzlaFPSymBV<!is_signed>; /* Allow conversion between the sorts. */
  friend ::symfpu::ite<BzlaFPSymProp, BzlaFPSymBV<is_signed> >;

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
  static inline Bzla *s_bzla = nullptr;
  BzlaNode *d_node;
};

/* --- BzlaFPSymBV public --------------------------------------------------- */

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
  return *this == BzlaFPSymBV<is_signed>::allOnes(getWidth());
}

template <bool is_signed>
BzlaFPSymProp
BzlaFPSymBV<is_signed>::isAllZeros() const
{
  return *this == BzlaFPSymBV<is_signed>::zero(getWidth());
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
  return increment();
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  return decrement();
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
  BzlaNode *n       = is_signed ? bzla_exp_bv_slte(s_bzla, d_node, op.d_node)
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
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgte(s_bzla, d_node, op.d_node)
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
  BzlaNode *n       = is_signed ? bzla_exp_bv_slt(s_bzla, d_node, op.d_node)
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
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgt(s_bzla, d_node, op.d_node)
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
  assert(getWidth() > reduction);
  BzlaNode *n =
      bzla_exp_bv_slice(s_bzla, d_node, getWidth() - 1 - reduction, 0);
  BzlaFPSymBV<is_signed> res = BzlaFPSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::resize(uint32_t newSize) const
{
  uint32_t bw = getWidth();
  if (newSize > bw) return extend(newSize - bw);
  if (newSize < bw) return contract(bw - newSize);
  return *this;
}

template <bool is_signed>
BzlaFPSymBV<is_signed>
BzlaFPSymBV<is_signed>::matchWidth(const BzlaFPSymBV<is_signed> &op) const
{
  assert(getWidth() <= op.getWidth());
  return extend(op.getWidth() - getWidth());
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

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for rounding modes.                                      */
/* -------------------------------------------------------------------------- */

class BzlaFPSymRM
{
  friend WordBlaster;
  friend symfpu::ite<BzlaFPSymProp, BzlaFPSymRM>;

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
  static inline Bzla *s_bzla = nullptr;
  BzlaNode *init_const(const uint32_t val);
  BzlaNode *d_node;
};

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class BzlaFPSymTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = BzlaFPSymRM;
  using fpt  = bzla::fp::FloatingPointSortInfo;
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

}  // namespace fp
}  // namespace bzla

/* ========================================================================== */
/* ITE specializations.                                                       */
/* ========================================================================== */

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
BZLA_FP_ITE(bzla::fp::BzlaFPTraits::rm);
BZLA_FP_ITE(bzla::fp::BzlaFPTraits::prop);
BZLA_FP_ITE(bzla::fp::BzlaFPTraits::sbv);
BZLA_FP_ITE(bzla::fp::BzlaFPTraits::ubv);
#undef BZLA_FP_ITE

#define BZLA_FP_SYM_ITE(T)                                  \
  template <>                                               \
  struct ite<bzla::fp::BzlaFPSymProp, T>                    \
  {                                                         \
    static const T iteOp(const bzla::fp::BzlaFPSymProp &_c, \
                         const T &_t,                       \
                         const T &_e)                       \
    {                                                       \
      BzlaNode *c = _c.getNode();                           \
      BzlaNode *t = _t.getNode();                           \
      BzlaNode *e = _e.getNode();                           \
      assert(c);                                            \
      assert(t);                                            \
      assert(e);                                            \
      Bzla *bzla = T::s_bzla;                               \
      assert(bzla);                                         \
      assert(bzla == bzla_node_real_addr(c)->bzla);         \
      assert(bzla == bzla_node_real_addr(t)->bzla);         \
      assert(bzla == bzla_node_real_addr(e)->bzla);         \
      BzlaNode *ite = bzla_exp_cond(bzla, c, t, e);         \
      T res(ite);                                           \
      bzla_node_release(bzla, ite);                         \
      return res;                                           \
    }                                                       \
  };
BZLA_FP_SYM_ITE(bzla::fp::BzlaFPSymTraits::rm);
BZLA_FP_SYM_ITE(bzla::fp::BzlaFPSymTraits::prop);
BZLA_FP_SYM_ITE(bzla::fp::BzlaFPSymTraits::sbv);
BZLA_FP_SYM_ITE(bzla::fp::BzlaFPSymTraits::ubv);
#undef BZLA_FP_SYM_ITE

}  // namespace symfpu

/* -------------------------------------------------------------------------- */
#endif
