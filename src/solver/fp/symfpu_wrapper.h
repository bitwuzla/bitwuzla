#ifndef BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED
#define BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED

#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

extern "C" {
#include "bzlabvstruct.h"
#include "bzlacore.h"
#include "bzlaexp.h"
#include "bzlanode.h"
}

#include <cstdint>

#include "bitvector.h"
#include "symfpu/core/ite.h"
#include "symfpu/utils/numberOfRoundingModes.h"

namespace bzla {
namespace fp {

template <bool T>
class SymFpuSymBV;
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
/* Wrapper for BitVector.                                                     */
/* -------------------------------------------------------------------------- */

/**
 * The template parameter distinguishes signed and unsigned bit-vectors, a
 * distinction symfpu uses.
 */
template <bool is_signed>
class SymFpuBV
{
  friend SymFpuSymBV<true>;
  friend SymFpuSymBV<false>;
  friend WordBlaster;

 protected:
  using literalType = typename signedToLiteralType<is_signed>::literalType;

  friend SymFpuBV<!is_signed>; /* Allow conversion between the types. */
  friend ::symfpu::ite<bool, SymFpuBV<is_signed> >; /* For ite. */

 public:
  SymFpuBV(const uint32_t bw, const uint32_t val);
  SymFpuBV(const bool &val);
  SymFpuBV(const SymFpuBV<is_signed> &other);
  SymFpuBV(const SymFpuBV<!is_signed> &other);
  SymFpuBV(const BitVector &bv);
  ~SymFpuBV();

  uint32_t getWidth(void) const;
  BitVector *getBv(void) const { return d_bv.get(); }

  static SymFpuBV<is_signed> one(const uint32_t &bw);
  static SymFpuBV<is_signed> zero(const uint32_t &bw);
  static SymFpuBV<is_signed> allOnes(const uint32_t &bw);

  bool isAllOnes() const;
  bool isAllZeros() const;

  static SymFpuBV<is_signed> maxValue(const uint32_t &bw);
  static SymFpuBV<is_signed> minValue(const uint32_t &bw);

  SymFpuBV<is_signed> operator=(const SymFpuBV<is_signed> &other);

  /*** Operators ***/
  SymFpuBV<is_signed> operator<<(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator>>(const SymFpuBV<is_signed> &op) const;

  SymFpuBV<is_signed> operator|(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator&(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator+(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator-(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator*(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator/(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator%(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> operator-(void) const;
  SymFpuBV<is_signed> operator~(void) const;

  SymFpuBV<is_signed> increment() const;
  SymFpuBV<is_signed> decrement() const;
  SymFpuBV<is_signed> signExtendRightShift(const SymFpuBV<is_signed> &op) const;

  /*** Modular operations ***/
  // No overflow checking so these are the same as other operations
  SymFpuBV<is_signed> modularLeftShift(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> modularRightShift(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> modularIncrement() const;
  SymFpuBV<is_signed> modularDecrement() const;
  SymFpuBV<is_signed> modularAdd(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> modularNegate() const;

  /*** Comparisons ***/
  bool operator==(const SymFpuBV<is_signed> &op) const;
  bool operator<=(const SymFpuBV<is_signed> &op) const;
  bool operator>=(const SymFpuBV<is_signed> &op) const;
  bool operator<(const SymFpuBV<is_signed> &op) const;
  bool operator>(const SymFpuBV<is_signed> &op) const;

  /*** Type conversion ***/
  SymFpuBV<true> toSigned(void) const;
  SymFpuBV<false> toUnsigned(void) const;

  /*** Bit hacks ***/
  SymFpuBV<is_signed> extend(uint32_t extension) const;
  SymFpuBV<is_signed> contract(uint32_t reduction) const;
  SymFpuBV<is_signed> resize(uint32_t newSize) const;
  SymFpuBV<is_signed> matchWidth(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> append(const SymFpuBV<is_signed> &op) const;
  SymFpuBV<is_signed> extract(uint32_t upper, uint32_t lower) const;

 private:
  std::unique_ptr<BitVector> d_bv;
};

/* --- SymFpuBV public ------------------------------------------------------ */

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const uint32_t bw, const uint32_t val)
{
  assert(bw);
  d_bv.reset(new BitVector(bw, val));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const bool &val)
{
  d_bv.reset(new BitVector(val ? BitVector::mk_true() : BitVector::mk_false()));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const SymFpuBV<is_signed> &other)
{
  assert(other.d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const SymFpuBV<!is_signed> &other)
{
  assert(other.d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::SymFpuBV(const BitVector &bv)
{
  assert(!bv.is_null());
  d_bv.reset(new BitVector(bv));
}

template <bool is_signed>
SymFpuBV<is_signed>::~SymFpuBV()
{
}

template <bool is_signed>
uint32_t
SymFpuBV<is_signed>::getWidth(void) const
{
  assert(d_bv);
  return d_bv->size();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::one(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_one(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::zero(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_zero(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::allOnes(const uint32_t &bw)
{
  assert(bw);
  return BitVector::mk_ones(bw);
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::isAllOnes() const
{
  assert(d_bv);
  return d_bv->is_ones();
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::isAllZeros() const
{
  assert(d_bv);
  return d_bv->is_zero();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::maxValue(const uint32_t &bw)
{
  assert(bw);
  return is_signed ? BitVector::mk_max_signed(bw) : BitVector::mk_ones(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::minValue(const uint32_t &bw)
{
  assert(bw);
  return is_signed ? BitVector::mk_min_signed(bw) : BitVector::mk_zero(bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator=(const SymFpuBV<is_signed> &other)
{
  assert(d_bv);
  d_bv.reset(new BitVector(*other.d_bv));
  return *this;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator<<(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvshl(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator>>(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvashr(*op.d_bv) : d_bv->bvshr(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator|(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvor(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator&(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvand(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator+(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvadd(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator-(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvsub(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator*(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvmul(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator/(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvsdiv(*op.d_bv) : d_bv->bvudiv(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator%(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->bvsrem(*op.d_bv) : d_bv->bvurem(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator-(void) const
{
  assert(d_bv);
  return d_bv->bvneg();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::operator~(void) const
{
  assert(d_bv);
  return d_bv->bvnot();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::increment() const
{
  assert(d_bv);
  return d_bv->bvinc();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::decrement() const
{
  assert(d_bv);
  return d_bv->bvdec();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::signExtendRightShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  uint32_t bw   = d_bv->size();
  uint32_t bwop = op.d_bv->size();
  assert(bwop <= bw);
  return d_bv->bvashr(op.d_bv->bvsext(bw - bwop));
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularLeftShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this << op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularRightShift(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this >> op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularIncrement() const
{
  assert(d_bv);
  return increment();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularDecrement() const
{
  assert(d_bv);
  return decrement();
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularAdd(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return *this + op;
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::modularNegate() const
{
  assert(d_bv);
  return -(*this);
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator==(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bveq(*op.d_bv).is_true();
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator<=(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) <= 0
                   : d_bv->compare(*op.d_bv) <= 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator>=(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) >= 0
                   : d_bv->compare(*op.d_bv) >= 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator<(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) < 0
                   : d_bv->compare(*op.d_bv) < 0;
}

template <bool is_signed>
bool
SymFpuBV<is_signed>::operator>(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return is_signed ? d_bv->signed_compare(*op.d_bv) > 0
                   : d_bv->compare(*op.d_bv) > 0;
}

template <bool is_signed>
SymFpuBV<true>
SymFpuBV<is_signed>::toSigned(void) const
{
  assert(d_bv);
  return SymFpuBV<true>(*this);
}

template <bool is_signed>
SymFpuBV<false>
SymFpuBV<is_signed>::toUnsigned(void) const
{
  assert(d_bv);
  return SymFpuBV<false>(*this);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::extend(uint32_t extension) const
{
  assert(d_bv);
  return is_signed ? d_bv->bvsext(extension) : d_bv->bvzext(extension);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::contract(uint32_t reduction) const
{
  assert(d_bv);
  uint32_t bw = getWidth();
  assert(bw - 1 - reduction < bw);
  return d_bv->bvextract(bw - 1 - reduction, 0);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::resize(uint32_t newSize) const
{
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
SymFpuBV<is_signed>
SymFpuBV<is_signed>::matchWidth(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  uint32_t bw = getWidth();
  assert(bw <= op.getWidth());
  return extend(op.getWidth() - bw);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::append(const SymFpuBV<is_signed> &op) const
{
  assert(d_bv);
  assert(op.d_bv);
  return d_bv->bvconcat(*op.d_bv);
}

template <bool is_signed>
SymFpuBV<is_signed>
SymFpuBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(d_bv);
  assert(upper >= lower);
  return d_bv->bvextract(upper, lower);
}

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class SymFpuTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = RoundingMode;
  using fpt  = FloatingPointSortInfo;
  using prop = bool;
  using sbv  = SymFpuBV<true>;
  using ubv  = SymFpuBV<false>;

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

class SymFpuSymRM;
class SymFpuSymProp;
template <bool T>
class SymFpuSymBV;

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

class SymFpuSymProp
{
  friend WordBlaster;
  friend SymFpuSymBV<true>;
  friend SymFpuSymBV<false>;
  friend ::symfpu::ite<SymFpuSymProp, SymFpuSymProp>;

 public:
  SymFpuSymProp(BzlaNode *node);
  SymFpuSymProp(bool v);
  SymFpuSymProp(const SymFpuSymProp &other);
  ~SymFpuSymProp();

  BzlaNode *getNode() const { return d_node; }

  SymFpuSymProp &operator=(const SymFpuSymProp &other);

  SymFpuSymProp operator!(void) const;
  SymFpuSymProp operator&&(const SymFpuSymProp &op) const;
  SymFpuSymProp operator||(const SymFpuSymProp &op) const;
  SymFpuSymProp operator==(const SymFpuSymProp &op) const;
  SymFpuSymProp operator^(const SymFpuSymProp &op) const;

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
class SymFpuSymBV;

template <bool is_signed>
class SymFpuSymBV
{
  friend WordBlaster;
  friend SymFpuSymBV<!is_signed>; /* Allow conversion between the sorts. */
  friend ::symfpu::ite<SymFpuSymProp, SymFpuSymBV<is_signed> >;

 public:
  /** Constructors for bit-vector nodes. */
  SymFpuSymBV(BzlaNode *node);
  SymFpuSymBV(const uint32_t w, const uint32_t val);
  SymFpuSymBV(const SymFpuSymProp &p);
  SymFpuSymBV(const SymFpuSymBV<is_signed> &other);
  SymFpuSymBV(const SymFpuSymBV<!is_signed> &other);
  SymFpuSymBV(const BitVector &bv);
  SymFpuSymBV(const SymFpuBV<is_signed> &bv);
  /** Constructors for Boolean nodes. */
  SymFpuSymBV(bool v);
  /** Destructor. */
  ~SymFpuSymBV();

  SymFpuSymBV<is_signed> &operator=(const SymFpuSymBV<is_signed> &other);

  uint32_t getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }

  /** Constant creation and test */
  static SymFpuSymBV<is_signed> one(const uint32_t &w);
  static SymFpuSymBV<is_signed> zero(const uint32_t &w);
  static SymFpuSymBV<is_signed> allOnes(const uint32_t &w);

  SymFpuSymProp isAllOnes() const;
  SymFpuSymProp isAllZeros() const;

  static SymFpuSymBV<is_signed> maxValue(const uint32_t &w);
  static SymFpuSymBV<is_signed> minValue(const uint32_t &w);

  /** Operators */
  SymFpuSymBV<is_signed> operator<<(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator>>(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator|(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator&(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator+(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator-(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator*(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator/(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator%(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> operator-(void) const;
  SymFpuSymBV<is_signed> operator~(void) const;
  SymFpuSymBV<is_signed> increment() const;
  SymFpuSymBV<is_signed> decrement() const;
  SymFpuSymBV<is_signed> signExtendRightShift(
      const SymFpuSymBV<is_signed> &op) const;

  /** Modular operations */
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  SymFpuSymBV<is_signed> modularLeftShift(
      const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> modularRightShift(
      const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> modularIncrement() const;
  SymFpuSymBV<is_signed> modularDecrement() const;
  SymFpuSymBV<is_signed> modularAdd(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> modularNegate() const;

  /** Operators for Boolean nodes */
  SymFpuSymProp operator!(void) const;
  SymFpuSymProp operator&&(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator||(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator^(const SymFpuSymBV<is_signed> &op) const;

  /** Comparisons */
  SymFpuSymProp operator==(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator<=(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator>=(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator<(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymProp operator>(const SymFpuSymBV<is_signed> &op) const;

  /** Type conversion */
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  SymFpuSymBV<true> toSigned(void) const;
  SymFpuSymBV<false> toUnsigned(void) const;

  /** Bit hacks */
  SymFpuSymBV<is_signed> extend(uint32_t extension) const;
  SymFpuSymBV<is_signed> contract(uint32_t reduction) const;
  SymFpuSymBV<is_signed> resize(uint32_t newSize) const;
  SymFpuSymBV<is_signed> matchWidth(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> append(const SymFpuSymBV<is_signed> &op) const;
  SymFpuSymBV<is_signed> extract(uint32_t upper, uint32_t lower) const;

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

/* --- SymFpuSymBV public --------------------------------------------------- */

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(BzlaNode *node)
{
  assert(s_bzla);
  assert(check_node(node));
  d_node = bzla_node_copy(s_bzla, node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const uint32_t w, const uint32_t val)
{
  assert(s_bzla);
  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  d_node       = is_signed ? bzla_exp_bv_int(s_bzla, val, s)
                           : bzla_exp_bv_unsigned(s_bzla, val, s);
  bzla_sort_release(s_bzla, s);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymProp &p)
{
  assert(s_bzla);
  assert(p.d_node);
  assert(bzla_sort_bv_get_width(s_bzla, bzla_node_get_sort_id(p.d_node)));
  d_node = bzla_node_copy(s_bzla, p.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuSymBV<!is_signed> &other)
{
  assert(s_bzla);
  assert(other.d_node);
  assert(check_node(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const BitVector &bv)
{
  assert(s_bzla);
  BzlaBitVector *bbv = bzla_bv_new(s_bzla->mm, bv.size());
  bbv->d_bv.reset(new bzla::BitVector(bv));
  d_node = bzla_exp_bv_const(s_bzla, bbv);
  bzla_bv_free(s_bzla->mm, bbv);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::SymFpuSymBV(const SymFpuBV<is_signed> &bv)
{
  assert(s_bzla);
  assert(bv.d_bv);
  BzlaBitVector *bbv = bzla_bv_new(s_bzla->mm, bv.d_bv->size());
  bbv->d_bv.reset(new bzla::BitVector(*bv.d_bv));
  d_node = bzla_exp_bv_const(s_bzla, bbv);
  bzla_bv_free(s_bzla->mm, bbv);
}

template <bool is_signed>
SymFpuSymBV<is_signed>::~SymFpuSymBV()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed> &
SymFpuSymBV<is_signed>::operator=(const SymFpuSymBV<is_signed> &other)
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
SymFpuSymBV<is_signed>::getWidth(void) const
{
  assert(s_bzla);
  return bzla_node_bv_get_width(s_bzla, d_node);
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::one(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_one(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::zero(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_zero(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::allOnes(const uint32_t &w)
{
  assert(s_bzla);
  BzlaSortId s               = bzla_sort_bv(s_bzla, w);
  BzlaNode *n                = bzla_exp_bv_ones(s_bzla, s);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::isAllOnes() const
{
  return *this == SymFpuSymBV<is_signed>::allOnes(getWidth());
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::isAllZeros() const
{
  return *this == SymFpuSymBV<is_signed>::zero(getWidth());
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::maxValue(const uint32_t &w)
{
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_max_signed(s_bzla, s)
                           : bzla_exp_bv_ones(s_bzla, s);

  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::minValue(const uint32_t &w)
{
  assert(s_bzla);

  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  BzlaNode *n  = is_signed ? bzla_exp_bv_min_signed(s_bzla, s)
                           : bzla_exp_bv_zero(s_bzla, s);

  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);

  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator<<(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sll(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator>>(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sra(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_srl(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator|(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator&(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator+(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_add(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sub(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator*(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_mul(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator/(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sdiv(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_udiv(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator%(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_srem(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_urem(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator-(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_neg(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::operator~(void) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_not(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::increment() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_inc(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::decrement() const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_dec(s_bzla, d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::signExtendRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_sra(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularLeftShift(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this << op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularRightShift(
    const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this >> op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularIncrement() const
{
  assert(s_bzla);
  return increment();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  return decrement();
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularAdd(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this + op;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::modularNegate() const
{
  assert(s_bzla);
  return -(*this);
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_bv_not(s_bzla, d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator||(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(checkBooleanNode(op.d_node));
  BzlaNode *n       = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator^(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  assert(check_node(op.d_node));
  BzlaNode *n       = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator==(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = bzla_exp_eq(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<=(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_slte(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ulte(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>=(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgte(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ugte(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator<(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_slt(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ult(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymProp
SymFpuSymBV<is_signed>::operator>(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n       = is_signed ? bzla_exp_bv_sgt(s_bzla, d_node, op.d_node)
                                : bzla_exp_bv_ugt(s_bzla, d_node, op.d_node);
  SymFpuSymProp res = SymFpuSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<true>
SymFpuSymBV<is_signed>::toSigned(void) const
{
  return SymFpuSymBV<true>(*this);
}

template <bool is_signed>
SymFpuSymBV<false>
SymFpuSymBV<is_signed>::toUnsigned(void) const
{
  return SymFpuSymBV<false>(*this);
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::extend(uint32_t extension) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sext(s_bzla, d_node, extension)
                          : bzla_exp_bv_uext(s_bzla, d_node, extension);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::contract(uint32_t reduction) const
{
  assert(s_bzla);
  assert(getWidth() > reduction);
  BzlaNode *n =
      bzla_exp_bv_slice(s_bzla, d_node, getWidth() - 1 - reduction, 0);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::resize(uint32_t newSize) const
{
  uint32_t bw = getWidth();
  if (newSize > bw) return extend(newSize - bw);
  if (newSize < bw) return contract(bw - newSize);
  return *this;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::matchWidth(const SymFpuSymBV<is_signed> &op) const
{
  assert(getWidth() <= op.getWidth());
  return extend(op.getWidth() - getWidth());
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::append(const SymFpuSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n                = bzla_exp_bv_concat(s_bzla, d_node, op.d_node);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
SymFpuSymBV<is_signed>
SymFpuSymBV<is_signed>::extract(uint32_t upper, uint32_t lower) const
{
  assert(s_bzla);
  assert(upper >= lower);
  BzlaNode *n                = bzla_exp_bv_slice(s_bzla, d_node, upper, lower);
  SymFpuSymBV<is_signed> res = SymFpuSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::check_node(const BzlaNode *node) const
{
  assert(s_bzla == bzla_node_real_addr(node)->bzla);
  return bzla_sort_is_bv(s_bzla, bzla_node_get_sort_id(node));
}

template <bool is_signed>
bool
SymFpuSymBV<is_signed>::checkBooleanNode(const BzlaNode *node) const
{
  assert(check_node(node));
  return bzla_node_bv_get_width(s_bzla, node) == 1;
}

/* -------------------------------------------------------------------------- */
/* Bitwuzla wrapper for rounding modes.                                      */
/* -------------------------------------------------------------------------- */

class SymFpuSymRM
{
  friend WordBlaster;
  friend symfpu::ite<SymFpuSymProp, SymFpuSymRM>;

 public:
  /* Constructors. */
  SymFpuSymRM(BzlaNode *node);
  SymFpuSymRM(const uint32_t val);
  SymFpuSymRM(const SymFpuSymRM &other);
  /* Destructor. */
  ~SymFpuSymRM();

  BzlaNode *getNode() const { return d_node; }

  SymFpuSymProp valid(void) const;
  SymFpuSymProp operator==(const SymFpuSymRM &other) const;

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

class SymFpuSymTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = SymFpuSymRM;
  using fpt  = bzla::fp::FloatingPointSortInfo;
  using prop = SymFpuSymProp;
  using sbv  = SymFpuSymBV<true>;
  using ubv  = SymFpuSymBV<false>;

  /* Give concrete instances (wrapped nodes) for each rounding mode. */
  static SymFpuSymRM RNE(void);
  static SymFpuSymRM RNA(void);
  static SymFpuSymRM RTP(void);
  static SymFpuSymRM RTN(void);
  static SymFpuSymRM RTZ(void);

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
BZLA_FP_ITE(bzla::fp::SymFpuTraits::rm);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::prop);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::sbv);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::ubv);
#undef BZLA_FP_ITE

#define BZLA_FP_SYM_ITE(T)                                  \
  template <>                                               \
  struct ite<bzla::fp::SymFpuSymProp, T>                    \
  {                                                         \
    static const T iteOp(const bzla::fp::SymFpuSymProp &_c, \
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
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::rm);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::prop);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::sbv);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::ubv);
#undef BZLA_FP_SYM_ITE

}  // namespace symfpu

/* -------------------------------------------------------------------------- */
#endif
