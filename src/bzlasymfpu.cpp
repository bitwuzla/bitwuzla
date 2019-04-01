/*  Boolector: Satisfiablity Modulo Theories (SMT) solver.
 *
 *  Copyright (C) 2019 Aina Niemetz.
 *
 *  This file is part of Boolector.
 *  See COPYING for more information on using this software.
 */

extern "C" {
#include "bzlaabort.h"
#include "bzlaexp.h"
#include "bzlanode.h"
}

#ifdef BZLA_USE_SYMFPU
#include "symfpu/core/unpackedFloat.h"
#endif

/* ========================================================================== */

class BzlaSymRM;
class BzlaFPSortInfo;
class BzlaSymProp;
template <bool T>
class BzlaSymBV;

/* Template parameter for SymFPU templates. --------------------------------- */
class BzlaSymTraits
{
 public:
  /* The six key types that SymFPU uses. */
  typedef unsigned bwt;
  typedef BzlaSymRM rm;
  typedef BzlaFPSortInfo fpt;
  typedef BzlaSymProp prop;
  typedef BzlaSymBV<true> sbv;
  typedef BzlaSymBV<false> ubv;

  /* Give concrete instances (wrapped nodes) for each rounding mode. */
  static BzlaSymRM RNE(void);
  static BzlaSymRM RNA(void);
  static BzlaSymRM RTP(void);
  static BzlaSymRM RTN(void);
  static BzlaSymRM RTZ(void);

  /* Properties used by Symfpu. */
  static void precondition(const bool b);
  static void postcondition(const bool b);
  static void invariant(const bool b);
  static void precondition(const prop &p);
  static void postcondition(const prop &p);
  static void invariant(const prop &p);
};

/* Use the same type names as SymFPU. */
typedef BzlaSymTraits::bwt bwt;

/* Mapping between sorts. */
template <bool T>
struct BzlaSignedToLitSort;
template <>
struct BzlaSignedToLitSort<true>
{
  typedef int32_t BzlaLitSort;
};
template <>
struct BzlaSignedToLitSort<false>
{
  typedef uint32_t BzlaLitSort;
};

/* Bitwuzla wrapper for rounding modes. ------------------------------------ */
class BzlaSymRM
{
#ifdef BZLA_USE_SYMFPU
  friend symfpu::ite<BzlaSymProp, BzlaSymRM>;
#endif

 public:
  BzlaSymRM(const BzlaNode *node);
  BzlaSymRM(const uint32_t val);
  BzlaSymRM(const BzlaSymRM &other);

  BzlaSymProp valid(void) const;
  BzlaSymProp operator==(const BzlaSymRM &rm) const;

 protected:
  bool checkNode(const BzlaNode *node);
};

/* Bitwuzla wrapper for floating-point sorts. ------------------------------ */
class BzlaFPSortInfo
{
 public:
  BzlaFPSortInfo(const BzlaSort sort);
  BzlaFPSortInfo(unsigned node, unsigned sig);
  BzlaFPSortInfo(const BzlaFPSortInfo &other);

  BzlaSort getSort(void) const;
};

/* Bitwuzla wrapper for propositions. -------------------------------------- */
class BzlaSymProp
{
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaSymProp, BzlaSymProp>;
#endif

 public:
  BzlaSymProp(BzlaNode *node);
  BzlaSymProp(bool v);
  BzlaSymProp(const BzlaSymProp &other);
  ~BzlaSymProp();

  static void setBtor(Bzla *bzla) { s_bzla = bzla; }

  BzlaSymProp operator!(void) const;
  BzlaSymProp operator&&(const BzlaSymProp &op) const;
  BzlaSymProp operator||(const BzlaSymProp &op) const;
  BzlaSymProp operator==(const BzlaSymProp &op) const;
  BzlaSymProp operator^(const BzlaSymProp &op) const;

 protected:
  bool checkNode(const BzlaNode *node);

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

Bzla *BzlaSymProp::s_bzla = nullptr;

/* Bitwuzla wrapper for bit-vector terms. ---------------------------------- */
template <bool is_signed>
class BzlaSymBV
{
  friend BzlaSymBV<!is_signed>; /* Allow conversion between the sorts. */
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaSymProp, BzlaSymBV<is_signed> >;
#endif

 public:
  BzlaSymBV(BzlaNode *node);
  BzlaSymBV(const bwt w, const uint32_t val);
  BzlaSymBV(const BzlaSymProp &p);
  BzlaSymBV(const BzlaSymBV<is_signed> &other);
  BzlaSymBV(const BzlaBitVector *bv);
  ~BzlaSymBV();

  bwt getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }
  static void setBtor(Bzla *bzla) { s_bzla = bzla; }

  /*** Constant creation and test ***/
  static BzlaSymBV<is_signed> one(const bwt &w);
  static BzlaSymBV<is_signed> zero(const bwt &w);
  static BzlaSymBV<is_signed> allOnes(const bwt &w);

  BzlaSymProp isAllOnes() const;
  BzlaSymProp isAllZeros() const;

  static BzlaSymBV<is_signed> maxValue(const bwt &w);
  static BzlaSymBV<is_signed> minValue(const bwt &w);

  /*** Operators ***/
  BzlaSymBV<is_signed> operator<<(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator>>(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator|(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator&(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator+(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator-(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator*(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator/(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator%(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> operator-(void) const;
  BzlaSymBV<is_signed> operator~(void) const;
  BzlaSymBV<is_signed> increment() const;
  BzlaSymBV<is_signed> decrement() const;
  BzlaSymBV<is_signed> signExtendRightShift(
      const BzlaSymBV<is_signed> &op) const;

  /*** Modular operations ***/
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  BzlaSymBV<is_signed> modularLeftShift(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> modularRightShift(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> modularIncrement() const;
  BzlaSymBV<is_signed> modularDecrement() const;
  BzlaSymBV<is_signed> modularAdd(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> modularNegate() const;

  /*** Comparisons ***/
  BzlaSymProp operator==(const BzlaSymBV<is_signed> &op) const;
  BzlaSymProp operator<=(const BzlaSymBV<is_signed> &op) const;
  BzlaSymProp operator>=(const BzlaSymBV<is_signed> &op) const;
  BzlaSymProp operator<(const BzlaSymBV<is_signed> &op) const;
  BzlaSymProp operator>(const BzlaSymBV<is_signed> &op) const;

  /*** Type conversion ***/
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  BzlaSymBV<true> toSigned(void) const;
  BzlaSymBV<false> toUnsigned(void) const;

  /*** Bit hacks ***/
  BzlaSymBV<is_signed> extend(bwt extension) const;
  BzlaSymBV<is_signed> contract(bwt reduction) const;
  BzlaSymBV<is_signed> resize(bwt newSize) const;
  BzlaSymBV<is_signed> matchWidth(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> append(const BzlaSymBV<is_signed> &op) const;
  BzlaSymBV<is_signed> extract(bwt upper, bwt lower) const;

 protected:
  typedef typename BzlaSignedToLitSort<is_signed>::BzlaLitSort literalType;

  // BzlaNode* boolNodeToBV(BzlaNode* node) const;
  // BzlaNode* BVToBoolNode(BzlaNode* node) const;

  bool checkNode(const BzlaNode *node);
  // BzlaNode *fromProposition (BzlaNode *node) const;
  // BzlaNode *toProposition (BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

BzlaSymProp::BzlaSymProp(BzlaNode *node)
{
  assert(s_bzla);
  assert(checkNode(node));
  d_node = bzla_node_copy(s_bzla, node);
}

BzlaSymProp::BzlaSymProp(bool v)
{
  assert(s_bzla);
  d_node = v ? bzla_exp_true(s_bzla) : bzla_exp_false(s_bzla);
}

BzlaSymProp::BzlaSymProp(const BzlaSymProp &other)
{
  assert(s_bzla);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

BzlaSymProp::~BzlaSymProp()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

BzlaSymProp
BzlaSymProp::operator!(void) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_bv_not(s_bzla, d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaSymProp
BzlaSymProp::operator&&(const BzlaSymProp &op) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaSymProp
BzlaSymProp::operator||(const BzlaSymProp &op) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaSymProp
BzlaSymProp::operator==(const BzlaSymProp &op) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_eq(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

BzlaSymProp
BzlaSymProp::operator^(const BzlaSymProp &op) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_bv_xor(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

bool
BzlaSymProp::checkNode(const BzlaNode *node)
{
  return bzla_sort_is_bv(node->bzla, bzla_node_get_sort_id(node))
         && bzla_node_bv_get_width(s_bzla, node) == 1;
}

/* -------------------------------------------------------------------------- */

template <bool is_signed>
BzlaSymBV<is_signed>::BzlaSymBV(BzlaNode *node)
{
  assert(s_bzla);
  assert(checkNode(node));
  d_node = bzla_node_copy(s_bzla, node);
}

template <bool is_signed>
BzlaSymBV<is_signed>::BzlaSymBV(const bwt w, const uint32_t val)
{
  assert(s_bzla);
  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  d_node       = bzla_exp_bv_int(s_bzla, val, s);
  bzla_sort_release(s_bzla, s);
}

template <bool is_signed>
BzlaSymBV<is_signed>::BzlaSymBV(const BzlaSymProp &p)
{
  assert(s_bzla);
  // TODO
}

template <bool is_signed>
BzlaSymBV<is_signed>::BzlaSymBV(const BzlaSymBV<is_signed> &other)
{
  assert(s_bzla);
  assert(checkNode(other.d_node));
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool is_signed>
BzlaSymBV<is_signed>::BzlaSymBV(const BzlaBitVector *bv)
{
  assert(s_bzla);
  d_node = bzla_exp_bv_const(s_bzla, bv);
}

template <bool is_signed>
BzlaSymBV<is_signed>::~BzlaSymBV()
{
  assert(s_bzla);
  bzla_node_release(s_bzla, d_node);
}

template <bool is_signed>
bwt
BzlaSymBV<is_signed>::getWidth(void) const
{
  assert(s_bzla);
  return bzla_node_bv_get_width(s_bzla, d_node);
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::one(const bwt &w)
{
  assert(s_bzla);
  BzlaSortId s             = bzla_sort_bv(s_bzla, w);
  BzlaNode *n              = bzla_exp_bv_one(s_bzla, s);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::zero(const bwt &w)
{
  assert(s_bzla);
  BzlaSortId s             = bzla_sort_bv(s_bzla, w);
  BzlaNode *n              = bzla_exp_bv_zero(s_bzla, s);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::allOnes(const bwt &w)
{
  assert(s_bzla);
  BzlaSortId s             = bzla_sort_bv(s_bzla, w);
  BzlaNode *n              = bzla_exp_bv_ones(s_bzla, s);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::isAllOnes() const
{
  return *this == BzlaSymBV<is_signed>::allOnes(this->getWidth());
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::isAllZeros() const
{
  return *this == BzlaSymBV<is_signed>::zero(this->getWidth());
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::maxValue(const bwt &w)
{
  assert(s_bzla);
  BzlaSortId s             = bzla_sort_bv(s_bzla, w);
  BzlaNode *n              = bzla_exp_bv_max_signed(s_bzla, s);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::minValue(const bwt &w)
{
  assert(s_bzla);
  BzlaSortId s             = bzla_sort_bv(s_bzla, w);
  BzlaNode *n              = bzla_exp_bv_min_signed(s_bzla, s);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  bzla_sort_release(s_bzla, s);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator<<(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_sll(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator>>(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sra(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_srl(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator|(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_or(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator&(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_and(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator+(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_add(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator-(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_sub(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator*(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_mul(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator/(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sdiv(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_udiv(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator%(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_srem(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_urem(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator-(void) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_neg(s_bzla, d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::operator~(void) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_not(s_bzla, d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::increment() const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_inc(s_bzla, d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::decrement() const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_dec(s_bzla, d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::signExtendRightShift(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_sra(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularLeftShift(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this << op;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularRightShift(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this >> op;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularIncrement() const
{
  assert(s_bzla);
  return this->increment();
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularDecrement() const
{
  assert(s_bzla);
  return this->decrement();
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularAdd(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  return *this + op;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::modularNegate() const
{
  assert(s_bzla);
  return -(*this);
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::operator==(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n     = bzla_exp_eq(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::operator<=(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_slte(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ulte(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::operator>=(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sgte(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ugte(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::operator<(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_slt(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ult(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymProp
BzlaSymBV<is_signed>::operator>(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sgt(s_bzla, d_node, op.d_node)
                          : bzla_exp_bv_ugt(s_bzla, d_node, op.d_node);
  BzlaSymProp res = BzlaSymProp(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<true>
BzlaSymBV<is_signed>::toSigned(void) const
{
  return BzlaSymBV<true>(*this);
}

template <bool is_signed>
BzlaSymBV<false>
BzlaSymBV<is_signed>::toUnsigned(void) const
{
  return BzlaSymBV<false>(*this);
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::extend(bwt extension) const
{
  assert(s_bzla);
  BzlaNode *n = is_signed ? bzla_exp_bv_sext(s_bzla, d_node, extension)
                          : bzla_exp_bv_uext(s_bzla, d_node, extension);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::contract(bwt reduction) const
{
  assert(s_bzla);
  assert(this->getWidth() > reduction);
  BzlaNode *n =
      bzla_exp_bv_slice(s_bzla, d_node, this->getWidth - 1 - reduction, 0);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::resize(bwt newSize) const
{
  bwt bw = this->getWidth();
  if (newSize > bw) return this->extend(newSize - bw);
  if (newSize < bw) return this->contract(bw - newSize);
  return *this;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::matchWidth(const BzlaSymBV<is_signed> &op) const
{
  assert(this->getWidth() <= op.getWidth());
  return this->extend(op.getWidth() - this->getWidth());
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::append(const BzlaSymBV<is_signed> &op) const
{
  assert(s_bzla);
  BzlaNode *n              = bzla_exp_bv_concat(s_bzla, d_node, op.d_node);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
BzlaSymBV<is_signed>
BzlaSymBV<is_signed>::extract(bwt upper, bwt lower) const
{
  assert(s_bzla);
  assert(upper >= lower);
  BzlaNode *n              = bzla_exp_bv_slice(s_bzla, d_node, upper, lower);
  BzlaSymBV<is_signed> res = BzlaSymBV<is_signed>(n);
  bzla_node_release(s_bzla, n);
  return res;
}

template <bool is_signed>
bool
BzlaSymBV<is_signed>::checkNode(const BzlaNode *node)
{
  return bzla_sort_is_bv(node->bzla, bzla_node_get_sort_id(node));
}

// BzlaNode* BzlaSymBV::boolNodeToBV(BzlaNode* node) const;
// BzlaNode* BzlaSymBV::BVToBoolNode(BzlaNode* node) const;

// template <bool is_signed>
// BzlaNode *
// BzlaSymBV<is_signed>::fromProposition (BzlaNode *node) const
//{
//  assert (s_bzla);
//  assert (checkNode (node));
//  return node;
//}
//
// template <bool is_signed>
// BzlaNode *
// BzlaSymBV<is_signed>::toProposition (BzlaNode *node) const
//{
//  assert (s_bzla);
//  assert (checkNode (node));
//  return node;
//}
