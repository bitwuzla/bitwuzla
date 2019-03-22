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
  BzlaSymProp(const BzlaNode *node);
  BzlaSymProp(bool v);
  BzlaSymProp(const BzlaSymProp &other);

  BzlaSymProp operator!(void) const;
  BzlaSymProp operator&&(const BzlaSymProp &op) const;
  BzlaSymProp operator||(const BzlaSymProp &op) const;
  BzlaSymProp operator==(const BzlaSymProp &op) const;
  BzlaSymProp operator^(const BzlaSymProp &op) const;

 protected:
  bool checkNode(const BzlaNode *node);
};

/* Bitwuzla wrapper for bit-vector terms. ---------------------------------- */
template <bool isSigned>
class BzlaSymBV
{
  friend BzlaSymBV<!isSigned>; /* Allow conversion between the sorts. */
#ifdef BZLA_USE_SYMFPU
  friend ::symfpu::ite<BzlaSymProp, BzlaSymBV<isSigned> >;
#endif

 public:
  BzlaSymBV(BzlaNode *node);
  BzlaSymBV(const bwt w, const uint32_t val);
  BzlaSymBV(const BzlaSymProp &p);
  BzlaSymBV(const BzlaSymBV<isSigned> &other);
  BzlaSymBV(const BzlaBitVector *bv);
  ~BzlaSymBV();

  bwt getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }
  static void setBtor(Bzla *bzla) { s_bzla = bzla; }

  /*** Constant creation and test ***/
  static BzlaSymBV<isSigned> one(const bwt &w);
  static BzlaSymBV<isSigned> zero(const bwt &w);
  static BzlaSymBV<isSigned> allOnes(const bwt &w);

  BzlaSymProp isAllOnes() const;
  BzlaSymProp isAllZeros() const;

  static BzlaSymBV<isSigned> maxValue(const bwt &w);
  static BzlaSymBV<isSigned> minValue(const bwt &w);

  /*** Operators ***/
  BzlaSymBV<isSigned> operator<<(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator>>(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator|(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator&(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator+(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator-(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator*(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator/(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator%(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> operator-(void) const;
  BzlaSymBV<isSigned> operator~(void) const;
  BzlaSymBV<isSigned> increment() const;
  BzlaSymBV<isSigned> decrement() const;
  BzlaSymBV<isSigned> signExtendRightShift(const BzlaSymBV<isSigned> &op) const;

  /*** Modular operations ***/
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  BzlaSymBV<isSigned> modularLeftShift(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> modularRightShift(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> modularIncrement() const;
  BzlaSymBV<isSigned> modularDecrement() const;
  BzlaSymBV<isSigned> modularAdd(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> modularNegate() const;

  /*** Comparisons ***/
  BzlaSymProp operator==(const BzlaSymBV<isSigned> &op) const;
  BzlaSymProp operator<=(const BzlaSymBV<isSigned> &op) const;
  BzlaSymProp operator>=(const BzlaSymBV<isSigned> &op) const;
  BzlaSymProp operator<(const BzlaSymBV<isSigned> &op) const;
  BzlaSymProp operator>(const BzlaSymBV<isSigned> &op) const;

  /*** Type conversion ***/
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  BzlaSymBV<true> toSigned(void) const;
  BzlaSymBV<false> toUnsigned(void) const;

  /*** Bit hacks ***/
  BzlaSymBV<isSigned> extend(bwt extension) const;
  BzlaSymBV<isSigned> contract(bwt reduction) const;
  BzlaSymBV<isSigned> resize(bwt newSize) const;
  BzlaSymBV<isSigned> matchWidth(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> append(const BzlaSymBV<isSigned> &op) const;
  BzlaSymBV<isSigned> extract(bwt upper, bwt lower) const;

 protected:
  typedef typename BzlaSignedToLitSort<isSigned>::BzlaLitSort literalType;

  // BzlaNode* boolNodeToBV(BzlaNode* node) const;
  // BzlaNode* BVToBoolNode(BzlaNode* node) const;

  bool checkNode(const BzlaNode *node);
  BzlaNode *fromProposition(BzlaNode *node) const;
  BzlaNode *toProposition(BzlaNode *node) const;

 private:
  BzlaNode *d_node;
  static Bzla *s_bzla;
};

/* -------------------------------------------------------------------------- */

template <bool isSigned>
BzlaSymBV<isSigned>::BzlaSymBV(BzlaNode *node) : d_node(node)
{
  assert(checkNode(node));
}

template <bool isSigned>
BzlaSymBV<isSigned>::BzlaSymBV(const bwt w, const uint32_t val)
{
  BzlaSortId s = bzla_sort_bv(s_bzla, w);
  d_node       = bzla_exp_bv_int(s_bzla, val, s);
}

template <bool isSigned>
BzlaSymBV<isSigned>::BzlaSymBV(const BzlaSymProp &p)
{
  // TODO
}

template <bool isSigned>
BzlaSymBV<isSigned>::BzlaSymBV(const BzlaSymBV<isSigned> &other)
{
  d_node = bzla_node_copy(s_bzla, other.d_node);
}

template <bool isSigned>
BzlaSymBV<isSigned>::BzlaSymBV(const BzlaBitVector *bv)
    : d_node(bzla_exp_bv_const(s_bzla, bv))
{
}

template <bool isSigned>
BzlaSymBV<isSigned>::~BzlaSymBV()
{
  bzla_node_release(s_bzla, d_node);
}

template <bool isSigned>
bwt
BzlaSymBV<isSigned>::getWidth(void) const
{
  return bzla_node_bv_get_width(s_bzla, d_node);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::one(const bwt &w)
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::zero(const bwt &w)
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::allOnes(const bwt &w)
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::isAllOnes() const
{
  // TODO
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::isAllZeros() const
{
  // TODO
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::maxValue(const bwt &w)
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::minValue(const bwt &w)
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator<<(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator>>(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator|(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator&(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator+(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator-(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator*(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator/(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator%(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator-(void) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::operator~(void) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::increment() const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::decrement() const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::signExtendRightShift(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularLeftShift(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularRightShift(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularIncrement() const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularDecrement() const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularAdd(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::modularNegate() const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::operator==(const BzlaSymBV<isSigned> &op) const
{
  // TODO
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::operator<=(const BzlaSymBV<isSigned> &op) const
{
  // TODO
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::operator>=(const BzlaSymBV<isSigned> &op) const
{
  // TODO
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::operator<(const BzlaSymBV<isSigned> &op) const
{
  // TODO
}

template <bool isSigned>
BzlaSymProp
BzlaSymBV<isSigned>::operator>(const BzlaSymBV<isSigned> &op) const
{
  // TODO
}

template <bool isSigned>
BzlaSymBV<true>
BzlaSymBV<isSigned>::toSigned(void) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<false>
BzlaSymBV<isSigned>::toUnsigned(void) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::extend(bwt extension) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::contract(bwt reduction) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::resize(bwt newSize) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::matchWidth(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::append(const BzlaSymBV<isSigned> &op) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
BzlaSymBV<isSigned>
BzlaSymBV<isSigned>::extract(bwt upper, bwt lower) const
{
  // TODO
  return BzlaSymBV<isSigned>(1, 0);
}

template <bool isSigned>
bool
BzlaSymBV<isSigned>::checkNode(const BzlaNode *node)
{
  return bzla_sort_is_bv(node->bzla, bzla_node_get_sort_id(node));
}

// BzlaNode* BzlaSymBV::boolNodeToBV(BzlaNode* node) const;
// BzlaNode* BzlaSymBV::BVToBoolNode(BzlaNode* node) const;

template <bool isSigned>
BzlaNode *
BzlaSymBV<isSigned>::fromProposition(BzlaNode *node) const
{
  assert(checkNode(node));
  // TODO
}

template <bool isSigned>
BzlaNode *
BzlaSymBV<isSigned>::toProposition(BzlaNode *node) const
{
  assert(checkNode(node));
  // TODO
}

/* ========================================================================== */

extern "C" {

BzlaNode *
bzla_exp_fp_rne(Bzla *bzla)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rna(Bzla *bzla)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtp(Bzla *bzla)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtn(Bzla *bzla)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rtz(Bzla *bzla)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_pos_zero(Bzla *bzla, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg_zero(Bzla *bzla, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_pos_inf(Bzla *bzla, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg_inf(Bzla *bzla, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_nan(Bzla *bzla, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_const(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_abs(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_neg(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_normal(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_subnormal(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_zero(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_inf(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_nan(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_neg(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_is_pos(Bzla *bzla, BzlaNode *node)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  /// FP STUB
  (void) node;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_min(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_max(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_rem(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_eq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_leq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_lt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_geq(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_gt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_sqrt(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_round_to_int(Bzla *bzla, BzlaNode *e0, BzlaNode *e1)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_add(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_sub(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_mul(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_div(Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_fma(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, BzlaNode *e2, BzlaNode *e3)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(bzla == bzla_node_real_addr(e2)->bzla);
  assert(bzla == bzla_node_real_addr(e3)->bzla);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) e2;
  (void) e3;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp(Bzla *bzla, BzlaNode *node, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) node;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_signed(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_unsigned(
    Bzla *bzla, BzlaNode *e0, BzlaNode *e1, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(e0)->bzla);
  assert(bzla == bzla_node_real_addr(e1)->bzla);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) e0;
  (void) e1;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}

BzlaNode *
bzla_exp_fp_to_fp_real(
    Bzla *bzla, BzlaNode *node, const char *real, uint32_t eb, uint32_t sb)
{
#if !defined(BZLA_USE_SYMFPU)
  BZLA_ABORT(true, "SymFPU not configured");
#endif
  assert(bzla == bzla_node_real_addr(node)->bzla);
  assert(real);
  assert(eb);
  assert(sb);
  /// FP STUB
  (void) node;
  (void) real;
  (void) eb;
  (void) sb;
  return bzla_exp_true(bzla);
  ////
}
}
