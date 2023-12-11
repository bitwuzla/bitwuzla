/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED
#define BZLA_SOLVER_FP_SYMFPU_WRAPPER_H_INCLUDED

#include <symfpu/core/ite.h>
#include <symfpu/utils/numberOfRoundingModes.h>

#include <cstdint>

#include "bv/bitvector.h"
#include "node/node.h"
#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla {
namespace fp {

template <bool T>
class SymFpuSymBV;
class WordBlaster;

/* ========================================================================== */
/* Glue for SymFPU: concrete.                                                 */
/* ========================================================================== */

/* Mapping between types. */
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
  // TODO: This doesn't have to be a pointer
  std::unique_ptr<BitVector> d_bv;
};

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class SymFpuTraits
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = RoundingMode;
  using fpt  = FloatingPointTypeInfo;
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
/* Wrapper for propositions.                                                  */
/* -------------------------------------------------------------------------- */

class SymFpuSymProp
{
  friend WordBlaster;
  friend SymFpuSymBV<true>;
  friend SymFpuSymBV<false>;
  friend ::symfpu::ite<SymFpuSymProp, SymFpuSymProp>;

 public:
  SymFpuSymProp(const Node &node);
  SymFpuSymProp(bool v);
  SymFpuSymProp(const SymFpuSymProp &other);
  ~SymFpuSymProp();

  const Node &getNode() const { return d_node; }

  SymFpuSymProp &operator=(const SymFpuSymProp &other);

  SymFpuSymProp operator!(void) const;
  SymFpuSymProp operator&&(const SymFpuSymProp &op) const;
  SymFpuSymProp operator||(const SymFpuSymProp &op) const;
  SymFpuSymProp operator==(const SymFpuSymProp &op) const;
  SymFpuSymProp operator^(const SymFpuSymProp &op) const;

 protected:
  bool check_node(const Node &node) const;

 private:
  Node d_node;
};

/* -------------------------------------------------------------------------- */
/* Wrapper for bit-vector terms.                                              */
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
  SymFpuSymBV(const Node &node);
  SymFpuSymBV(const uint32_t w, const uint32_t val);
  SymFpuSymBV(const SymFpuSymProp &p);
  SymFpuSymBV(const SymFpuSymBV<is_signed> &other);
  SymFpuSymBV(const SymFpuSymBV<!is_signed> &other);
  SymFpuSymBV(const BitVector &bv);
  SymFpuSymBV(const SymFpuBV<is_signed> &bv);
  /** Construrs for Boolean nodes. */
  SymFpuSymBV(bool v);
  /** Destructor. */
  ~SymFpuSymBV();

  SymFpuSymBV<is_signed> &operator=(const SymFpuSymBV<is_signed> &other);

  uint32_t getWidth(void) const;
  const Node &getNode(void) const { return d_node; }

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

  bool check_node(const Node &node) const;
  bool check_bool_node(const Node &node) const;
  // BzlaNode *fromProposition (BzlaNode *node) const;
  // BzlaNode *toProposition (BzlaNode *node) const;

 private:
  Node d_node;
};
/* -------------------------------------------------------------------------- */
/* Wrapper for rounding modes.                                                */
/* -------------------------------------------------------------------------- */

class SymFpuSymRM
{
  friend WordBlaster;
  friend symfpu::ite<SymFpuSymProp, SymFpuSymRM>;

 public:
  /* Constructors. */
  SymFpuSymRM(const Node &node);
  SymFpuSymRM(const RoundingMode rm);
  SymFpuSymRM(const SymFpuSymRM &other);
  /* Destructor. */
  ~SymFpuSymRM();

  const Node &getNode() const { return d_node; }

  SymFpuSymProp valid(void) const;
  SymFpuSymProp operator==(const SymFpuSymRM &other) const;

 protected:
  bool check_node(const Node &node) const;

 private:
  Node mk_value(const RoundingMode rm);
  Node d_node;
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
  using fpt  = FloatingPointTypeInfo;
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
  }
BZLA_FP_ITE(bzla::fp::SymFpuTraits::rm);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::prop);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::sbv);
BZLA_FP_ITE(bzla::fp::SymFpuTraits::ubv);
#undef BZLA_FP_ITE

#define BZLA_FP_SYM_ITE(T)                                               \
  template <>                                                            \
  struct ite<bzla::fp::SymFpuSymProp, T>                                 \
  {                                                                      \
    static const T iteOp(const bzla::fp::SymFpuSymProp &_c,              \
                         const T &_t,                                    \
                         const T &_e)                                    \
    {                                                                    \
      assert(!_c.getNode().is_null());                                   \
      assert(!_t.getNode().is_null());                                   \
      assert(!_e.getNode().is_null());                                   \
      bzla::NodeManager &nm = bzla::NodeManager::get();                  \
      return nm.mk_node(                                                 \
          bzla::node::Kind::ITE,                                         \
          {nm.mk_node(                                                   \
               bzla::node::Kind::EQUAL,                                  \
               {_c.getNode(), nm.mk_value(bzla::BitVector::mk_true())}), \
           _t.getNode(),                                                 \
           _e.getNode()});                                               \
    }                                                                    \
  }
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::rm);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::prop);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::sbv);
BZLA_FP_SYM_ITE(bzla::fp::SymFpuSymTraits::ubv);
#undef BZLA_FP_SYM_ITE
}  // namespace symfpu

/* -------------------------------------------------------------------------- */
#endif
