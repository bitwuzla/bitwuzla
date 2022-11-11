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

#include "bv/bitvector.h"
#include "symfpu/core/ite.h"
#include "symfpu/utils/numberOfRoundingModes.h"

namespace bzla {
namespace fp {

template <bool T>
class SymFpuSymBVOld;
class WordBlaster;
class WordBlasterOld;

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
  friend SymFpuSymBVOld<true>;
  friend SymFpuSymBVOld<false>;
  friend WordBlaster;
  friend WordBlasterOld;

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

class SymFpuSymRMOld;
class SymFpuSymPropOld;
template <bool T>
class SymFpuSymBVOld;

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

class SymFpuSymPropOld
{
  friend WordBlaster;
  friend WordBlasterOld;
  friend SymFpuSymBVOld<true>;
  friend SymFpuSymBVOld<false>;
  friend ::symfpu::ite<SymFpuSymPropOld, SymFpuSymPropOld>;

 public:
  SymFpuSymPropOld(BzlaNode *node);
  SymFpuSymPropOld(bool v);
  SymFpuSymPropOld(const SymFpuSymPropOld &other);
  ~SymFpuSymPropOld();

  BzlaNode *getNode() const { return d_node; }

  SymFpuSymPropOld &operator=(const SymFpuSymPropOld &other);

  SymFpuSymPropOld operator!(void) const;
  SymFpuSymPropOld operator&&(const SymFpuSymPropOld &op) const;
  SymFpuSymPropOld operator||(const SymFpuSymPropOld &op) const;
  SymFpuSymPropOld operator==(const SymFpuSymPropOld &op) const;
  SymFpuSymPropOld operator^(const SymFpuSymPropOld &op) const;

 protected:
  bool check_node(const BzlaNode *node) const;

 private:
  static inline Bzla *s_bzla = nullptr;
  BzlaNode *d_node;
};

/* -------------------------------------------------------------------------- */
/* Wrapper for bit-vector terms.                                              */
/* -------------------------------------------------------------------------- */

template <bool is_signed>
class SymFpuSymBVOld;

template <bool is_signed>
class SymFpuSymBVOld
{
  friend WordBlaster;
  friend WordBlasterOld;
  friend SymFpuSymBVOld<!is_signed>; /* Allow conversion between the sorts. */
  friend ::symfpu::ite<SymFpuSymPropOld, SymFpuSymBVOld<is_signed> >;

 public:
  /** Constructors for bit-vector nodes. */
  SymFpuSymBVOld(BzlaNode *node);
  SymFpuSymBVOld(const uint32_t w, const uint32_t val);
  SymFpuSymBVOld(const SymFpuSymPropOld &p);
  SymFpuSymBVOld(const SymFpuSymBVOld<is_signed> &other);
  SymFpuSymBVOld(const SymFpuSymBVOld<!is_signed> &other);
  SymFpuSymBVOld(const BitVector &bv);
  SymFpuSymBVOld(const SymFpuBV<is_signed> &bv);
  /** Constructors for Boolean nodes. */
  SymFpuSymBVOld(bool v);
  /** Destructor. */
  ~SymFpuSymBVOld();

  SymFpuSymBVOld<is_signed> &operator=(const SymFpuSymBVOld<is_signed> &other);

  uint32_t getWidth(void) const;
  BzlaNode *getNode(void) const { return d_node; }

  /** Constant creation and test */
  static SymFpuSymBVOld<is_signed> one(const uint32_t &w);
  static SymFpuSymBVOld<is_signed> zero(const uint32_t &w);
  static SymFpuSymBVOld<is_signed> allOnes(const uint32_t &w);

  SymFpuSymPropOld isAllOnes() const;
  SymFpuSymPropOld isAllZeros() const;

  static SymFpuSymBVOld<is_signed> maxValue(const uint32_t &w);
  static SymFpuSymBVOld<is_signed> minValue(const uint32_t &w);

  /** Operators */
  SymFpuSymBVOld<is_signed> operator<<(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator>>(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator|(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator&(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator+(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator-(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator*(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator/(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator%(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> operator-(void) const;
  SymFpuSymBVOld<is_signed> operator~(void) const;
  SymFpuSymBVOld<is_signed> increment() const;
  SymFpuSymBVOld<is_signed> decrement() const;
  SymFpuSymBVOld<is_signed> signExtendRightShift(
      const SymFpuSymBVOld<is_signed> &op) const;

  /** Modular operations */
  // This back-end doesn't do any overflow checking so these are the same as
  // other operations
  SymFpuSymBVOld<is_signed> modularLeftShift(
      const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> modularRightShift(
      const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> modularIncrement() const;
  SymFpuSymBVOld<is_signed> modularDecrement() const;
  SymFpuSymBVOld<is_signed> modularAdd(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> modularNegate() const;

  /** Operators for Boolean nodes */
  SymFpuSymPropOld operator!(void) const;
  SymFpuSymPropOld operator&&(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator||(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator^(const SymFpuSymBVOld<is_signed> &op) const;

  /** Comparisons */
  SymFpuSymPropOld operator==(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator<=(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator>=(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator<(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymPropOld operator>(const SymFpuSymBVOld<is_signed> &op) const;

  /** Type conversion */
  // Bitwuzla nodes make no distinction between signed and unsigned, thus these
  // are trivial
  SymFpuSymBVOld<true> toSigned(void) const;
  SymFpuSymBVOld<false> toUnsigned(void) const;

  /** Bit hacks */
  SymFpuSymBVOld<is_signed> extend(uint32_t extension) const;
  SymFpuSymBVOld<is_signed> contract(uint32_t reduction) const;
  SymFpuSymBVOld<is_signed> resize(uint32_t newSize) const;
  SymFpuSymBVOld<is_signed> matchWidth(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> append(const SymFpuSymBVOld<is_signed> &op) const;
  SymFpuSymBVOld<is_signed> extract(uint32_t upper, uint32_t lower) const;

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

/* -------------------------------------------------------------------------- */
/* Wrapper for rounding modes.                                                */
/* -------------------------------------------------------------------------- */

class SymFpuSymRMOld
{
  friend WordBlaster;
  friend WordBlasterOld;
  friend symfpu::ite<SymFpuSymPropOld, SymFpuSymRMOld>;

 public:
  /* Constructors. */
  SymFpuSymRMOld(BzlaNode *node);
  SymFpuSymRMOld(const RoundingMode rm);
  SymFpuSymRMOld(const SymFpuSymRMOld &other);
  /* Destructor. */
  ~SymFpuSymRMOld();

  BzlaNode *getNode() const { return d_node; }

  SymFpuSymPropOld valid(void) const;
  SymFpuSymPropOld operator==(const SymFpuSymRMOld &other) const;

 protected:
  bool check_node(const BzlaNode *node) const;

 private:
  static inline Bzla *s_bzla = nullptr;
  BzlaNode *init_const(const RoundingMode rm);
  BzlaNode *d_node;
};

/* -------------------------------------------------------------------------- */
/* Template parameter for SymFPU templates.                                   */
/* -------------------------------------------------------------------------- */

class SymFpuSymTraitsOld
{
 public:
  /* The six key types that SymFPU uses. */
  using bwt  = uint32_t;
  using rm   = SymFpuSymRMOld;
  using fpt  = FloatingPointTypeInfo;
  using prop = SymFpuSymPropOld;
  using sbv  = SymFpuSymBVOld<true>;
  using ubv  = SymFpuSymBVOld<false>;

  /* Give concrete instances (wrapped nodes) for each rounding mode. */
  static SymFpuSymRMOld RNE(void);
  static SymFpuSymRMOld RNA(void);
  static SymFpuSymRMOld RTP(void);
  static SymFpuSymRMOld RTN(void);
  static SymFpuSymRMOld RTZ(void);

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

#define BZLA_FP_ITE_OLD(T)                                          \
  template <>                                                       \
  struct ite<bool, T>                                               \
  {                                                                 \
    static const T &iteOp(const bool &_c, const T &_t, const T &_e) \
    {                                                               \
      return _c ? _t : _e;                                          \
    }                                                               \
  };
BZLA_FP_ITE_OLD(bzla::fp::SymFpuTraits::rm);
BZLA_FP_ITE_OLD(bzla::fp::SymFpuTraits::prop);
BZLA_FP_ITE_OLD(bzla::fp::SymFpuTraits::sbv);
BZLA_FP_ITE_OLD(bzla::fp::SymFpuTraits::ubv);
#undef BZLA_FP_ITE_OLD

#define BZLA_FP_SYM_ITE_OLD(T)                                 \
  template <>                                                  \
  struct ite<bzla::fp::SymFpuSymPropOld, T>                    \
  {                                                            \
    static const T iteOp(const bzla::fp::SymFpuSymPropOld &_c, \
                         const T &_t,                          \
                         const T &_e)                          \
    {                                                          \
      BzlaNode *c = _c.getNode();                              \
      BzlaNode *t = _t.getNode();                              \
      BzlaNode *e = _e.getNode();                              \
      assert(c);                                               \
      assert(t);                                               \
      assert(e);                                               \
      Bzla *bzla = T::s_bzla;                                  \
      assert(bzla);                                            \
      assert(bzla == bzla_node_real_addr(c)->bzla);            \
      assert(bzla == bzla_node_real_addr(t)->bzla);            \
      assert(bzla == bzla_node_real_addr(e)->bzla);            \
      BzlaNode *ite = bzla_exp_cond(bzla, c, t, e);            \
      T res(ite);                                              \
      bzla_node_release(bzla, ite);                            \
      return res;                                              \
    }                                                          \
  };
BZLA_FP_SYM_ITE_OLD(bzla::fp::SymFpuSymTraitsOld::rm);
BZLA_FP_SYM_ITE_OLD(bzla::fp::SymFpuSymTraitsOld::prop);
BZLA_FP_SYM_ITE_OLD(bzla::fp::SymFpuSymTraitsOld::sbv);
BZLA_FP_SYM_ITE_OLD(bzla::fp::SymFpuSymTraitsOld::ubv);
#undef BZLA_FP_SYM_ITE_OLD

}  // namespace symfpu

/* -------------------------------------------------------------------------- */
#endif
