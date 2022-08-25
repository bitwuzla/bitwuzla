#ifndef BZLA_NODE_KIND_H_INCLUDED
#define BZLA_NODE_KIND_H_INCLUDED

#include <array>
#include <cstddef>
#include <cstdint>
#include <sstream>

namespace bzla::node {

/* --- Kind ---------------------------------------------------------------- */

enum class Kind
{
  NULL_NODE = 0,

  VALUE,
  CONSTANT,
  VARIABLE,

  /* --- Unary ------------------------------------------------------------- */
  NOT,
  AND,
  OR,
  BV_EXTRACT,
  FP_ABS,
  FP_IS_INF,
  FP_IS_NAN,
  FP_IS_NEG,
  FP_IS_NORM,
  FP_IS_POS,
  FP_IS_SUBNORM,
  FP_IS_ZERO,
  FP_NEG,
  FP_TO_FP_FROM_BV,  // ((_ to_fp eb sb) (BitVec eb+sb))
  /* --- Binary ------------------------------------------------------------ */
  EQUAL,
  BV_NOT,
  BV_AND,
  BV_ADD,
  BV_MUL,
  BV_ULT,
  BV_SHL,
  BV_SLT,
  BV_SHR,
  BV_ASHR,
  BV_UDIV,
  BV_UREM,
  BV_CONCAT,
  FP_EQUAL,
  FP_LE,
  FP_LT,
  FP_MIN,
  FP_MAX,
  FP_SQRT,
  FP_REM,
  FP_RTI,
  FP_TO_SBV,          // ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb))
  FP_TO_UBV,          // ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb))
  FP_TO_FP_FROM_FP,   // ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb))
  FP_TO_FP_FROM_SBV,  // ((_ to_fp eb sb) RoundingMode (_ BitVec m))
  FP_TO_FP_FROM_UBV,  // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m))
  SELECT,
  APPLY,
  FORALL,
  EXISTS,
  LAMBDA,
  /* --- Ternary ----------------------------------------------------------- */
  ITE,
  FP_ADD,
  FP_MUL,
  FP_DIV,
  STORE,
  /* ----------------------------- quaternary --------------------------- */
  FP_FMA,

  NUM_KINDS,
};

struct KindInformation
{
  static constexpr uint8_t s_nary = 5;
  uint8_t num_children            = 0;
  uint8_t num_indices             = 0;
  const char* enum_name           = nullptr;
  const char* smt2_name           = nullptr;

  bool is_nary() const { return num_children == s_nary; }
};

struct KindInfo
{
  /** Return kind information for given `kind`. */
  const KindInformation& operator[](Kind kind) const
  {
    return d_info[static_cast<size_t>(kind)];
  }

  /** Initialize kind information for given `kind`. */
  constexpr KindInformation& init(Kind kind)
  {
    ++d_num_inited;
    return d_info[static_cast<size_t>(kind)];
  }

  constexpr bool complete() const
  {
    return d_num_inited == static_cast<size_t>(Kind::NUM_KINDS);
  }

 private:
  size_t d_num_inited = 0;
  std::array<KindInformation, static_cast<size_t>(Kind::NUM_KINDS)> d_info;
};

namespace {

constexpr KindInfo
mk_kind_info()
{
  KindInfo info;
  info.init(Kind::NULL_NODE)        = {0, 0, "NULL_NODE"};
  info.init(Kind::VALUE)            = {0, 0, "VALUE"};
  info.init(Kind::CONSTANT)         = {0, 0, "CONSTANT"};
  info.init(Kind::VARIABLE)         = {0, 0, "VARIABLE"};
  info.init(Kind::BV_EXTRACT)       = {1, 2, "BV_EXTRACT", "extract"};
  info.init(Kind::BV_NOT)           = {1, 0, "BV_NOT", "bvnot"};
  info.init(Kind::FP_ABS)           = {1, 0, "FP_ABS", "fp.abs"};
  info.init(Kind::FP_IS_INF)        = {1, 0, "FP_IS_INF", "fp.isInfinite"};
  info.init(Kind::FP_IS_NAN)        = {1, 0, "FP_IS_NAN", "fp.isNaN"};
  info.init(Kind::FP_IS_NEG)        = {1, 0, "FP_IS_NEG", "fp.isNegative"};
  info.init(Kind::FP_IS_NORM)       = {1, 0, "FP_IS_NORM", "fp.isNormal"};
  info.init(Kind::FP_IS_POS)        = {1, 0, "FP_IS_POS", "fp.isPositive"};
  info.init(Kind::FP_IS_SUBNORM)    = {1, 0, "FP_IS_SUBNORM", "fp.isSubnormal"};
  info.init(Kind::FP_IS_ZERO)       = {1, 0, "FP_IS_ZERO", "fp.isZero"};
  info.init(Kind::FP_NEG)           = {1, 0, "FP_IS_NEG", "fp.neg"};
  info.init(Kind::FP_TO_FP_FROM_BV) = {1, 2, "FP_TO_FP_FROM_BV", "to_fp"};
  info.init(Kind::NOT)              = {1, 0, "NOT", "not"};
  info.init(Kind::AND)              = {2, 0, "AND", "and"};
  info.init(Kind::APPLY)            = {KindInformation::s_nary, 0, "APPLY"};
  info.init(Kind::BV_ADD)           = {2, 0, "BV_ADD", "bvadd"};
  info.init(Kind::BV_AND)           = {2, 0, "BV_AND", "bvand"};
  info.init(Kind::BV_ASHR)          = {2, 0, "BV_ASHR", "bvashr"};
  info.init(Kind::BV_CONCAT)        = {2, 0, "BV_CONCAT", "concat"};
  info.init(Kind::BV_MUL)           = {2, 0, "BV_MUL", "bvmul"};
  info.init(Kind::BV_SHL)           = {2, 0, "BV_SHL", "bvshl"};
  info.init(Kind::BV_SHR)           = {2, 0, "BV_SHR", "bvshr"};
  info.init(Kind::BV_SLT)           = {2, 0, "BV_SLT", "bvslt"};
  info.init(Kind::BV_UDIV)          = {2, 0, "BV_UDIV", "bvudiv"};
  info.init(Kind::BV_ULT)           = {2, 0, "BV_ULT", "bvult"};
  info.init(Kind::BV_UREM)          = {2, 0, "BV_UREM", "bvurem"};
  info.init(Kind::EQUAL)            = {2, 0, "EQUAL", "="};
  info.init(Kind::EXISTS)           = {2, 0, "EXISTS", "exists"};
  info.init(Kind::FORALL)           = {2, 0, "FORALL", "forall"};
  info.init(Kind::FP_EQUAL)         = {2, 0, "FP_EQUAL", "fp.eq"};
  info.init(Kind::FP_LE)            = {2, 0, "FP_LE", "fp.leq"};
  info.init(Kind::FP_LT)            = {2, 0, "FP_LT", "fp.lt"};
  info.init(Kind::FP_MAX)           = {2, 0, "FP_MAX", "fp.max"};
  info.init(Kind::FP_MIN)           = {2, 0, "FP_MIN", "fp.min"};
  info.init(Kind::FP_REM)           = {2, 0, "FP_REM", "fp.rem"};
  info.init(Kind::FP_RTI)           = {2, 0, "FP_RTI", "fp.roundToIntegral"};
  info.init(Kind::FP_SQRT)          = {2, 0, "FP_SQRT", "fp.sqrt"};
  info.init(Kind::FP_TO_FP_FROM_FP) = {2, 2, "FP_TO_FP_FROM_FP", "to_fp"};
  info.init(Kind::FP_TO_FP_FROM_SBV) = {2, 2, "FP_TO_FP_FROM_SBV", "to_fp"};
  info.init(Kind::FP_TO_FP_FROM_UBV) = {
      2, 2, "FP_TO_FP_FROM_UBV", "to_fp_unsigned"};
  info.init(Kind::FP_TO_SBV) = {2, 1, "FP_TO_SBV", "to_sbv"};
  info.init(Kind::FP_TO_UBV) = {2, 1, "FP_TO_UBV", "to_ubv"};
  info.init(Kind::LAMBDA)    = {2, 0, "LAMBDA", "lambda"};
  info.init(Kind::OR)        = {2, 0, "OR", "or"};
  info.init(Kind::SELECT)    = {2, 0, "SELECT", "select"};
  info.init(Kind::FP_ADD)    = {3, 0, "FP_ADD", "fp.add"};
  info.init(Kind::FP_DIV)    = {3, 0, "FP_DIV", "fp.div"};
  info.init(Kind::FP_MUL)    = {3, 0, "FP_MUL", "fp.mul"};
  info.init(Kind::ITE)       = {3, 0, "ITE", "ite"};
  info.init(Kind::STORE)     = {3, 0, "STORE", "store"};
  info.init(Kind::FP_FMA)    = {4, 0, "FP_FMA", "fp.fma"};
  return info;
}

}  // namespace

static constexpr KindInfo s_node_kind_info = mk_kind_info();
static_assert(s_node_kind_info.complete(), "KindInfo not fully initialized.");

std::ostream& operator<<(std::ostream& out, Kind kind);

}  // namespace bzla::node
#endif
