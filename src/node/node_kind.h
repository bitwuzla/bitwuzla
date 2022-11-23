#ifndef BZLA_NODE_NODE_KIND_H_INCLUDED
#define BZLA_NODE_NODE_KIND_H_INCLUDED

#include <array>
#include <cstddef>
#include <cstdint>
#include <sstream>

namespace bzla::node {

/* --- Kind ---------------------------------------------------------------- */

/**
 * Node kinds.
 */
enum class Kind
{
  NULL_NODE = 0,

  CONSTANT,
  VALUE,
  VARIABLE,
  DISTINCT,
  EQUAL,
  ITE,

  /* --- Boolean ------------------------------------------------------------ */
  AND,
  IMPLIES,
  NOT,
  OR,
  XOR,

  /* --- Bit-vectors -------------------------------------------------------- */
  BV_ADD,
  BV_AND,
  BV_ASHR,
  BV_COMP,
  BV_CONCAT,
  BV_DEC,
  BV_EXTRACT,
  BV_INC,
  BV_MUL,
  BV_NAND,
  BV_NEG,
  BV_NOR,
  BV_NOT,
  BV_OR,
  BV_REDAND,
  BV_REDOR,
  BV_REDXOR,
  BV_REPEAT,
  BV_ROL,
  BV_ROLI,
  BV_ROR,
  BV_RORI,
  BV_SADDO,
  BV_SDIV,
  BV_SDIVO,
  BV_SGE,
  BV_SGT,
  BV_SHL,
  BV_SHR,
  BV_SIGN_EXTEND,
  BV_SLE,
  BV_SLT,
  BV_SMOD,
  BV_SMULO,
  BV_SREM,
  BV_SSUBO,
  BV_SUB,
  BV_UADDO,
  BV_UDIV,
  BV_UGE,
  BV_UGT,
  BV_ULE,
  BV_ULT,
  BV_UMULO,
  BV_UREM,
  BV_USUBO,
  BV_XNOR,
  BV_XOR,
  BV_ZERO_EXTEND,

  /* --- Floating-points ---------------------------------------------------- */
  FP_ABS,
  FP_ADD,
  FP_DIV,
  FP_EQUAL,
  FP_FMA,
  FP_FP,
  FP_GE,
  FP_GT,
  FP_IS_INF,
  FP_IS_NAN,
  FP_IS_NEG,
  FP_IS_NORMAL,
  FP_IS_POS,
  FP_IS_SUBNORMAL,
  FP_IS_ZERO,
  FP_LE,
  FP_LT,
  FP_MAX,
  FP_MIN,
  FP_MUL,
  FP_NEG,
  FP_REM,
  FP_RTI,
  FP_SQRT,
  FP_SUB,
  FP_TO_FP_FROM_BV,   // ((_ to_fp eb sb) (BitVec eb+sb))
  FP_TO_FP_FROM_FP,   // ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb))
  FP_TO_FP_FROM_SBV,  // ((_ to_fp eb sb) RoundingMode (_ BitVec m))
  FP_TO_FP_FROM_UBV,  // ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m))
  FP_TO_SBV,          // ((_ fp.to_sbv m) RoundingMode (_ FloatingPoint eb sb))
  FP_TO_UBV,          // ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb))

  /* --- Arrays ------------------------------------------------------------- */
  CONST_ARRAY,
  SELECT,
  STORE,

  /* --- Quantifiers -------------------------------------------------------- */
  EXISTS,
  FORALL,

  /* --- Functions ---------------------------------------------------------- */
  APPLY,
  LAMBDA,

  NUM_KINDS,
};

/**
 * Struct to store information for a kind.
 */
struct KindInformation
{
  enum class Attribute
  {
    NONE,
    LEFT_ASSOC,
    RIGHT_ASSOC,
    CHAINABLE,
    PAIRWISE,
  };

  static constexpr uint8_t s_nary = 5;
  uint8_t num_children            = 0;
  uint8_t num_indices             = 0;
  const char* enum_name           = nullptr;
  const char* smt2_name           = nullptr;
  Attribute attribute             = Attribute::NONE;

  bool is_nary() const { return num_children == s_nary; }

  bool is_left_associative() const
  {
    return attribute == Attribute::LEFT_ASSOC;
  }
  bool is_right_associative() const
  {
    return attribute == Attribute::RIGHT_ASSOC;
  }
  bool is_chainable() const { return attribute == Attribute::CHAINABLE; }
  bool is_pairwise() const { return attribute == Attribute::PAIRWISE; }
};

/**
 * Struct to storing and accessing information for all kinds.
 */
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

/**
 * Initialization of the KindInfo struct.
 */
constexpr KindInfo
mk_kind_info()
{
  KindInfo info;
  info.init(Kind::NULL_NODE) = {0, 0, "NULL_NODE"};

  info.init(Kind::CONSTANT) = {0, 0, "CONSTANT"};
  info.init(Kind::VALUE)    = {0, 0, "VALUE"};
  info.init(Kind::VARIABLE) = {0, 0, "VARIABLE"};
  info.init(Kind::DISTINCT) = {
      KindInformation::s_nary, 0, "DISTINCT", "distinct"};
  info.init(Kind::EQUAL)    = {2, 0, "EQUAL", "="};
  info.init(Kind::ITE)      = {3, 0, "ITE", "ite"};
  /* Boolean */
  info.init(Kind::AND)     = {2, 0, "AND", "and"};
  info.init(Kind::IMPLIES) = {2, 0, "IMPLIES", "=>"};
  info.init(Kind::NOT)     = {1, 0, "NOT", "not"};
  info.init(Kind::OR)      = {2, 0, "OR", "or"};
  info.init(Kind::XOR)     = {2, 0, "XOR", "xor"};
  /* Bit-vectors */
  info.init(Kind::BV_ADD)         = {2, 0, "BV_ADD", "bvadd"};
  info.init(Kind::BV_AND)         = {2, 0, "BV_AND", "bvand"};
  info.init(Kind::BV_ASHR)        = {2, 0, "BV_ASHR", "bvashr"};
  info.init(Kind::BV_COMP)        = {2, 0, "BV_COMP", "bvcomp"};
  info.init(Kind::BV_CONCAT)      = {2, 0, "BV_CONCAT", "concat"};
  info.init(Kind::BV_DEC)         = {2, 0, "BV_DEC", "bvdec"};
  info.init(Kind::BV_EXTRACT)     = {1, 2, "BV_EXTRACT", "extract"};
  info.init(Kind::BV_INC)         = {2, 0, "BV_DEC", "bvinc"};
  info.init(Kind::BV_MUL)         = {2, 0, "BV_MUL", "bvmul"};
  info.init(Kind::BV_NAND)        = {2, 0, "BV_NAND", "bvnand"};
  info.init(Kind::BV_NEG)         = {1, 0, "BV_NEG", "bvneg"};
  info.init(Kind::BV_NOR)         = {2, 0, "BV_NOR", "bvnor"};
  info.init(Kind::BV_NOT)         = {1, 0, "BV_NOT", "bvnot"};
  info.init(Kind::BV_OR)          = {2, 0, "BV_OR", "bvor"};
  info.init(Kind::BV_REDAND)      = {1, 0, "BV_REDAND", "bvredand"};
  info.init(Kind::BV_REDOR)       = {1, 0, "BV_REDOR", "bvredor"};
  info.init(Kind::BV_REDXOR)      = {1, 0, "BV_REDXOR", "bvredxor"};
  info.init(Kind::BV_REPEAT)      = {1, 1, "BV_REPEAT", "repeat"};
  info.init(Kind::BV_ROL)         = {1, 1, "BV_ROL", "bvrol"};
  info.init(Kind::BV_ROLI)        = {1, 1, "BV_ROLI", "rotate_left"};
  info.init(Kind::BV_ROR)         = {2, 0, "BV_ROR", "bvror"};
  info.init(Kind::BV_RORI)        = {1, 1, "BV_RORI", "rotate_right"};
  info.init(Kind::BV_SADDO)       = {2, 0, "BV_SADDO", "bvsaddo"};
  info.init(Kind::BV_SDIV)        = {2, 0, "BV_SDIV", "bvsdiv"};
  info.init(Kind::BV_SDIVO)       = {2, 0, "BV_SDIVO", "bvsdivo"};
  info.init(Kind::BV_SGE)         = {2, 0, "BV_SGE", "bvsge"};
  info.init(Kind::BV_SGT)         = {2, 0, "BV_SGT", "bvsgt"};
  info.init(Kind::BV_SHL)         = {2, 0, "BV_SHL", "bvshl"};
  info.init(Kind::BV_SHR)         = {2, 0, "BV_SHR", "bvlshr"};
  info.init(Kind::BV_SIGN_EXTEND) = {1, 1, "BV_SIGN_EXTEND", "sign_extend"};
  info.init(Kind::BV_SLE)         = {2, 0, "BV_SLE", "bvsle"};
  info.init(Kind::BV_SLT)         = {2, 0, "BV_SLT", "bvslt"};
  info.init(Kind::BV_SMOD)        = {2, 0, "BV_SMOD", "bvsmod"};
  info.init(Kind::BV_SMULO)       = {2, 0, "BV_SMULO", "bvsmulo"};
  info.init(Kind::BV_SREM)        = {2, 0, "BV_SREM", "bvsrem"};
  info.init(Kind::BV_SSUBO)       = {2, 0, "BV_SSUBO", "bvssubo"};
  info.init(Kind::BV_SUB)         = {2, 0, "BV_SUB", "bvsub"};
  info.init(Kind::BV_UADDO)       = {2, 0, "BV_UADDO", "bvuaddo"};
  info.init(Kind::BV_UDIV)        = {2, 0, "BV_UDIV", "bvudiv"};
  info.init(Kind::BV_UGE)         = {2, 0, "BV_UGE", "bvuge"};
  info.init(Kind::BV_UGT)         = {2, 0, "BV_UGT", "bvugt"};
  info.init(Kind::BV_ULE)         = {2, 0, "BV_ULE", "bvule"};
  info.init(Kind::BV_ULT)         = {2, 0, "BV_ULT", "bvult"};
  info.init(Kind::BV_UMULO)       = {2, 0, "BV_UMULO", "bvumulo"};
  info.init(Kind::BV_UREM)        = {2, 0, "BV_UREM", "bvurem"};
  info.init(Kind::BV_USUBO)       = {2, 0, "BV_USUBO", "bvusubo"};
  info.init(Kind::BV_XNOR)        = {2, 0, "BV_XNOR", "bvxnor"};
  info.init(Kind::BV_XOR)         = {2, 0, "BV_XOR", "bvxor"};
  info.init(Kind::BV_ZERO_EXTEND) = {1, 1, "BV_ZERO_EXTEND", "zero_extend"};

  /* Floating-points */
  info.init(Kind::FP_ABS)           = {1, 0, "FP_ABS", "fp.abs"};
  info.init(Kind::FP_ADD)            = {3, 0, "FP_ADD", "fp.add"};
  info.init(Kind::FP_DIV)            = {3, 0, "FP_DIV", "fp.div"};
  info.init(Kind::FP_EQUAL)          = {2, 0, "FP_EQUAL", "fp.eq"};
  info.init(Kind::FP_FMA)            = {4, 0, "FP_FMA", "fp.fma"};
  info.init(Kind::FP_FP)             = {3, 0, "FP_FP", "fp"};
  info.init(Kind::FP_GE)             = {2, 0, "FP_GE", "fp.geq"};
  info.init(Kind::FP_GT)             = {2, 0, "FP_GT", "fp.gt"};
  info.init(Kind::FP_IS_INF)        = {1, 0, "FP_IS_INF", "fp.isInfinite"};
  info.init(Kind::FP_IS_NAN)        = {1, 0, "FP_IS_NAN", "fp.isNaN"};
  info.init(Kind::FP_IS_NEG)        = {1, 0, "FP_IS_NEG", "fp.isNegative"};
  info.init(Kind::FP_IS_NORMAL)      = {1, 0, "FP_IS_NORMAL", "fp.isNormal"};
  info.init(Kind::FP_IS_POS)        = {1, 0, "FP_IS_POS", "fp.isPositive"};
  info.init(Kind::FP_IS_SUBNORMAL)   = {
        1, 0, "FP_IS_SUBNORMAL", "fp.isSubnormal"};
  info.init(Kind::FP_IS_ZERO)        = {1, 0, "FP_IS_ZERO", "fp.isZero"};
  info.init(Kind::FP_LE)            = {2, 0, "FP_LE", "fp.leq"};
  info.init(Kind::FP_LT)            = {2, 0, "FP_LT", "fp.lt"};
  info.init(Kind::FP_MAX)           = {2, 0, "FP_MAX", "fp.max"};
  info.init(Kind::FP_MIN)           = {2, 0, "FP_MIN", "fp.min"};
  info.init(Kind::FP_MUL)            = {3, 0, "FP_MUL", "fp.mul"};
  info.init(Kind::FP_NEG)            = {1, 0, "FP_IS_NEG", "fp.neg"};
  info.init(Kind::FP_REM)           = {2, 0, "FP_REM", "fp.rem"};
  info.init(Kind::FP_RTI)           = {2, 0, "FP_RTI", "fp.roundToIntegral"};
  info.init(Kind::FP_SQRT)          = {2, 0, "FP_SQRT", "fp.sqrt"};
  info.init(Kind::FP_SUB)            = {3, 0, "FP_SUB", "fp.sub"};
  info.init(Kind::FP_TO_FP_FROM_BV)  = {1, 2, "FP_TO_FP_FROM_BV", "to_fp"};
  info.init(Kind::FP_TO_FP_FROM_FP) = {2, 2, "FP_TO_FP_FROM_FP", "to_fp"};
  info.init(Kind::FP_TO_FP_FROM_SBV) = {2, 2, "FP_TO_FP_FROM_SBV", "to_fp"};
  info.init(Kind::FP_TO_FP_FROM_UBV) = {
      2, 2, "FP_TO_FP_FROM_UBV", "to_fp_unsigned"};
  info.init(Kind::FP_TO_SBV) = {2, 1, "FP_TO_SBV", "to_sbv"};
  info.init(Kind::FP_TO_UBV) = {2, 1, "FP_TO_UBV", "to_ubv"};
  /* Arrays */
  info.init(Kind::CONST_ARRAY) = {1, 0, "CONST_ARRAY"};
  info.init(Kind::SELECT)      = {2, 0, "SELECT", "select"};
  info.init(Kind::STORE)       = {3, 0, "STORE", "store"};
  /* Quantifiers */
  info.init(Kind::EXISTS) = {2, 0, "EXISTS", "exists"};
  info.init(Kind::FORALL) = {2, 0, "FORALL", "forall"};
  /* Functions */
  info.init(Kind::APPLY)  = {KindInformation::s_nary, 0, "APPLY"};
  info.init(Kind::LAMBDA) = {2, 0, "LAMBDA", "lambda"};

  return info;
}

}  // namespace

static constexpr KindInfo s_node_kind_info = mk_kind_info();
static_assert(s_node_kind_info.complete(), "KindInfo not fully initialized.");

/**
 * Print kind to stream.
 */
std::ostream& operator<<(std::ostream& out, Kind kind);

}  // namespace bzla::node
#endif
