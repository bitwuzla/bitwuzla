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
  FP_GEQ,
  FP_GT,
  FP_IS_INF,
  FP_IS_NAN,
  FP_IS_NEG,
  FP_IS_NORMAL,
  FP_IS_POS,
  FP_IS_SUBNORMAL,
  FP_IS_ZERO,
  FP_LEQ,
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
 * Struct to storing and accessing information for all kinds.
 */
struct KindInfo
{
  constexpr KindInfo()
  {
    init(Kind::NULL_NODE, 0, 0, "NULL_NODE");

    init(Kind::CONSTANT, 0, 0, "CONSTANT");
    init(Kind::VALUE, 0, 0, "VALUE", "");
    init(Kind::VARIABLE, 0, 0, "VARIABLE");
    init(Kind::DISTINCT,
         KindInfo::s_nary,
         0,
         "DISTINCT",
         "distinct",
         KindInfo::PAIRWISE);
    init(Kind::EQUAL, 2, 0, "EQUAL", "=", KindInfo::CHAINABLE);
    init(Kind::ITE, 3, 0, "ITE", "ite");

    /* Boolean */
    init(Kind::AND, 2, 0, "AND", "and", KindInfo::LEFT_ASSOC);
    init(Kind::IMPLIES, 2, 0, "IMPLIES", "=>", KindInfo::RIGHT_ASSOC);
    init(Kind::NOT, 1, 0, "NOT", "not");
    init(Kind::OR, 2, 0, "OR", "or", KindInfo::LEFT_ASSOC);
    init(Kind::XOR, 2, 0, "XOR", "xor", KindInfo::LEFT_ASSOC);

    /* Bit-vectors */
    init(Kind::BV_ADD, 2, 0, "BV_ADD", "bvadd", KindInfo::LEFT_ASSOC);
    init(Kind::BV_AND, 2, 0, "BV_AND", "bvand", KindInfo::LEFT_ASSOC);
    init(Kind::BV_ASHR, 2, 0, "BV_ASHR", "bvashr");
    init(Kind::BV_COMP, 2, 0, "BV_COMP", "bvcomp", KindInfo::CHAINABLE);
    init(Kind::BV_CONCAT, 2, 0, "BV_CONCAT", "concat", KindInfo::LEFT_ASSOC);
    init(Kind::BV_DEC, 2, 0, "BV_DEC", "bvdec");
    init(Kind::BV_EXTRACT, 1, 2, "BV_EXTRACT", "extract");
    init(Kind::BV_INC, 2, 0, "BV_INC", "bvinc");
    init(Kind::BV_MUL, 2, 0, "BV_MUL", "bvmul", KindInfo::LEFT_ASSOC);
    init(Kind::BV_NAND, 2, 0, "BV_NAND", "bvnand");
    init(Kind::BV_NEG, 1, 0, "BV_NEG", "bvneg");
    init(Kind::BV_NOR, 2, 0, "BV_NOR", "bvnor");
    init(Kind::BV_NOT, 1, 0, "BV_NOT", "bvnot");
    init(Kind::BV_OR, 2, 0, "BV_OR", "bvor", KindInfo::LEFT_ASSOC);
    init(Kind::BV_REDAND, 1, 0, "BV_REDAND", "bvredand");
    init(Kind::BV_REDOR, 1, 0, "BV_REDOR", "bvredor");
    init(Kind::BV_REDXOR, 1, 0, "BV_REDXOR", "bvredxor");
    init(Kind::BV_REPEAT, 1, 1, "BV_REPEAT", "repeat");
    init(Kind::BV_ROL, 1, 1, "BV_ROL", "bvrol");
    init(Kind::BV_ROLI, 1, 1, "BV_ROLI", "rotate_left");
    init(Kind::BV_ROR, 2, 0, "BV_ROR", "bvror");
    init(Kind::BV_RORI, 1, 1, "BV_RORI", "rotate_right");
    init(Kind::BV_SADDO, 2, 0, "BV_SADDO", "bvsaddo");
    init(Kind::BV_SDIV, 2, 0, "BV_SDIV", "bvsdiv");
    init(Kind::BV_SDIVO, 2, 0, "BV_SDIVO", "bvsdivo");
    init(Kind::BV_SGE, 2, 0, "BV_SGE", "bvsge");
    init(Kind::BV_SGT, 2, 0, "BV_SGT", "bvsgt");
    init(Kind::BV_SHL, 2, 0, "BV_SHL", "bvshl");
    init(Kind::BV_SHR, 2, 0, "BV_SHR", "bvlshr");
    init(Kind::BV_SIGN_EXTEND, 1, 1, "BV_SIGN_EXTEND", "sign_extend");
    init(Kind::BV_SLE, 2, 0, "BV_SLE", "bvsle");
    init(Kind::BV_SLT, 2, 0, "BV_SLT", "bvslt");
    init(Kind::BV_SMOD, 2, 0, "BV_SMOD", "bvsmod");
    init(Kind::BV_SMULO, 2, 0, "BV_SMULO", "bvsmulo");
    init(Kind::BV_SREM, 2, 0, "BV_SREM", "bvsrem");
    init(Kind::BV_SSUBO, 2, 0, "BV_SSUBO", "bvssubo");
    init(Kind::BV_SUB, 2, 0, "BV_SUB", "bvsub");
    init(Kind::BV_UADDO, 2, 0, "BV_UADDO", "bvuaddo");
    init(Kind::BV_UDIV, 2, 0, "BV_UDIV", "bvudiv");
    init(Kind::BV_UGE, 2, 0, "BV_UGE", "bvuge");
    init(Kind::BV_UGT, 2, 0, "BV_UGT", "bvugt");
    init(Kind::BV_ULE, 2, 0, "BV_ULE", "bvule");
    init(Kind::BV_ULT, 2, 0, "BV_ULT", "bvult");
    init(Kind::BV_UMULO, 2, 0, "BV_UMULO", "bvumulo");
    init(Kind::BV_UREM, 2, 0, "BV_UREM", "bvurem");
    init(Kind::BV_USUBO, 2, 0, "BV_USUBO", "bvusubo");
    init(Kind::BV_XNOR, 2, 0, "BV_XNOR", "bvxnor", KindInfo::LEFT_ASSOC);
    init(Kind::BV_XOR, 2, 0, "BV_XOR", "bvxor", KindInfo::LEFT_ASSOC);
    init(Kind::BV_ZERO_EXTEND, 1, 1, "BV_ZERO_EXTEND", "zero_extend");

    /* Floating-points */
    init(Kind::FP_ABS, 1, 0, "FP_ABS", "fp.abs");
    init(Kind::FP_ADD, 3, 0, "FP_ADD", "fp.add");
    init(Kind::FP_DIV, 3, 0, "FP_DIV", "fp.div");
    init(Kind::FP_EQUAL, 2, 0, "FP_EQUAL", "fp.eq", KindInfo::CHAINABLE);
    init(Kind::FP_FMA, 4, 0, "FP_FMA", "fp.fma");
    init(Kind::FP_FP, 3, 0, "FP_FP", "fp");
    init(Kind::FP_GEQ, 2, 0, "FP_GEQ", "fp.geq", KindInfo::CHAINABLE);
    init(Kind::FP_GT, 2, 0, "FP_GT", "fp.gt", KindInfo::CHAINABLE);
    init(Kind::FP_IS_INF, 1, 0, "FP_IS_INF", "fp.isInfinite");
    init(Kind::FP_IS_NAN, 1, 0, "FP_IS_NAN", "fp.isNaN");
    init(Kind::FP_IS_NEG, 1, 0, "FP_IS_NEG", "fp.isNegative");
    init(Kind::FP_IS_NORMAL, 1, 0, "FP_IS_NORMAL", "fp.isNormal");
    init(Kind::FP_IS_POS, 1, 0, "FP_IS_POS", "fp.isPositive");
    init(Kind::FP_IS_SUBNORMAL, 1, 0, "FP_IS_SUBNORMAL", "fp.isSubnormal");
    init(Kind::FP_IS_ZERO, 1, 0, "FP_IS_ZERO", "fp.isZero");
    init(Kind::FP_LEQ, 2, 0, "FP_LEQ", "fp.leq", KindInfo::CHAINABLE);
    init(Kind::FP_LT, 2, 0, "FP_LT", "fp.lt", KindInfo::CHAINABLE);
    init(Kind::FP_MAX, 2, 0, "FP_MAX", "fp.max");
    init(Kind::FP_MIN, 2, 0, "FP_MIN", "fp.min");
    init(Kind::FP_MUL, 3, 0, "FP_MUL", "fp.mul");
    init(Kind::FP_NEG, 1, 0, "FP_NEG", "fp.neg");
    init(Kind::FP_REM, 2, 0, "FP_REM", "fp.rem");
    init(Kind::FP_RTI, 2, 0, "FP_RTI", "fp.roundToIntegral");
    init(Kind::FP_SQRT, 2, 0, "FP_SQRT", "fp.sqrt");
    init(Kind::FP_SUB, 3, 0, "FP_SUB", "fp.sub");
    init(Kind::FP_TO_FP_FROM_BV, 1, 2, "FP_TO_FP_FROM_BV", "to_fp");
    init(Kind::FP_TO_FP_FROM_FP, 2, 2, "FP_TO_FP_FROM_FP", "to_fp");
    init(Kind::FP_TO_FP_FROM_SBV, 2, 2, "FP_TO_FP_FROM_SBV", "to_fp");
    init(Kind::FP_TO_FP_FROM_UBV, 2, 2, "FP_TO_FP_FROM_UBV", "to_fp_unsigned");
    init(Kind::FP_TO_SBV, 2, 1, "FP_TO_SBV", "to_sbv");
    init(Kind::FP_TO_UBV, 2, 1, "FP_TO_UBV", "to_ubv");

    /* Arrays */
    init(Kind::CONST_ARRAY, 1, 0, "CONST_ARRAY");
    init(Kind::SELECT, 2, 0, "SELECT", "select");
    init(Kind::STORE, 3, 0, "STORE", "store");

    /* Quantifiers */
    init(Kind::EXISTS, 2, 0, "EXISTS", "exists");
    init(Kind::FORALL, 2, 0, "FORALL", "forall");

    /* Functions */
    init(Kind::APPLY, KindInfo::s_nary, 0, "APPLY");
    init(Kind::LAMBDA, 2, 0, "LAMBDA", "lambda");
  }

  /** @return The number of children for this kind. */
  uint8_t num_children(Kind kind) const;

  /** @return The number of indices for this kind. */
  uint8_t num_indices(Kind kind) const;

  /** @return The string representation for this kind. */
  const char* enum_name(Kind kind) const;

  /** @return The SMT-LIBv2 string representation for this kind. */
  const char* smt2_name(Kind kind) const;

  /** @return Does this kind support an arbitrary number of children? */
  bool is_nary(Kind kind) const;

  /** @return Is given kind left associative. */
  bool is_left_associative(Kind kind) const;

  /** @return Is given kind right associative. */
  bool is_right_associative(Kind kind) const;

  /** @return Is given kind chainable (e.g. EQUAL). */
  bool is_chainable(Kind kind) const;

  /** @return Is given kind pairwise chainable (e.g. DISTINCT). */
  bool is_pairwise(Kind kind) const;

  /** Are all kinds initialized? */
  constexpr bool complete() const
  {
    return d_num_inited == static_cast<size_t>(Kind::NUM_KINDS);
  }

 private:
  static constexpr uint8_t s_nary = UINT8_MAX;

  enum KindAttribute
  {
    NONE,
    LEFT_ASSOC,
    RIGHT_ASSOC,
    CHAINABLE,
    PAIRWISE,
  };

  struct KindData
  {
    uint8_t d_num_children    = 0;
    uint8_t d_num_indices     = 0;
    const char* d_enum_name   = nullptr;
    const char* d_smt2_name   = nullptr;
    KindAttribute d_attribute = KindAttribute::NONE;
  };

  /** Initialize kind information for given `kind`. */
  constexpr void init(Kind kind,
                      uint8_t num_children,
                      uint8_t num_indices,
                      const char* enum_name,
                      const char* smt2_name   = "",
                      KindAttribute attribute = NONE)
  {
    ++d_num_inited;
    d_info[static_cast<size_t>(kind)] = {
        num_children, num_indices, enum_name, smt2_name, attribute};
  }

  size_t d_num_inited = 0;
  std::array<KindData, static_cast<size_t>(Kind::NUM_KINDS)> d_info;
};

static constexpr KindInfo s_node_kind_info;
static_assert(s_node_kind_info.complete(), "KindInfo not fully initialized.");

/**
 * Print kind to stream.
 */
std::ostream& operator<<(std::ostream& out, Kind kind);

}  // namespace bzla::node
#endif
