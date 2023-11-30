/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

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
  BV_NEGO,
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
 * Print kind to stream.
 */
std::ostream& operator<<(std::ostream& out, Kind kind);

}  // namespace bzla::node
#endif
