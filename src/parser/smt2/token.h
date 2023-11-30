/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_SMT2_TOKEN_H_INCLUDED
#define BZLA_PARSER_SMT2_TOKEN_H_INCLUDED

#include <cstdint>
#include <iostream>

namespace bzla {
namespace parser::smt2 {

enum class TokenClass
{
  BITS = 8,
  SIZE = (1 << BITS),
  MASK = (SIZE - 1),

  MISC     = 0,
  VALUE    = (SIZE << 0),
  RESERVED = (SIZE << 1),
  COMMAND  = (SIZE << 2),
  KEYWORD  = (SIZE << 3),
  CORE     = (SIZE << 4),
  ARRAY    = (SIZE << 5),
  BV       = (SIZE << 6),
  FP       = (SIZE << 7),
  REALS    = (SIZE << 8),
};

enum class Token
{
  INVALID = static_cast<int32_t>(TokenClass::MISC),
  ENDOFFILE,
  PARENT,
  LPAR,
  RPAR,
  SYMBOL,
  ATTRIBUTE,
  OPEN,  // place holder for open item
  TERM,  // term argument
  FUN_APP,
  /* <var_binding> */
  LETBIND,
  /* (<var_binding>+) */
  PARLETBIND,
  /* <sorted_var> */
  SORTED_VAR,
  /* (<sorted_var>+) */
  SORTED_VARS,

  /* Values --------------------------------------------------------------- */

  DECIMAL_VALUE = static_cast<int32_t>(TokenClass::VALUE),
  HEXADECIMAL_VALUE,
  BINARY_VALUE,
  STRING_VALUE,
  REAL_VALUE,

  /* Reserved words ------------------------------------------------------- */

  BANG = static_cast<int32_t>(TokenClass::RESERVED),
  UNDERSCORE,
  AS,
  BINARY_RESERVED_WORD,
  DECIMAL_RESERVED_WORD,
  EXISTS,
  HEXADECIMAL_RESERVED_WORD,
  FORALL,
  LET,
  NUMERAL_RESERVED_WORD,
  PAR,
  STRING_RESERVED_WORD,
  // 'match' unsupported

  /* Commands ------------------------------------------------------------- */

  ASSERT = static_cast<int32_t>(TokenClass::COMMAND),
  CHECK_SAT,
  CHECK_SAT_ASSUMING,
  DECLARE_CONST,
  DECLARE_FUN,
  DECLARE_SORT,
  DEFINE_FUN,
  DEFINE_SORT,
  ECHO,
  EXIT,
  GET_ASSERTIONS,
  GET_ASSIGNMENT,
  GET_INFO,
  GET_MODEL,
  GET_OPTION,
  GET_PROOF,
  GET_UNSAT_ASSUMPTIONS,
  GET_UNSAT_CORE,
  GET_VALUE,
  POP,
  PUSH,
  RESET,
  RESET_ASSERTIONS,
  SET_INFO,
  SET_LOGIC,
  SET_OPTION,
  // 'declare-datatype' unsupported
  // 'declare-datatypes' unsupported
  // 'define-fun-rec' unsupported

  /* Keywords ------------------------------------------------------------- */

  ALL_STATISTICS = static_cast<int32_t>(TokenClass::KEYWORD),
  AUTHORS,
  ASSERTION_STACK_LEVELS,
  CATEGORY,
  CHAINABLE,
  DEFINITION,
  DIAG_OUTPUT_CHANNEL,
  ERROR_BEHAVIOR,
  EXTENSIONS,
  FUNS,
  FUNS_DESCRIPTION,
  GLOBAL_DECLARATIONS,
  INTERACTIVE_MODE,
  LANGUAGE,
  LEFT_ASSOC,
  LICENSE,
  NAME,
  NAMED,
  NOTES,
  PATTERN,
  PRINT_SUCCESS,
  PRODUCE_ASSIGNMENTS,
  PRODUCE_MODELS,
  PRODUCE_PROOFS,
  PRODUCE_UNSAT_ASSUMPTIONS,
  PRODUCE_UNSAT_CORES,
  RANDOM_SEED,
  REASON_UNKNOWN,
  REGULAR_OUTPUT_CHANNEL,
  REPR_RESOURCE_LIMIT,
  RIGHT_ASSOC,
  SMTLIB_VERSION,
  SORTS,
  SORTS_DESCRIPTION,
  SOURCE,
  STATUS,
  THEORIES,
  VALUES,
  VERBOSITY,
  VERSION,

  /* Core symbols --------------------------------------------------------- */

  AND = static_cast<int32_t>(TokenClass::CORE),
  BOOL,
  DISTINCT,
  EQUAL,
  FALSE,
  IMPLIES,
  ITE,
  NOT,
  OR,
  TRUE,
  XOR,

  /* Arrays --------------------------------------------------------------- */

  ARRAY = static_cast<int32_t>(TokenClass::ARRAY),
  ARRAY_SELECT,
  ARRAY_STORE,

  /* Bit-Vectors ---------------------------------------------------------- */

  BV_BITVEC = static_cast<int32_t>(TokenClass::BV),
  BV_VALUE,
  BV_ADD,
  BV_AND,
  BV_ASHR,
  BV_COMP,
  BV_CONCAT,
  BV_EXTRACT,
  BV_LSHR,
  BV_MUL,
  BV_NAND,
  BV_NEG,
  BV_NOR,
  BV_NOT,
  BV_OR,
  BV_REPEAT,
  BV_ROTATE_LEFT,
  BV_ROTATE_RIGHT,
  BV_SDIV,
  BV_SGE,
  BV_SGT,
  BV_SHL,
  BV_SIGN_EXTEND,
  BV_SLE,
  BV_SLT,
  BV_SMOD,
  BV_SREM,
  BV_SUB,
  BV_UDIV,
  BV_UGE,
  BV_UGT,
  BV_ULE,
  BV_ULT,
  BV_UREM,
  BV_XNOR,
  BV_XOR,
  BV_ZERO_EXTEND,
  // Bitwuzla extensions
  BV_DEC,
  BV_INC,
  BV_REDOR,
  BV_REDAND,
  BV_REDXOR,
  BV_NEGO,
  BV_SADDO,
  BV_UADDO,
  BV_SDIVO,
  BV_SMULO,
  BV_UMULO,
  BV_SSUBO,
  BV_USUBO,

  /* Floating-Point Arithmetic -------------------------------------------- */

  FP_FLOATINGPOINT = static_cast<int32_t>(TokenClass::FP),
  FP_FLOAT16,
  FP_FLOAT32,
  FP_FLOAT64,
  FP_FLOAT128,
  FP_ROUNDINGMODE,
  FP_RM_RNA,
  FP_RM_RNA_LONG,
  FP_RM_RNE,
  FP_RM_RNE_LONG,
  FP_RM_RTN,
  FP_RM_RTN_LONG,
  FP_RM_RTP,
  FP_RM_RTP_LONG,
  FP_RM_RTZ,
  FP_RM_RTZ_LONG,
  FP_ABS,
  FP_ADD,
  FP_DIV,
  FP_EQ,
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
  FP_NOTANUMBER,
  FP_NEG,
  FP_NEG_INF,
  FP_NEG_ZERO,
  FP_POS_INF,
  FP_POS_ZERO,
  FP_REM,
  FP_RTI,
  FP_SQRT,
  FP_SUB,
  FP_TO_FP,
  FP_TO_FP_UNSIGNED,
  FP_TO_SBV,
  FP_TO_UBV,

  /* Reals (for to_fp conversion) ----------------------------------------- */
  REAL_DIV = static_cast<int32_t>(TokenClass::REALS),
};

bool is_token_class(Token token, TokenClass tclass);

std::ostream& operator<<(std::ostream& out, Token token);

}  // namespace parser::smt2
}  // namespace bzla

namespace std {
std::string to_string(bzla::parser::smt2::Token token);
}

#endif
