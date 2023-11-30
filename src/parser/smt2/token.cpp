/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/smt2/token.h"

namespace bzla {
namespace parser::smt2 {

bool
is_token_class(Token token, TokenClass tclass)
{
  return static_cast<uint32_t>(token) & static_cast<uint32_t>(tclass);
}

std::ostream&
operator<<(std::ostream& out, Token token)
{
  out << std::to_string(token);
  return out;
}

}  // namespace parser::smt2
}  // namespace bzla

namespace std {

std::string
to_string(bzla::parser::smt2::Token token)
{
  using namespace bzla::parser::smt2;
  switch (token)
  {
    case Token::INVALID: return "<invalid token>";
    case Token::ENDOFFILE: return "<eof token>";
    case Token::PARENT: return "<parent token>";
    case Token::SYMBOL: return "<symbol token>";
    case Token::ATTRIBUTE: return "<attribute token>";
    case Token::OPEN: return "<open item token>";
    case Token::TERM: return "<term token>";
    case Token::FUN_APP: return "<function application token>";
    case Token::LETBIND: return "<letbind token>";
    case Token::PARLETBIND: return "<parletbind token>";
    case Token::SORTED_VAR: return "<sorted_var token>";
    case Token::SORTED_VARS: return "<sorted_vars token>";

    case Token::DECIMAL_VALUE: return "<decimal value token>";
    case Token::HEXADECIMAL_VALUE: return "<hexadecimal value token>";
    case Token::BINARY_VALUE: return "<binary value token>";
    case Token::STRING_VALUE: return "<string value token>";
    case Token::REAL_VALUE: return "<real value token>";

    case Token::LPAR: return "(";
    case Token::RPAR: return ")";

    // Reserved words
    case Token::BANG: return "!";
    case Token::UNDERSCORE: return "_";
    case Token::AS: return "as";
    case Token::BINARY_RESERVED_WORD: return "BINARY";
    case Token::DECIMAL_RESERVED_WORD: return "DECIMAL";
    case Token::EXISTS: return "exists";
    case Token::FORALL: return "forall";
    case Token::HEXADECIMAL_RESERVED_WORD: return "HEXADECIMAL";
    case Token::LET: return "let";
    case Token::NUMERAL_RESERVED_WORD: return "NUMERAL";
    case Token::PAR: return "par";
    case Token::STRING_RESERVED_WORD: return "STRING";
    // Commands
    case Token::ASSERT: return "assert";
    case Token::CHECK_SAT: return "check-sat";
    case Token::CHECK_SAT_ASSUMING: return "check-sat-assuming";
    case Token::DECLARE_CONST: return "declare-const";
    case Token::DECLARE_FUN: return "declare-fun";
    case Token::DECLARE_SORT: return "declare-sort";
    case Token::DEFINE_FUN: return "define-fun";
    case Token::DEFINE_SORT: return "define-sort";
    case Token::ECHO: return "echo";
    case Token::EXIT: return "exit";
    case Token::GET_ASSERTIONS: return "get-assertions";
    case Token::GET_ASSIGNMENT: return "get-assignment";
    case Token::GET_INFO: return "get-info";
    case Token::GET_OPTION: return "get-option";
    case Token::GET_MODEL: return "get-model";
    case Token::GET_PROOF: return "get-proof";
    case Token::GET_UNSAT_ASSUMPTIONS: return "get-unsat-assumptions";
    case Token::GET_UNSAT_CORE: return "get-unsat-core";
    case Token::GET_VALUE: return "get-value";
    case Token::POP: return "pop";
    case Token::PUSH: return "push";
    case Token::RESET: return "reset";
    case Token::RESET_ASSERTIONS: return "reset-assertions";
    case Token::SET_LOGIC: return "set-logic";
    case Token::SET_INFO: return "set-info";
    case Token::SET_OPTION: return "set-option";
    // Keywords
    case Token::ALL_STATISTICS: return ":all-statistics";
    case Token::ASSERTION_STACK_LEVELS: return ":assertion-stack-levels";
    case Token::AUTHORS: return ":authors";
    case Token::CATEGORY: return ":category";
    case Token::CHAINABLE: return ":chainable";
    case Token::DEFINITION: return ":definition";
    case Token::DIAG_OUTPUT_CHANNEL: return ":diagnostic-output-channel";
    case Token::ERROR_BEHAVIOR: return ":error-behavior";
    case Token::EXTENSIONS: return ":extensions";
    case Token::FUNS: return ":funs";
    case Token::FUNS_DESCRIPTION: return ":funs-description";
    case Token::INTERACTIVE_MODE: return ":interactive-mode";
    case Token::LANGUAGE: return ":language";
    case Token::LEFT_ASSOC: return ":left-assoc";
    case Token::LICENSE: return ":license";
    case Token::NAME: return ":name";
    case Token::NAMED: return ":named";
    case Token::NOTES: return ":notes";
    case Token::PATTERN: return ":pattern";
    case Token::PRINT_SUCCESS: return ":print-success";
    case Token::PRODUCE_ASSIGNMENTS: return ":produce-assignments";
    case Token::PRODUCE_MODELS: return ":produce-models";
    case Token::PRODUCE_PROOFS: return ":produce-proofs";
    case Token::PRODUCE_UNSAT_ASSUMPTIONS: return ":produce-unsat-assumptions";
    case Token::PRODUCE_UNSAT_CORES: return ":produce-unsat-cores";
    case Token::RANDOM_SEED: return ":random-seed";
    case Token::REASON_UNKNOWN: return ":reason-unknown";
    case Token::REGULAR_OUTPUT_CHANNEL: return ":regular-output-channel";
    case Token::REPR_RESOURCE_LIMIT: return ":reproducible-resource-limit";
    case Token::RIGHT_ASSOC: return ":right-assoc";
    case Token::SMTLIB_VERSION: return ":smt-lib-version";
    case Token::SORTS: return ":sorts";
    case Token::SORTS_DESCRIPTION: return ":sorts-description";
    case Token::STATUS: return ":status";
    case Token::SOURCE: return ":source";
    case Token::THEORIES: return ":theories";
    case Token::VALUES: return ":values";
    case Token::VERBOSITY: return ":verbosity";
    case Token::VERSION: return ":version";
    case Token::GLOBAL_DECLARATIONS: return ":global-declarations";
    // Core symbols
    case Token::AND: return "and";
    case Token::BOOL: return "Bool";
    case Token::DISTINCT: return "distinct";
    case Token::EQUAL: return "=";
    case Token::FALSE: return "false";
    case Token::IMPLIES: return "=>";
    case Token::ITE: return "ite";
    case Token::NOT: return "not";
    case Token::OR: return "or";
    case Token::TRUE: return "true";
    case Token::XOR: return "xor";
    // Arrays
    case Token::ARRAY: return "Array";
    case Token::ARRAY_SELECT: return "select";
    case Token::ARRAY_STORE: return "store";
    // BV
    case Token::BV_BITVEC: return "BitVec";
    case Token::BV_VALUE: return "<bvX token>";
    case Token::BV_ADD: return "bvadd";
    case Token::BV_AND: return "bvand";
    case Token::BV_ASHR: return "bvashr";
    case Token::BV_COMP: return "bvcomp";
    case Token::BV_CONCAT: return "concat";
    case Token::BV_EXTRACT: return "extract";
    case Token::BV_LSHR: return "bvlshr";
    case Token::BV_MUL: return "bvmul";
    case Token::BV_NAND: return "bvnand";
    case Token::BV_NEG: return "bvneg";
    case Token::BV_NOR: return "bvnor";
    case Token::BV_NOT: return "bvnot";
    case Token::BV_OR: return "bvor";
    case Token::BV_REPEAT: return "repeat";
    case Token::BV_ROTATE_LEFT: return "rotate_left";
    case Token::BV_ROTATE_RIGHT: return "rotate_right";
    case Token::BV_SDIV: return "bvsdiv";
    case Token::BV_SGE: return "bvsge";
    case Token::BV_SGT: return "bvsgt";
    case Token::BV_SHL: return "bvshl";
    case Token::BV_SIGN_EXTEND: return "sign_extend";
    case Token::BV_SLE: return "bvsle";
    case Token::BV_SLT: return "bvslt";
    case Token::BV_SMOD: return "bvsmod";
    case Token::BV_SREM: return "bvsrem";
    case Token::BV_SUB: return "bvsub";
    case Token::BV_UDIV: return "bvudiv";
    case Token::BV_UGE: return "bvuge";
    case Token::BV_UGT: return "bvugt";
    case Token::BV_ULE: return "bvule";
    case Token::BV_ULT: return "bvult";
    case Token::BV_UREM: return "bvurem";
    case Token::BV_XNOR: return "bvxnor";
    case Token::BV_XOR: return "bvxor";
    case Token::BV_ZERO_EXTEND: return "zero_extend";
    // Bitwuzla extensions
    case Token::BV_DEC: return "bvdec";
    case Token::BV_INC: return "bvinc";
    case Token::BV_REDOR: return "bvredor";
    case Token::BV_REDAND: return "bvredand";
    case Token::BV_REDXOR: return "bvredxor";
    case Token::BV_NEGO: return "bvnego";
    case Token::BV_SADDO: return "bvsaddo";
    case Token::BV_UADDO: return "bvuaddo";
    case Token::BV_SDIVO: return "bvsdivo";
    case Token::BV_SMULO: return "bvsmulo";
    case Token::BV_UMULO: return "bvumulo";
    case Token::BV_SSUBO: return "bvssubo";
    case Token::BV_USUBO: return "bvusubo";
    // FP
    case Token::FP_FLOATINGPOINT: return "FloatingPoint";
    case Token::FP_FLOAT16: return "Float16";
    case Token::FP_FLOAT32: return "Float32";
    case Token::FP_FLOAT64: return "Float64";
    case Token::FP_FLOAT128: return "Float128";
    case Token::FP_ROUNDINGMODE: return "RoundingMode";
    case Token::FP_RM_RNA: return "RNA";
    case Token::FP_RM_RNA_LONG: return "roundNearestTiesToAway";
    case Token::FP_RM_RNE: return "RNE";
    case Token::FP_RM_RNE_LONG: return "roundNearestTiesToEven";
    case Token::FP_RM_RTN: return "RTN";
    case Token::FP_RM_RTN_LONG: return "roundTowardNegative";
    case Token::FP_RM_RTP: return "RTP";
    case Token::FP_RM_RTP_LONG: return "roundTowardPositive";
    case Token::FP_RM_RTZ: return "RTZ";
    case Token::FP_RM_RTZ_LONG: return "roundTowardZero";
    case Token::FP_ABS: return "fp.abs";
    case Token::FP_ADD: return "fp.add";
    case Token::FP_DIV: return "fp.div";
    case Token::FP_EQ: return "fp.eq";
    case Token::FP_FMA: return "fp.fma";
    case Token::FP_FP: return "fp";
    case Token::FP_GEQ: return "fp.geq";
    case Token::FP_GT: return "fp.gt";
    case Token::FP_IS_INF: return "fp.isInfinite";
    case Token::FP_IS_NAN: return "fp.isNaN";
    case Token::FP_IS_NEG: return "fp.isNegative";
    case Token::FP_IS_NORMAL: return "fp.isNormal";
    case Token::FP_IS_POS: return "fp.isPositive";
    case Token::FP_IS_SUBNORMAL: return "fp.isSubnormal";
    case Token::FP_IS_ZERO: return "fp.isZero";
    case Token::FP_LEQ: return "fp.leq";
    case Token::FP_LT: return "fp.lt";
    case Token::FP_MAX: return "fp.max";
    case Token::FP_MIN: return "fp.min";
    case Token::FP_MUL: return "fp.mul";
    case Token::FP_NOTANUMBER: return "NaN";
    case Token::FP_NEG: return "fp.neg";
    case Token::FP_NEG_INF: return "-oo";
    case Token::FP_NEG_ZERO: return "-zero";
    case Token::FP_POS_INF: return "+oo";
    case Token::FP_POS_ZERO: return "+zero";
    case Token::FP_REM: return "fp.rem";
    case Token::FP_RTI: return "fp.roundToIntegral";
    case Token::FP_SQRT: return "fp.sqrt";
    case Token::FP_SUB: return "fp.sub";
    case Token::FP_TO_FP: return "to_fp";
    case Token::FP_TO_FP_UNSIGNED: return "to_fp_unsigned";
    case Token::FP_TO_SBV: return "fp.to_sbv";
    case Token::FP_TO_UBV: return "fp.to_ubv";
    // Reals
    case Token::REAL_DIV: return "/";
  }
  return "<unsupported token>";
}

}  // namespace std
