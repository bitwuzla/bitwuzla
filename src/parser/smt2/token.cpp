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
  switch (token)
  {
    case bzla::parser::smt2::Token::INVALID: return "<invalid token>";
    case bzla::parser::smt2::Token::ENDOFFILE: return "<eof token>";
    case bzla::parser::smt2::Token::PARENT: return "<parent token>";
    case bzla::parser::smt2::Token::LPAR: return "(";
    case bzla::parser::smt2::Token::RPAR: return ")";
    case bzla::parser::smt2::Token::SYMBOL: return "<symbol token>";
    case bzla::parser::smt2::Token::ATTRIBUTE: return "<attribute token>";
    case bzla::parser::smt2::Token::EXP: return "<expression token>";
    case bzla::parser::smt2::Token::LETBIND: return "<letbind token>";
    case bzla::parser::smt2::Token::PARLETBIND: return "<parletbind token>";
    case bzla::parser::smt2::Token::SORTED_VAR: return "<sorted_var token>";
    case bzla::parser::smt2::Token::SORTED_VARS: return "<sorted_vars token>";
    case bzla::parser::smt2::Token::DECIMAL_CONSTANT:
      return "<decimal constant token>";
    case bzla::parser::smt2::Token::HEXADECIMAL_CONSTANT:
      return "<hexadecimal constant token>";
    case bzla::parser::smt2::Token::BINARY_CONSTANT:
      return "<binary constant token>";
    case bzla::parser::smt2::Token::STRING_CONSTANT:
      return "<string constant token>";
    case bzla::parser::smt2::Token::REAL_CONSTANT:
      return "<real constant token>";
    // Reserved words
    case bzla::parser::smt2::Token::BANG: return "!";
    case bzla::parser::smt2::Token::UNDERSCORE: return "_";
    case bzla::parser::smt2::Token::AS: return "as";
    case bzla::parser::smt2::Token::BINARY_RESERVED_WORD: return "BINARY";
    case bzla::parser::smt2::Token::DECIMAL_RESERVED_WORD: return "DECIMAL";
    case bzla::parser::smt2::Token::EXISTS: return "exists";
    case bzla::parser::smt2::Token::FORALL: return "forall";
    case bzla::parser::smt2::Token::HEXADECIMAL_RESERVED_WORD:
      return "HEXADECIMAL";
    case bzla::parser::smt2::Token::LET: return "let";
    case bzla::parser::smt2::Token::NUMERAL_RESERVED_WORD: return "NUMERAL";
    case bzla::parser::smt2::Token::PAR: return "par";
    case bzla::parser::smt2::Token::STRING_RESERVED_WORD: return "STRING";
    // Commands
    case bzla::parser::smt2::Token::ASSERT: return "assert";
    case bzla::parser::smt2::Token::CHECK_SAT: return "check-sat";
    case bzla::parser::smt2::Token::CHECK_SAT_ASSUMING:
      return "check-sat-assuming";
    case bzla::parser::smt2::Token::DECLARE_CONST: return "declare-const";
    case bzla::parser::smt2::Token::DECLARE_FUN: return "declare-fun";
    case bzla::parser::smt2::Token::DECLARE_SORT: return "declare-sort";
    case bzla::parser::smt2::Token::DEFINE_FUN: return "define-fun";
    case bzla::parser::smt2::Token::DEFINE_SORT: return "define-sort";
    case bzla::parser::smt2::Token::ECHO: return "echo";
    case bzla::parser::smt2::Token::EXIT: return "exit";
    case bzla::parser::smt2::Token::GET_ASSERTIONS: return "get-assertions";
    case bzla::parser::smt2::Token::GET_ASSIGNMENT: return "get-assignment";
    case bzla::parser::smt2::Token::GET_INFO: return "get-info";
    case bzla::parser::smt2::Token::GET_OPTION: return "get-option";
    case bzla::parser::smt2::Token::GET_MODEL: return "get-model";
    case bzla::parser::smt2::Token::GET_PROOF: return "get-proof";
    case bzla::parser::smt2::Token::GET_UNSAT_ASSUMPTIONS:
      return "get-unsat-assumptions";
    case bzla::parser::smt2::Token::GET_UNSAT_CORE: return "get-unsat-core";
    case bzla::parser::smt2::Token::GET_VALUE: return "get-value";
    case bzla::parser::smt2::Token::POP: return "pop";
    case bzla::parser::smt2::Token::PUSH: return "push";
    case bzla::parser::smt2::Token::RESET: return "reset";
    case bzla::parser::smt2::Token::RESET_ASSERTIONS: return "reset-assertions";
    case bzla::parser::smt2::Token::SET_LOGIC: return "set-logic";
    case bzla::parser::smt2::Token::SET_INFO: return "set-info";
    case bzla::parser::smt2::Token::SET_OPTION: return "set-option";
    // Keywords
    case bzla::parser::smt2::Token::ALL_STATISTICS: return ":all-statistics";
    case bzla::parser::smt2::Token::ASSERTION_STACK_LEVELS:
      return ":assertion-stack-levels";
    case bzla::parser::smt2::Token::AUTHORS: return ":authors";
    case bzla::parser::smt2::Token::CATEGORY: return ":category";
    case bzla::parser::smt2::Token::CHAINABLE: return ":chainable";
    case bzla::parser::smt2::Token::DEFINITION: return ":definition";
    case bzla::parser::smt2::Token::DIAG_OUTPUT_CHANNEL:
      return ":diagnostic-output-channel";
    case bzla::parser::smt2::Token::ERROR_BEHAVIOR: return ":error-behavior";
    case bzla::parser::smt2::Token::EXTENSIONS: return ":extensions";
    case bzla::parser::smt2::Token::FUNS: return ":funs";
    case bzla::parser::smt2::Token::FUNS_DESCRIPTION:
      return ":funs-description";
    case bzla::parser::smt2::Token::INTERACTIVE_MODE:
      return ":interactive-mode";
    case bzla::parser::smt2::Token::LANGUAGE: return ":language";
    case bzla::parser::smt2::Token::LEFT_ASSOC: return ":left-assoc";
    case bzla::parser::smt2::Token::LICENSE: return ":license";
    case bzla::parser::smt2::Token::NAME: return ":name";
    case bzla::parser::smt2::Token::NAMED: return ":named";
    case bzla::parser::smt2::Token::NOTES: return ":notes";
    case bzla::parser::smt2::Token::PATTERN: return ":pattern";
    case bzla::parser::smt2::Token::PRINT_SUCCESS: return ":print-success";
    case bzla::parser::smt2::Token::PRODUCE_ASSIGNMENTS:
      return ":produce-assignments";
    case bzla::parser::smt2::Token::PRODUCE_MODELS: return ":produce-models";
    case bzla::parser::smt2::Token::PRODUCE_PROOFS: return ":produce-proofs";
    case bzla::parser::smt2::Token::PRODUCE_UNSAT_ASSUMPTIONS:
      return "TOKEN_PRODUCE_UNSAT_ASSUMPTIONS";
    case bzla::parser::smt2::Token::PRODUCE_UNSAT_CORES:
      return ":produce-unsat-cores";
    case bzla::parser::smt2::Token::RANDOM_SEED: return ":random-seed";
    case bzla::parser::smt2::Token::REASON_UNKNOWN: return ":reason-unknown";
    case bzla::parser::smt2::Token::REGULAR_OUTPUT_CHANNEL:
      return ":regular-output-channel";
    case bzla::parser::smt2::Token::REPRODUCIBLE_RESOURCE_LIMIT:
      return ":reproducible-resource-limit";
    case bzla::parser::smt2::Token::RIGHT_ASSOC: return ":right-assoc";
    case bzla::parser::smt2::Token::SMTLIB_VERSION: return ":smt-lib-version";
    case bzla::parser::smt2::Token::SORTS: return ":sorts";
    case bzla::parser::smt2::Token::SORTS_DESCRIPTION:
      return ":sorts-description";
    case bzla::parser::smt2::Token::STATUS: return ":status";
    case bzla::parser::smt2::Token::SOURCE: return ":source";
    case bzla::parser::smt2::Token::THEORIES: return ":theoreis";
    case bzla::parser::smt2::Token::VALUES: return ":values";
    case bzla::parser::smt2::Token::VERBOSITY: return ":verbosity";
    case bzla::parser::smt2::Token::VERSION: return ":version";
    case bzla::parser::smt2::Token::GLOBAL_DECLARATIONS:
      return ":global-declarations";
    // Core symbols
    case bzla::parser::smt2::Token::AND: return "and";
    case bzla::parser::smt2::Token::BOOL: return "Bool";
    case bzla::parser::smt2::Token::DISTINCT: return "distinct";
    case bzla::parser::smt2::Token::EQUAL: return "=";
    case bzla::parser::smt2::Token::FALSE: return "false";
    case bzla::parser::smt2::Token::IMPLIES: return "=>";
    case bzla::parser::smt2::Token::ITE: return "ite";
    case bzla::parser::smt2::Token::NOT: return "not";
    case bzla::parser::smt2::Token::OR: return "or";
    case bzla::parser::smt2::Token::TRUE: return "true";
    case bzla::parser::smt2::Token::XOR: return "xor";
  }
  return "<unsupported token>";
}

}  // namespace std
