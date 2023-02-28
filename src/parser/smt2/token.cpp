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
  switch (token)
  {
    case Token::INVALID: out << "TOKEN_INVALID"; break;
    case Token::ENDOFFILE: out << "TOKEN_EOF"; break;
    case Token::PARENT: out << "TOKEN_PARENT"; break;
    case Token::LPAR: out << "TOKEN_LPAR"; break;
    case Token::RPAR: out << "TOKEN_RPAR"; break;
    case Token::SYMBOL: out << "TOKEN_SYMBOL"; break;
    case Token::ATTRIBUTE: out << "TOKEN_ATTRIBUTE"; break;
    case Token::EXP: out << "TOKEN_EXP"; break;
    case Token::LETBIND: out << "TOKEN_LETBIND"; break;
    case Token::PARLETBIND: out << "TOKEN_PARLETBIND"; break;
    case Token::SORTED_VAR: out << "TOKEN_SORTED_VAR"; break;
    case Token::SORTED_VARS: out << "TOKEN_SORTED_VARS"; break;
    case Token::DECIMAL_CONSTANT: out << "TOKEN_DECIMAL_CONSTANT"; break;
    case Token::HEXADECIMAL_CONSTANT:
      out << "TOKEN_HEXADECIMAL_CONSTANT";
      break;
    case Token::BINARY_CONSTANT: out << "TOKEN_BINARY_CONSTANT"; break;
    case Token::STRING_CONSTANT: out << "TOKEN_STRING_CONSTANT"; break;
    case Token::REAL_CONSTANT: out << "TOKEN_REAL_CONSTANT"; break;
    case Token::PAR: out << "TOKEN_PAR"; break;
    case Token::NUMERAL_RESERVED_WORD:
      out << "TOKEN_NUMERAL_RESERVED_WORD";
      break;
    case Token::DECIMAL_RESERVED_WORD:
      out << "TOKEN_DECIMAL_RESERVED_WORD";
      break;
    case Token::STRING_RESERVED_WORD:
      out << "TOKEN_STRING_RESERVED_WORD";
      break;
    case Token::UNDERSCORE: out << "TOKEN_UNDERSCORE"; break;
    case Token::BANG: out << "TOKEN_BANG"; break;
    case Token::AS: out << "TOKEN_AS"; break;
    case Token::LET: out << "TOKEN_LET"; break;
    case Token::FORALL: out << "TOKEN_FORALL"; break;
    case Token::EXISTS: out << "TOKEN_EXISTS"; break;
    case Token::SET_LOGIC: out << "TOKEN_SET_LOGIC"; break;
    case Token::SET_OPTION: out << "TOKEN_SET_OPTION"; break;
    case Token::SET_INFO: out << "TOKEN_SET_INFO"; break;
    case Token::DECLARE_SORT: out << "TOKEN_DECLARE_SORT"; break;
    case Token::DEFINE_SORT: out << "TOKEN_DEFINE_SORT"; break;
    case Token::DECLARE_FUN: out << "TOKEN_DECLARE_SORT"; break;
    case Token::DEFINE_FUN: out << "TOKEN_DEFINE_FUN"; break;
    case Token::DECLARE_CONST: out << "TOKEN_DECLARE_CONST"; break;
    case Token::PUSH: out << "TOKEN_PUSH"; break;
    case Token::POP: out << "TOKEN_POP"; break;
    case Token::ASSERT: out << "TOKEN_ASSERT"; break;
    case Token::CHECK_SAT: out << "TOKEN_CHECK_SAT"; break;
    case Token::CHECK_SAT_ASSUMING: out << "TOKEN_CHECK_SAT_ASSUMING"; break;
    case Token::GET_ASSERTIONS: out << "TOKEN_GET_ASSERTIONS"; break;
    case Token::GET_ASSIGNMENT: out << "TOKEN_GET_ASSIGNMENT"; break;
    case Token::GET_INFO: out << "TOKEN_GET_INFO"; break;
    case Token::GET_OPTION: out << "TOKEN_GET_OPTION"; break;
    case Token::GET_PROOF: out << "TOKEN_GET_PROOF"; break;
    case Token::GET_UNSAT_ASSUMPTIONS:
      out << "TOKEN_GET_UNSAT_ASSUMPTIONS";
      break;
    case Token::GET_UNSAT_CORE: out << "TOKEN_GET_UNSAT_CORE"; break;
    case Token::GET_VALUE: out << "TOKEN_GET_VALUE"; break;
    case Token::EXIT: out << "TOKEN_EXIT"; break;
    case Token::GET_MODEL: out << "TOKEN_GET_MODEL"; break;
    case Token::ECHO: out << "TOKEN_ECHO"; break;
    case Token::ALL_STATISTICS: out << "TOKEN_ALL_STATISTICS"; break;
    case Token::AUTHORS: out << "TOKEN_AUTHORS"; break;
    case Token::AXIOMS: out << "TOKEN_AXIOMS"; break;
    case Token::CHAINABLE: out << "TOKEN_CHAINABLE"; break;
    case Token::DEFINITION: out << "TOKEN_DEFINITION"; break;
    case Token::DIAG_OUTPUT_CHANNEL: out << "TOKEN_DIAG_OUTPUT_CHANNEL"; break;
    case Token::ERROR_BEHAVIOR: out << "TOKEN_ERROR_BEHAVIOR"; break;
    case Token::EXPAND_DEFINITIONS: out << "TOKEN_EXPAND_DEFINITIONS"; break;
    case Token::EXTENSIONS: out << "TOKEN_EXTENSIONS"; break;
    case Token::FUNS: out << "TOKEN_FUNS"; break;
    case Token::FUNS_DESCRIPTION: out << "TOKEN_FUNS_DESCRIPTION"; break;
    case Token::INTERACTIVE_MODE: out << "TOKEN_INTERACTIVE_MODE"; break;
    case Token::PRODUCE_ASSERTIONS: out << "TOKEN_PRODUCE_ASSERTIONS"; break;
    case Token::LANGUAGE: out << "TOKEN_LANGUAGE"; break;
    case Token::LEFT_ASSOC: out << "TOKEN_LEFT_ASSOC"; break;
    case Token::NAME: out << "TOKEN_NAME"; break;
    case Token::NAMED: out << "TOKEN_NAMED"; break;
    case Token::NOTES: out << "TOKEN_NOTES"; break;
    case Token::PRINT_SUCCESS: out << "TOKEN_PRINT_SUCCESS"; break;
    case Token::PRODUCE_ASSIGNMENTS: out << "TOKEN_PRODUCE_ASSIGNMENTS"; break;
    case Token::PRODUCE_MODELS: out << "TOKEN_PRODUCE_MODELS"; break;
    case Token::PRODUCE_PROOFS: out << "TOKEN_PRODUCE_PROOFS"; break;
    case Token::PRODUCE_UNSAT_ASSUMPTIONS:
      out << "TOKEN_PRODUCE_UNSAT_ASSUMPTIONS";
      break;
    case Token::PRODUCE_UNSAT_CORES: out << "TOKEN_PRODUCE_UNSAT_CORES"; break;
    case Token::RANDOM_SEED: out << "TOKEN_PRODUCE_RANDOM_SEED"; break;
    case Token::REASON_UNKNOWN: out << "TOKEN_REASON_UNKNOWN"; break;
    case Token::REGULAR_OUTPUT_CHANNEL:
      out << "TOKEN_REGULAR_OUTPUT_CHANNEL";
      break;
    case Token::RIGHT_ASSOC: out << "TOKEN_RIGHT_ASSOC"; break;
    case Token::SORTS: out << "TOKEN_SORTS"; break;
    case Token::SORTS_DESCRIPTION: out << "TOKEN_SORTS_DESCRIPTION"; break;
    case Token::STATUS: out << "TOKEN_STATUS"; break;
    case Token::THEORIES: out << "TOKEN_THEORIES"; break;
    case Token::VALUES: out << "TOKEN_VALUES"; break;
    case Token::VERBOSITY: out << "TOKEN_VERBOSITY"; break;
    case Token::VERSION: out << "TOKEN_VERSION"; break;
    case Token::GLOBAL_DECLARATIONS: out << "TOKEN_GLOBAL_DECLARATIONS"; break;
  }
  return out;
}

}  // namespace parser::smt2
}  // namespace bzla
