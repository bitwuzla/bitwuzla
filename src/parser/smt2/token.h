#include <cstdint>
#include <iostream>

namespace bzla {
namespace parser::smt2 {

enum class TokenClass
{
  BITS = 6,
  SIZE = (1 << BITS),
  MASK = (SIZE - 1),

  MISC     = 0,
  CONSTANT = (SIZE << 0),
  RESERVED = (SIZE << 1),
  COMMAND  = (SIZE << 2),
  KEYWORD  = (SIZE << 3),
  CORE     = (SIZE << 4),
};

enum class Token
{
  INVALID   = 0 + static_cast<int32_t>(TokenClass::MISC),
  ENDOFFILE = 1 + static_cast<int32_t>(TokenClass::MISC),
  PARENT    = 2 + static_cast<int32_t>(TokenClass::MISC),
  LPAR      = 3 + static_cast<int32_t>(TokenClass::MISC),
  RPAR      = 4 + static_cast<int32_t>(TokenClass::MISC),
  SYMBOL    = 5 + static_cast<int32_t>(TokenClass::MISC),
  ATTRIBUTE = 6 + static_cast<int32_t>(TokenClass::MISC),
  EXP       = 7 + static_cast<int32_t>(TokenClass::MISC),
  /* <var_binding> */
  LETBIND = 8 + static_cast<int32_t>(TokenClass::MISC),
  /* (<var_binding>+) */
  PARLETBIND = 9 + static_cast<int32_t>(TokenClass::MISC),
  /* <sorted_var> */
  SORTED_VAR = 10 + static_cast<int32_t>(TokenClass::MISC),
  /* (<sorted_var>+) */
  SORTED_VARS = 11 + static_cast<int32_t>(TokenClass::MISC),

  /* ---------------------------------------------------------------------- */
  /* Constants                                                              */

  DECIMAL_CONSTANT     = 0 + static_cast<int32_t>(TokenClass::CONSTANT),
  HEXADECIMAL_CONSTANT = 1 + static_cast<int32_t>(TokenClass::CONSTANT),
  BINARY_CONSTANT      = 2 + static_cast<int32_t>(TokenClass::CONSTANT),
  STRING_CONSTANT      = 3 + static_cast<int32_t>(TokenClass::CONSTANT),
  REAL_CONSTANT        = 4 + static_cast<int32_t>(TokenClass::CONSTANT),

  /* ---------------------------------------------------------------------- */
  /* Reserved Words                                                         */

  BANG                      = 0 + static_cast<int32_t>(TokenClass::RESERVED),
  UNDERSCORE                = 1 + static_cast<int32_t>(TokenClass::RESERVED),
  AS                        = 2 + static_cast<int32_t>(TokenClass::RESERVED),
  BINARY_RESERVED_WORD      = 3 + static_cast<int32_t>(TokenClass::RESERVED),
  DECIMAL_RESERVED_WORD     = 4 + static_cast<int32_t>(TokenClass::RESERVED),
  EXISTS                    = 5 + static_cast<int32_t>(TokenClass::RESERVED),
  HEXADECIMAL_RESERVED_WORD = 6 + static_cast<int32_t>(TokenClass::RESERVED),
  FORALL                    = 7 + static_cast<int32_t>(TokenClass::RESERVED),
  LET                       = 8 + static_cast<int32_t>(TokenClass::RESERVED),
  NUMERAL_RESERVED_WORD     = 9 + static_cast<int32_t>(TokenClass::RESERVED),
  PAR                       = 10 + static_cast<int32_t>(TokenClass::RESERVED),
  STRING_RESERVED_WORD      = 11 + static_cast<int32_t>(TokenClass::RESERVED),
  // 'match' unsupported

  /* ---------------------------------------------------------------------- */
  /* Commands                                                               */

  ASSERT                = 0 + static_cast<int32_t>(TokenClass::COMMAND),
  CHECK_SAT             = 1 + static_cast<int32_t>(TokenClass::COMMAND),
  CHECK_SAT_ASSUMING    = 2 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_CONST         = 3 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_FUN           = 4 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_SORT          = 5 + static_cast<int32_t>(TokenClass::COMMAND),
  DEFINE_FUN            = 6 + static_cast<int32_t>(TokenClass::COMMAND),
  DEFINE_SORT           = 7 + static_cast<int32_t>(TokenClass::COMMAND),
  ECHO                  = 8 + static_cast<int32_t>(TokenClass::COMMAND),
  EXIT                  = 9 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_ASSERTIONS        = 10 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_ASSIGNMENT        = 11 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_INFO              = 12 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_MODEL             = 13 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_OPTION            = 14 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_PROOF             = 15 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_UNSAT_ASSUMPTIONS = 16 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_UNSAT_CORE        = 17 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_VALUE             = 18 + static_cast<int32_t>(TokenClass::COMMAND),
  POP                   = 19 + static_cast<int32_t>(TokenClass::COMMAND),
  PUSH                  = 20 + static_cast<int32_t>(TokenClass::COMMAND),
  RESET                 = 21 + static_cast<int32_t>(TokenClass::COMMAND),
  RESET_ASSERTIONS      = 22 + static_cast<int32_t>(TokenClass::COMMAND),
  SET_INFO              = 23 + static_cast<int32_t>(TokenClass::COMMAND),
  SET_LOGIC             = 24 + static_cast<int32_t>(TokenClass::COMMAND),
  SET_OPTION            = 25 + static_cast<int32_t>(TokenClass::COMMAND),
  // 'declare-datatype' unsupported
  // 'declare-datatypes' unsupported
  // 'define-fun-rec' unsupported

  /* ---------------------------------------------------------------------- */
  /* Keywords                                                               */

  ALL_STATISTICS              = 0 + static_cast<int32_t>(TokenClass::KEYWORD),
  AUTHORS                     = 1 + static_cast<int32_t>(TokenClass::KEYWORD),
  ASSERTION_STACK_LEVELS      = 2 + static_cast<int32_t>(TokenClass::KEYWORD),
  CATEGORY                    = 3 + static_cast<int32_t>(TokenClass::KEYWORD),
  CHAINABLE                   = 4 + static_cast<int32_t>(TokenClass::KEYWORD),
  DEFINITION                  = 5 + static_cast<int32_t>(TokenClass::KEYWORD),
  DIAG_OUTPUT_CHANNEL         = 6 + static_cast<int32_t>(TokenClass::KEYWORD),
  ERROR_BEHAVIOR              = 7 + static_cast<int32_t>(TokenClass::KEYWORD),
  EXTENSIONS                  = 8 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS                        = 9 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS_DESCRIPTION            = 10 + static_cast<int32_t>(TokenClass::KEYWORD),
  GLOBAL_DECLARATIONS         = 11 + static_cast<int32_t>(TokenClass::KEYWORD),
  INTERACTIVE_MODE            = 12 + static_cast<int32_t>(TokenClass::KEYWORD),
  LANGUAGE                    = 13 + static_cast<int32_t>(TokenClass::KEYWORD),
  LEFT_ASSOC                  = 14 + static_cast<int32_t>(TokenClass::KEYWORD),
  LICENSE                     = 15 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAME                        = 16 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAMED                       = 17 + static_cast<int32_t>(TokenClass::KEYWORD),
  NOTES                       = 18 + static_cast<int32_t>(TokenClass::KEYWORD),
  PATTERN                     = 19 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRINT_SUCCESS               = 20 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_ASSIGNMENTS         = 21 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_MODELS              = 22 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_PROOFS              = 23 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_ASSUMPTIONS   = 24 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_CORES         = 25 + static_cast<int32_t>(TokenClass::KEYWORD),
  RANDOM_SEED                 = 26 + static_cast<int32_t>(TokenClass::KEYWORD),
  REASON_UNKNOWN              = 27 + static_cast<int32_t>(TokenClass::KEYWORD),
  REGULAR_OUTPUT_CHANNEL      = 28 + static_cast<int32_t>(TokenClass::KEYWORD),
  REPRODUCIBLE_RESOURCE_LIMIT = 29 + static_cast<int32_t>(TokenClass::KEYWORD),
  RIGHT_ASSOC                 = 30 + static_cast<int32_t>(TokenClass::KEYWORD),
  SMTLIB_VERSION              = 31 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS                       = 32 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS_DESCRIPTION           = 33 + static_cast<int32_t>(TokenClass::KEYWORD),
  SOURCE                      = 34 + static_cast<int32_t>(TokenClass::KEYWORD),
  STATUS                      = 35 + static_cast<int32_t>(TokenClass::KEYWORD),
  THEORIES                    = 36 + static_cast<int32_t>(TokenClass::KEYWORD),
  VALUES                      = 37 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERBOSITY                   = 38 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERSION                     = 39 + static_cast<int32_t>(TokenClass::KEYWORD),

  /* ---------------------------------------------------------------------- */
  /* Core Symbols                                                           */

  AND      = 0 + static_cast<int32_t>(TokenClass::CORE),
  BOOL     = 1 + static_cast<int32_t>(TokenClass::CORE),
  DISTINCT = 2 + static_cast<int32_t>(TokenClass::CORE),
  EQUAL    = 3 + static_cast<int32_t>(TokenClass::CORE),
  FALSE    = 4 + static_cast<int32_t>(TokenClass::CORE),
  IMPLIES  = 5 + static_cast<int32_t>(TokenClass::CORE),
  ITE      = 6 + static_cast<int32_t>(TokenClass::CORE),
  NOT      = 7 + static_cast<int32_t>(TokenClass::CORE),
  OR       = 8 + static_cast<int32_t>(TokenClass::CORE),
  TRUE     = 9 + static_cast<int32_t>(TokenClass::CORE),
  XOR      = 10 + static_cast<int32_t>(TokenClass::CORE),
};

bool is_token_class(Token token, TokenClass tclass);

std::ostream& operator<<(std::ostream& out, Token token);

}  // namespace parser::smt2
}  // namespace bzla

namespace std {
std::string to_string(bzla::parser::smt2::Token token);
}
