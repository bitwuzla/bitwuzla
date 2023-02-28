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

  PAR                   = 0 + static_cast<int32_t>(TokenClass::RESERVED),
  NUMERAL_RESERVED_WORD = 1 + static_cast<int32_t>(TokenClass::RESERVED),
  DECIMAL_RESERVED_WORD = 2 + static_cast<int32_t>(TokenClass::RESERVED),
  STRING_RESERVED_WORD  = 3 + static_cast<int32_t>(TokenClass::RESERVED),
  UNDERSCORE            = 4 + static_cast<int32_t>(TokenClass::RESERVED),
  BANG                  = 5 + static_cast<int32_t>(TokenClass::RESERVED),
  AS                    = 6 + static_cast<int32_t>(TokenClass::RESERVED),
  LET                   = 7 + static_cast<int32_t>(TokenClass::RESERVED),
  FORALL                = 8 + static_cast<int32_t>(TokenClass::RESERVED),
  EXISTS                = 9 + static_cast<int32_t>(TokenClass::RESERVED),

  /* ---------------------------------------------------------------------- */
  /* Commands                                                               */

  SET_LOGIC             = 0 + static_cast<int32_t>(TokenClass::COMMAND),
  SET_OPTION            = 1 + static_cast<int32_t>(TokenClass::COMMAND),
  SET_INFO              = 2 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_SORT          = 3 + static_cast<int32_t>(TokenClass::COMMAND),
  DEFINE_SORT           = 4 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_FUN           = 5 + static_cast<int32_t>(TokenClass::COMMAND),
  DEFINE_FUN            = 6 + static_cast<int32_t>(TokenClass::COMMAND),
  DECLARE_CONST         = 7 + static_cast<int32_t>(TokenClass::COMMAND),
  PUSH                  = 8 + static_cast<int32_t>(TokenClass::COMMAND),
  POP                   = 9 + static_cast<int32_t>(TokenClass::COMMAND),
  ASSERT                = 10 + static_cast<int32_t>(TokenClass::COMMAND),
  CHECK_SAT             = 11 + static_cast<int32_t>(TokenClass::COMMAND),
  CHECK_SAT_ASSUMING    = 12 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_ASSERTIONS        = 13 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_ASSIGNMENT        = 14 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_INFO              = 15 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_OPTION            = 16 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_PROOF             = 17 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_UNSAT_ASSUMPTIONS = 18 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_UNSAT_CORE        = 19 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_VALUE             = 20 + static_cast<int32_t>(TokenClass::COMMAND),
  EXIT                  = 21 + static_cast<int32_t>(TokenClass::COMMAND),
  GET_MODEL             = 22 + static_cast<int32_t>(TokenClass::COMMAND),
  ECHO                  = 23 + static_cast<int32_t>(TokenClass::COMMAND),

  /* ---------------------------------------------------------------------- */
  /* Keywords                                                               */

  ALL_STATISTICS            = 0 + static_cast<int32_t>(TokenClass::KEYWORD),
  AUTHORS                   = 1 + static_cast<int32_t>(TokenClass::KEYWORD),
  AXIOMS                    = 2 + static_cast<int32_t>(TokenClass::KEYWORD),
  CHAINABLE                 = 3 + static_cast<int32_t>(TokenClass::KEYWORD),
  DEFINITION                = 4 + static_cast<int32_t>(TokenClass::KEYWORD),
  DIAG_OUTPUT_CHANNEL       = 5 + static_cast<int32_t>(TokenClass::KEYWORD),
  ERROR_BEHAVIOR            = 6 + static_cast<int32_t>(TokenClass::KEYWORD),
  EXPAND_DEFINITIONS        = 7 + static_cast<int32_t>(TokenClass::KEYWORD),
  EXTENSIONS                = 8 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS                      = 9 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS_DESCRIPTION          = 10 + static_cast<int32_t>(TokenClass::KEYWORD),
  INTERACTIVE_MODE          = 11 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_ASSERTIONS        = 12 + static_cast<int32_t>(TokenClass::KEYWORD),
  LANGUAGE                  = 13 + static_cast<int32_t>(TokenClass::KEYWORD),
  LEFT_ASSOC                = 14 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAME                      = 15 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAMED                     = 16 + static_cast<int32_t>(TokenClass::KEYWORD),
  NOTES                     = 17 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRINT_SUCCESS             = 18 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_ASSIGNMENTS       = 19 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_MODELS            = 20 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_PROOFS            = 21 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_ASSUMPTIONS = 22 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_CORES       = 23 + static_cast<int32_t>(TokenClass::KEYWORD),
  RANDOM_SEED               = 24 + static_cast<int32_t>(TokenClass::KEYWORD),
  REASON_UNKNOWN            = 25 + static_cast<int32_t>(TokenClass::KEYWORD),
  REGULAR_OUTPUT_CHANNEL    = 26 + static_cast<int32_t>(TokenClass::KEYWORD),
  RIGHT_ASSOC               = 27 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS                     = 28 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS_DESCRIPTION         = 29 + static_cast<int32_t>(TokenClass::KEYWORD),
  STATUS                    = 30 + static_cast<int32_t>(TokenClass::KEYWORD),
  THEORIES                  = 31 + static_cast<int32_t>(TokenClass::KEYWORD),
  VALUES                    = 32 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERBOSITY                 = 33 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERSION                   = 34 + static_cast<int32_t>(TokenClass::KEYWORD),
  GLOBAL_DECLARATIONS       = 35 + static_cast<int32_t>(TokenClass::KEYWORD),
};

bool is_token_class(Token token, TokenClass tclass);

std::ostream& operator<<(std::ostream& out, Token token);

}  // namespace parser::smt2
}  // namespace bzla
