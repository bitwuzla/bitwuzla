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

  /* Values --------------------------------------------------------------- */

  DECIMAL_VALUE     = 0 + static_cast<int32_t>(TokenClass::VALUE),
  HEXADECIMAL_VALUE = 1 + static_cast<int32_t>(TokenClass::VALUE),
  BINARY_VALUE      = 2 + static_cast<int32_t>(TokenClass::VALUE),
  STRING_VALUE      = 3 + static_cast<int32_t>(TokenClass::VALUE),
  REAL_VALUE        = 4 + static_cast<int32_t>(TokenClass::VALUE),

  /* Reserved words ------------------------------------------------------- */

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

  /* Commands ------------------------------------------------------------- */

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

  /* Keywords ------------------------------------------------------------- */

  ALL_STATISTICS            = 0 + static_cast<int32_t>(TokenClass::KEYWORD),
  AUTHORS                   = 1 + static_cast<int32_t>(TokenClass::KEYWORD),
  ASSERTION_STACK_LEVELS    = 2 + static_cast<int32_t>(TokenClass::KEYWORD),
  CATEGORY                  = 3 + static_cast<int32_t>(TokenClass::KEYWORD),
  CHAINABLE                 = 4 + static_cast<int32_t>(TokenClass::KEYWORD),
  DEFINITION                = 5 + static_cast<int32_t>(TokenClass::KEYWORD),
  DIAG_OUTPUT_CHANNEL       = 6 + static_cast<int32_t>(TokenClass::KEYWORD),
  ERROR_BEHAVIOR            = 7 + static_cast<int32_t>(TokenClass::KEYWORD),
  EXTENSIONS                = 8 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS                      = 9 + static_cast<int32_t>(TokenClass::KEYWORD),
  FUNS_DESCRIPTION          = 10 + static_cast<int32_t>(TokenClass::KEYWORD),
  GLOBAL_DECLARATIONS       = 11 + static_cast<int32_t>(TokenClass::KEYWORD),
  INTERACTIVE_MODE          = 12 + static_cast<int32_t>(TokenClass::KEYWORD),
  LANGUAGE                  = 13 + static_cast<int32_t>(TokenClass::KEYWORD),
  LEFT_ASSOC                = 14 + static_cast<int32_t>(TokenClass::KEYWORD),
  LICENSE                   = 15 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAME                      = 16 + static_cast<int32_t>(TokenClass::KEYWORD),
  NAMED                     = 17 + static_cast<int32_t>(TokenClass::KEYWORD),
  NOTES                     = 18 + static_cast<int32_t>(TokenClass::KEYWORD),
  PATTERN                   = 19 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRINT_SUCCESS             = 20 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_ASSIGNMENTS       = 21 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_MODELS            = 22 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_PROOFS            = 23 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_ASSUMPTIONS = 24 + static_cast<int32_t>(TokenClass::KEYWORD),
  PRODUCE_UNSAT_CORES       = 25 + static_cast<int32_t>(TokenClass::KEYWORD),
  RANDOM_SEED               = 26 + static_cast<int32_t>(TokenClass::KEYWORD),
  REASON_UNKNOWN            = 27 + static_cast<int32_t>(TokenClass::KEYWORD),
  REGULAR_OUTPUT_CHANNEL    = 28 + static_cast<int32_t>(TokenClass::KEYWORD),
  REPR_RESOURCE_LIMIT       = 29 + static_cast<int32_t>(TokenClass::KEYWORD),
  RIGHT_ASSOC               = 30 + static_cast<int32_t>(TokenClass::KEYWORD),
  SMTLIB_VERSION            = 31 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS                     = 32 + static_cast<int32_t>(TokenClass::KEYWORD),
  SORTS_DESCRIPTION         = 33 + static_cast<int32_t>(TokenClass::KEYWORD),
  SOURCE                    = 34 + static_cast<int32_t>(TokenClass::KEYWORD),
  STATUS                    = 35 + static_cast<int32_t>(TokenClass::KEYWORD),
  THEORIES                  = 36 + static_cast<int32_t>(TokenClass::KEYWORD),
  VALUES                    = 37 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERBOSITY                 = 38 + static_cast<int32_t>(TokenClass::KEYWORD),
  VERSION                   = 39 + static_cast<int32_t>(TokenClass::KEYWORD),

  /* Core symbols --------------------------------------------------------- */

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

  /* Arrays --------------------------------------------------------------- */

  ARRAY        = 0 + static_cast<int32_t>(TokenClass::ARRAY),
  ARRAY_SELECT = 1 + static_cast<int32_t>(TokenClass::ARRAY),
  ARRAY_STORE  = 2 + static_cast<int32_t>(TokenClass::ARRAY),

  /* Bit-Vectors ---------------------------------------------------------- */

  BV_BITVEC       = 0 + static_cast<int32_t>(TokenClass::BV),
  BV_ADD          = 1 + static_cast<int32_t>(TokenClass::BV),
  BV_AND          = 2 + static_cast<int32_t>(TokenClass::BV),
  BV_ASHR         = 3 + static_cast<int32_t>(TokenClass::BV),
  BV_COMP         = 4 + static_cast<int32_t>(TokenClass::BV),
  BV_CONCAT       = 5 + static_cast<int32_t>(TokenClass::BV),
  BV_EXTRACT      = 6 + static_cast<int32_t>(TokenClass::BV),
  BV_LSHR         = 7 + static_cast<int32_t>(TokenClass::BV),
  BV_MUL          = 8 + static_cast<int32_t>(TokenClass::BV),
  BV_NAND         = 9 + static_cast<int32_t>(TokenClass::BV),
  BV_NEG          = 10 + static_cast<int32_t>(TokenClass::BV),
  BV_NOR          = 11 + static_cast<int32_t>(TokenClass::BV),
  BV_NOT          = 12 + static_cast<int32_t>(TokenClass::BV),
  BV_OR           = 13 + static_cast<int32_t>(TokenClass::BV),
  BV_REPEAT       = 14 + static_cast<int32_t>(TokenClass::BV),
  BV_ROTATE_LEFT  = 15 + static_cast<int32_t>(TokenClass::BV),
  BV_ROTATE_RIGHT = 16 + static_cast<int32_t>(TokenClass::BV),
  BV_SDIV         = 17 + static_cast<int32_t>(TokenClass::BV),
  BV_SGE          = 18 + static_cast<int32_t>(TokenClass::BV),
  BV_SGT          = 19 + static_cast<int32_t>(TokenClass::BV),
  BV_SHL          = 20 + static_cast<int32_t>(TokenClass::BV),
  BV_SIGN_EXTEND  = 21 + static_cast<int32_t>(TokenClass::BV),
  BV_SLE          = 22 + static_cast<int32_t>(TokenClass::BV),
  BV_SLT          = 23 + static_cast<int32_t>(TokenClass::BV),
  BV_SMOD         = 24 + static_cast<int32_t>(TokenClass::BV),
  BV_SREM         = 25 + static_cast<int32_t>(TokenClass::BV),
  BV_SUB          = 26 + static_cast<int32_t>(TokenClass::BV),
  BV_UDIV         = 27 + static_cast<int32_t>(TokenClass::BV),
  BV_UGE          = 28 + static_cast<int32_t>(TokenClass::BV),
  BV_UGT          = 29 + static_cast<int32_t>(TokenClass::BV),
  BV_ULE          = 30 + static_cast<int32_t>(TokenClass::BV),
  BV_ULT          = 31 + static_cast<int32_t>(TokenClass::BV),
  BV_UREM         = 32 + static_cast<int32_t>(TokenClass::BV),
  BV_XNOR         = 33 + static_cast<int32_t>(TokenClass::BV),
  BV_XOR          = 34 + static_cast<int32_t>(TokenClass::BV),
  BV_ZERO_EXTEND  = 35 + static_cast<int32_t>(TokenClass::BV),
  // Bitwuzla extensions
  BV_REDOR  = 36 + static_cast<int32_t>(TokenClass::BV),
  BV_REDAND = 37 + static_cast<int32_t>(TokenClass::BV),
  BV_REDXOR = 38 + static_cast<int32_t>(TokenClass::BV),
  BV_SADDO  = 39 + static_cast<int32_t>(TokenClass::BV),
  BV_UADDO  = 40 + static_cast<int32_t>(TokenClass::BV),
  BV_SDIVO  = 41 + static_cast<int32_t>(TokenClass::BV),
  BV_SMULO  = 42 + static_cast<int32_t>(TokenClass::BV),
  BV_UMULO  = 43 + static_cast<int32_t>(TokenClass::BV),
  BV_SSUBO  = 44 + static_cast<int32_t>(TokenClass::BV),
  BV_USUBO  = 45 + static_cast<int32_t>(TokenClass::BV),

  /* Floating-Point Arithmetic -------------------------------------------- */

  FP_FLOATINGPOINT  = 0 + static_cast<int32_t>(TokenClass::FP),
  FP_FLOAT16        = 1 + static_cast<int32_t>(TokenClass::FP),
  FP_FLOAT32        = 2 + static_cast<int32_t>(TokenClass::FP),
  FP_FLOAT64        = 3 + static_cast<int32_t>(TokenClass::FP),
  FP_FLOAT128       = 4 + static_cast<int32_t>(TokenClass::FP),
  FP_ROUNDINGMODE   = 5 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RNA         = 6 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RNA_LONG    = 7 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RNE         = 8 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RNE_LONG    = 9 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTN         = 10 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTN_LONG    = 11 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTP         = 12 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTP_LONG    = 13 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTZ         = 14 + static_cast<int32_t>(TokenClass::FP),
  FP_RM_RTZ_LONG    = 15 + static_cast<int32_t>(TokenClass::FP),
  FP_ABS            = 16 + static_cast<int32_t>(TokenClass::FP),
  FP_ADD            = 17 + static_cast<int32_t>(TokenClass::FP),
  FP_DIV            = 18 + static_cast<int32_t>(TokenClass::FP),
  FP_EQ             = 19 + static_cast<int32_t>(TokenClass::FP),
  FP_FMA            = 20 + static_cast<int32_t>(TokenClass::FP),
  FP_FP             = 21 + static_cast<int32_t>(TokenClass::FP),
  FP_GEQ            = 22 + static_cast<int32_t>(TokenClass::FP),
  FP_GT             = 23 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_INF         = 24 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_NAN         = 25 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_NEG         = 26 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_NORMAL      = 27 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_POS         = 28 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_SUBNORMAL   = 29 + static_cast<int32_t>(TokenClass::FP),
  FP_IS_ZERO        = 30 + static_cast<int32_t>(TokenClass::FP),
  FP_LEQ            = 31 + static_cast<int32_t>(TokenClass::FP),
  FP_LT             = 32 + static_cast<int32_t>(TokenClass::FP),
  FP_MAX            = 33 + static_cast<int32_t>(TokenClass::FP),
  FP_MIN            = 34 + static_cast<int32_t>(TokenClass::FP),
  FP_MUL            = 35 + static_cast<int32_t>(TokenClass::FP),
  FP_NAN            = 36 + static_cast<int32_t>(TokenClass::FP),
  FP_NEG            = 37 + static_cast<int32_t>(TokenClass::FP),
  FP_NEG_INF        = 38 + static_cast<int32_t>(TokenClass::FP),
  FP_NEG_ZERO       = 39 + static_cast<int32_t>(TokenClass::FP),
  FP_POS_INF        = 40 + static_cast<int32_t>(TokenClass::FP),
  FP_POS_ZERO       = 41 + static_cast<int32_t>(TokenClass::FP),
  FP_REM            = 42 + static_cast<int32_t>(TokenClass::FP),
  FP_RTI            = 43 + static_cast<int32_t>(TokenClass::FP),
  FP_SQRT           = 44 + static_cast<int32_t>(TokenClass::FP),
  FP_SUB            = 45 + static_cast<int32_t>(TokenClass::FP),
  FP_TO_FP          = 46 + static_cast<int32_t>(TokenClass::FP),
  FP_TO_FP_UNSIGNED = 47 + static_cast<int32_t>(TokenClass::FP),
  FP_TO_SBV         = 48 + static_cast<int32_t>(TokenClass::FP),
  FP_TO_UBV         = 49 + static_cast<int32_t>(TokenClass::FP),

  /* Reals (for to_fp conversion) ----------------------------------------- */
  REAL_DIV = 0 + static_cast<int32_t>(TokenClass::REALS),
};

bool is_token_class(Token token, TokenClass tclass);

std::ostream& operator<<(std::ostream& out, Token token);

}  // namespace parser::smt2
}  // namespace bzla

namespace std {
std::string to_string(bzla::parser::smt2::Token token);
}
