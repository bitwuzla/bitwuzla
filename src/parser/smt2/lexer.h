#include <array>
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

std::ostream& operator<<(std::ostream& out, Token token);

class Lexer
{
 public:
  /** A coordinate in the input file. */
  struct Coordinate
  {
    uint64_t line;
    uint64_t col;
  };

  Lexer(std::istream* infile);
  Token next_token();
  const std::string& token() const;
  bool error() const;
  const std::string& error_msg() const;

 private:
  inline static const std::string s_printable_ascii_chars =
      "!\"#$%&'()*+,-./"
      "0123456789"
      ":;<=>?@"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "[\\]^_`"
      "abcdefghijklmnopqrstuvwxyz"
      "{|}~"
      " \t\r\n";
  inline static const std::string s_letter_chars =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "abcdefghijklmnopqrstuvwxyz";
  inline static const std::string s_decimal_digit_chars = "0123456789";
  inline static const std::string s_hexadecimal_digit_chars =
      "0123456789abcdefABCDEF";
  inline static const std::string s_extra_symbol_chars  = "+-/*=%?!.$_~&^<>@";
  inline static const std::string s_extra_keyword_chars = "+-/*=%?!.$_~&^<>@";

  enum class CharacterClass
  {
    DECIMAL_DIGIT     = (1 << 0),
    HEXADECIMAL_DIGIT = (1 << 1),
    STRING            = (1 << 2),
    SYMBOL            = (1 << 3),
    QUOTED_SYMBOL     = (1 << 4),
    KEYWORD           = (1 << 5),
  };

  void init_char_classes();
  uint32_t char_class(int32_t ch) const;
  bool is_char_class(int32_t ch, CharacterClass cclass) const;
  Token next_token_aux();
  int32_t next_char();
  void push_char(std::stringstream& token, int32_t ch);
  void save_char(int32_t ch);
  std::string err_char(int32_t ch) const;

  std::istream* d_infile = nullptr;

  std::array<uint32_t, 256> d_char_classes{};  // value-initialized to 0

  Coordinate d_coo{0, 0};
  Coordinate d_next_coo{0, 0};
  Coordinate d_last_coo{0, 0};
  uint64_t d_last_coo_nl_col = 0;

  std::string d_token;

  bool d_saved         = false;
  int32_t d_saved_char = 0;

  std::string d_error;
};

}  // namespace parser::smt2
}  // namespace bzla
