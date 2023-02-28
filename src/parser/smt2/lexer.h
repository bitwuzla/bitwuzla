#ifndef BZLA_PARSER_SMT2_LEXER_H_INCLUDED
#define BZLA_PARSER_SMT2_LEXER_H_INCLUDED

#include <array>

#include "parser/smt2/token.h"

namespace bzla {
namespace parser::smt2 {

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
  const Coordinate& coo() const;
  const Coordinate& last_coo() const;

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

  Coordinate d_coo{1, 1};
  Coordinate d_next_coo{1, 1};
  Coordinate d_last_coo{1, 1};
  uint64_t d_last_coo_nl_col = 1;

  std::string d_token;

  bool d_saved         = false;
  int32_t d_saved_char = 0;

  std::string d_error;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
