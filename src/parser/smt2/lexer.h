#ifndef BZLA_PARSER_SMT2_LEXER_H_INCLUDED
#define BZLA_PARSER_SMT2_LEXER_H_INCLUDED

#include <array>
#include <cassert>
#include <cstring>
#include <vector>

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

  Lexer(FILE* infile);
  Token next_token();
  bool has_token() const { return !d_token.empty(); }
  const char* token() const { return d_token.data(); }
  bool error() const;
  const std::string& error_msg() const;
  const Coordinate& coo() const { return d_coo; }
  const Coordinate& last_coo() const { return d_last_coo; }

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

  // implemented here for inlining
  bool is_char_class(int32_t ch, CharacterClass cclass) const
  {
    if (ch < 0 || ch >= 256)
    {
      return false;
    }

    return d_char_classes[static_cast<uint8_t>(ch)]
           & static_cast<uint8_t>(cclass);
  }

  Token next_token_aux();

  // implemented here for inlining
  int32_t next_char()
  {
    int32_t res;
    if (d_saved)
    {
      res     = d_saved_char;
      d_saved = false;
    }
    else
    {
      res = std::getc(d_infile);
    }
    if (res == '\n')
    {
      d_next_coo.line += 1;
      assert(d_next_coo.line > 0);
      d_last_coo_nl_col = d_next_coo.col;
      d_next_coo.col    = 1;
    }
    else
    {
      d_next_coo.col += 1;
      assert(d_next_coo.col > 0);
    }
    return res;
  }

  // implemented here for inlining
  void push_char(int32_t ch)
  {
    assert(ch != EOF);
    assert(ch >= 0 && ch < 256);
    d_token.push_back(static_cast<char>(ch));
  }

  // implemented here for inlining
  void save_char(int32_t ch)
  {
    assert(!d_saved);
    d_saved      = true;
    d_saved_char = ch;
    if (ch == '\n')
    {
      assert(d_next_coo.line > 1);
      d_next_coo.line -= 1;
      d_next_coo.col = d_last_coo_nl_col;
    }
    else
    {
      assert(d_next_coo.col > 1);
      d_next_coo.col -= 1;
    }
  }

  // implemented here for inlining
  bool is_printable(int32_t ch) const
  {
    return s_printable_ascii_chars.find(ch) != std::string::npos;
  }

  std::string err_char(int32_t ch) const;

  Token error(int32_t ch, const std::string& error_msg);

  FILE* d_infile = nullptr;

  std::array<uint8_t, 256> d_char_classes{};  // value-initialized to 0

  Coordinate d_coo{1, 1};
  Coordinate d_next_coo{1, 1};
  Coordinate d_last_coo{1, 1};
  uint64_t d_last_coo_nl_col = 1;

  std::vector<char> d_token;

  bool d_saved         = false;
  int32_t d_saved_char = 0;

  std::string d_error;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
