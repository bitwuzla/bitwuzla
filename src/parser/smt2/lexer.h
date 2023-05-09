#ifndef BZLA_PARSER_SMT2_LEXER_H_INCLUDED
#define BZLA_PARSER_SMT2_LEXER_H_INCLUDED

#include <array>
#include <cassert>
#include <cstring>
#include <sstream>
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

  /**
   * Constructor.
   * @param infile The input file.
   */
  Lexer(FILE* infile);
  /** @return The next token. */
  Token next_token();
  /**
   * @return True if lexer parsed a token that has a non-unique string
   *         representation (e.g., symbols, attributes, binary values, etc.).
   *         This string representation can then be queried via token().
   */
  bool has_token() const { return !d_token.empty(); }
  /**
   * Get a string representation of the last parsed token. Empty if
   * !has_token(), i.e., if token has a unique string representation (e.g.,
   * left/right parenthesis, underscore, etc.).
   * @return The string representation of the token.
   */
  const char* token() const { return d_token.data(); }
  /** @return True if lexer encountered an error. */
  bool error() const;
  /** @return The error message, empty if !error(). */
  const std::string& error_msg() const;
  /** @return The current coordinate in the input file. */
  const Coordinate& coo() const { return d_coo; }
  /**
   * @return The coordinate of the last token (the token previous to the
   *         current one).
   */
  const Coordinate& last_coo() const { return d_last_coo; }

 private:
  /** The size of the chunks to be read into the input file buffer d_buffer. */
  inline static constexpr size_t s_buf_size = 1024;

  /** The set of legal printable characters. */
  inline static const std::string s_printable_ascii_chars =
      "!\"#$%&'()*+,-./"
      "0123456789"
      ":;<=>?@"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "[\\]^_`"
      "abcdefghijklmnopqrstuvwxyz"
      "{|}~"
      " \t\r\n";
  /** The set of characters that are letters. */
  inline static const std::string s_letter_chars =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "abcdefghijklmnopqrstuvwxyz";
  /** The set of decimal digits. */
  inline static const std::string s_decimal_digit_chars = "0123456789";
  /** The set of hexadecimal digits. */
  inline static const std::string s_hexadecimal_digit_chars =
      "0123456789abcdefABCDEF";
  /** The set of non-letter/non-digit characters that may occur in symbols. */
  inline static const std::string s_extra_symbol_chars  = "+-/*=%?!.$_~&^<>@";
  /** The set of non-letter/non-digit characters that may occur in keywords. */
  inline static const std::string s_extra_keyword_chars = "+-/*=%?!.$_~&^<>@";

  /** The classification of a character according to where it may appear. */
  enum class CharacterClass
  {
    DECIMAL_DIGIT     = (1 << 0),
    HEXADECIMAL_DIGIT = (1 << 1),
    STRING            = (1 << 2),
    SYMBOL            = (1 << 3),
    QUOTED_SYMBOL     = (1 << 4),
    KEYWORD           = (1 << 5),
  };

  /** Initialize the character classes. */
  void init_char_classes();

  /**
   * @return True if given character belongs to the given character class.
   * @note implemented here for inlining
   */
  bool is_char_class(int32_t ch, CharacterClass cclass) const
  {
    if (ch < 0 || ch >= 256)
    {
      return false;
    }
    return d_char_classes[static_cast<uint8_t>(ch)]
           & static_cast<uint8_t>(cclass);
  }

  /** Helper for next_token(). */
  Token next_token_aux();

  /**
   * @return The next character in the input file.
   * @note implemented here for inlining
   */
  int32_t next_char()
  {
    if (d_buf_idx == s_buf_size)
    {
      assert(!d_saved);
      size_t cnt =
          std::fread(d_buffer.data(), sizeof(char), s_buf_size, d_infile);
      if (std::feof(d_infile))
      {
        d_buffer[cnt] = EOF;
      }
      d_buf_idx = 0;
    }
    d_saved     = false;
    int32_t res = d_buffer[d_buf_idx++];
    if (res == '\n')
    {
      d_cur_coo.line += 1;
      assert(d_cur_coo.line > 0);
      d_last_coo_nl_col = d_cur_coo.col;
      d_cur_coo.col     = 1;
    }
    else
    {
      d_cur_coo.col += 1;
      assert(d_cur_coo.col > 0);
    }
    return res;
  }

  /**
   * Push given character onto the token stack.
   * @note implemented here for inlining
   */
  void push_char(int32_t ch)
  {
    assert(ch != EOF);
    assert(ch >= 0 && ch < 256);
    d_token.push_back(static_cast<char>(ch));
  }

  /**
   * Store given character as a look ahead.
   * @note implemented here for inlining
   */
  void save_char(int32_t ch)
  {
    assert(!d_saved);
    assert(d_buf_idx > 0);
    d_saved = true;
    d_buf_idx -= 1;
    assert(d_buffer[d_buf_idx] == ch);
    if (ch == '\n')
    {
      assert(d_cur_coo.line > 1);
      d_cur_coo.line -= 1;
      d_cur_coo.col = d_last_coo_nl_col;
    }
    else
    {
      assert(d_cur_coo.col > 1);
      d_cur_coo.col -= 1;
    }
  }

  /**
   * @return True if given character is a printable character.
   * @note implemented here for inlining
   */
  bool is_printable(int32_t ch) const
  {
    return s_printable_ascii_chars.find(ch) != std::string::npos;
  }

  /**
   * Helper for error().
   * @return String "character '<ch>'".
   */
  std::string err_char(int32_t ch) const;

  /**
   * Helper for error handling.
   * Compiles all data required for aborting on error (coordinate, message).
   * @param ch Character, saved as look ahead.
   * @param error_msg The error message to set.
   * @return The invalid token.
   */
  Token error(int32_t ch, const std::string& error_msg);

  /** The input file. */
  FILE* d_infile = nullptr;
  /** The character classes. */
  std::array<uint8_t, 256> d_char_classes{};  // value-initialized to 0
  /** The coordinate of the current token. */
  Coordinate d_coo{1, 1};
  /** The current coordinate in the input file. */
  Coordinate d_cur_coo{1, 1};
  /** The coordinate of the last token. */
  Coordinate d_last_coo{1, 1};
  /** The column of the last new line. */
  uint64_t d_last_coo_nl_col = 1;

  /**
   * The string representation of the current token (if not a token with unique
   * representation, e.g., (, ), _, ...).
   */
  std::vector<char> d_token;

  /**
   * The read buffer.
   * Characters are read from the input file into the buffer in s_buf_size
   * chunks, and next_char() then reads character by character from the buffer.
   */
  std::array<char, s_buf_size> d_buffer{};  // value-initialized to 0
  /** The index of the next character to be read from the buffer. */
  size_t d_buf_idx = s_buf_size;
  /** True if we saved a character that has not been consumed yet. */
  bool d_saved = false;

  /** The error message. */
  std::string d_error;
};

}  // namespace parser::smt2
}  // namespace bzla

#endif
