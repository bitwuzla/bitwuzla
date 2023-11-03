/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_SMT2_LEXER_H_INCLUDED
#define BZLA_PARSER_SMT2_LEXER_H_INCLUDED

#include <array>
#include <cassert>
#include <cstring>
#include <sstream>
#include <vector>

#include "parser/smt2/token.h"

/* -------------------------------------------------------------------------- */

namespace bzla {
namespace parser::smt2 {

/* -------------------------------------------------------------------------- */

class CharacterClasses
{
 public:
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

  /**
   * @return True if given character belongs to the given character class.
   * @note implemented here for inlining
   */
  static bool is_in_class(int32_t ch, CharacterClass cclass)
  {
    if (ch < 0 || ch >= 256)
    {
      return false;
    }
    return get().d_char_classes[static_cast<uint8_t>(ch)]
           & static_cast<uint8_t>(cclass);
  }

  /**
   * @return True if given character is a printable character.
   * @note implemented here for inlining
   */
  static bool is_printable(int32_t ch)
  {
    for (size_t i = 0; s_printable_ascii_chars[i] != 0; ++i)
    {
      if (s_printable_ascii_chars[i] == ch)
      {
        return true;
      }
    }
    return false;
  }

 private:
  /** The set of legal printable characters. */
  inline static constexpr const char* s_printable_ascii_chars =
      "!\"#$%&'()*+,-./"
      "0123456789"
      ":;<=>?@"
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "[\\]^_`"
      "abcdefghijklmnopqrstuvwxyz"
      "{|}~"
      " \t\r\n";
  /** The set of characters that are letters. */
  inline static constexpr const char* s_letter_chars =
      "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
      "abcdefghijklmnopqrstuvwxyz";
  /** The set of decimal digits. */
  inline static constexpr const char* s_decimal_digit_chars = "0123456789";
  /** The set of hexadecimal digits. */
  inline static constexpr const char* s_hexadecimal_digit_chars =
      "0123456789abcdefABCDEF";
  /** The set of non-letter/non-digit characters that may occur in symbols. */
  inline static constexpr const char* s_extra_symbol_chars =
      "+-/*=%?!.$_~&^<>@";
  /** The set of non-letter/non-digit characters that may occur in keywords. */
  inline static constexpr const char* s_extra_keyword_chars =
      "+-/*=%?!.$_~&^<>@";

  /** Constructor. */
  constexpr CharacterClasses();
  /** Initialize the character classes. */
  constexpr void init();
  /** @return True if all character classes are initialized. */
  constexpr bool complete() const;
  /** Get CharacterClasses singleton. */
  static const CharacterClasses& get();

  /** The character classes. */
  std::array<uint8_t, 256> d_char_classes{};  // value-initialized to 0
};

/* -------------------------------------------------------------------------- */

class Lexer
{
 public:
  /**
   * Helper to determine if a given string is a valid symbol, i.e., contains
   * only characters allowed to occur in simple (non-quoted) symbols.
   * @note This is not needed for the lexer itself, but to determine, e.g., in
   *       the printer, if symbols created via the API conform to the SMT-LIB
   *       standard.
   * @return True if the given string is a valid symbol.
   */
  static bool is_valid_symbol(const std::string& s);
  /**
   * Helper to determine if a given string is a valid quoted symbol, i.e., a
   * sequence of whitespace and printable characters that starts and ends with
   * '|' and does not otherwise contain '\' and '|'.
   * @note This is not needed for the lexer itself, but to determine, e.g., in
   *       the printer, if symbols created via the API conform to the SMT-LIB
   *       standard.
   * @return True if the given string is a valid quoted symbol.
   */
  static bool is_valid_quoted_symbol(const std::string& s);

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

  /** The size of the chunks to be read into the input file buffer d_buffer. */
  size_t d_buf_size = 1024;
  /** The index of the next character to be read from the buffer. */
  size_t d_buf_idx = d_buf_size;

 private:
  /** Helper for next_token(). */
  Token next_token_aux();

  /**
   * @return The next character in the input file.
   * @note implemented here for inlining
   */
  int32_t next_char()
  {
    if (d_buf_idx == d_buf_size)
    {
      assert(!d_saved);
      size_t cnt =
          std::fread(d_buffer.data(), sizeof(char), d_buf_size, d_infile);
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
   * Characters are read from the input file into the buffer in d_buf_size
   * chunks, and next_char() then reads character by character from the buffer.
   */
  std::vector<char> d_buffer;  // value-initialized to 0
  /** True if we saved a character that has not been consumed yet. */
  bool d_saved = false;

  /** The error message. */
  std::string d_error;
};

/* -------------------------------------------------------------------------- */

}  // namespace parser::smt2
}  // namespace bzla

#endif
