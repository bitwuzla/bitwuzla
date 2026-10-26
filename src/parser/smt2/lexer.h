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
#include <string>
#include <string_view>
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
    BINARY_DIGIT      = (1 << 6),
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
    return (ch >= '!' && ch <= '~') || ch == ' ' || ch == '\t' || ch == '\r'
           || ch == '\n';
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

  /** Constructor. */
  Lexer() { configure_buffer(); }
  /** Disallow copying, the lexer maintains pointers into its read buffer. */
  Lexer(const Lexer&)            = delete;
  Lexer& operator=(const Lexer&) = delete;
  /**
   * @return The next token.
   * @note implemented here for inlining
   */
  Token next_token()
  {
    d_last_coo = d_coo;
    Token res  = next_token_aux();
    // The token is the sequence of characters consumed since d_tok_start,
    // prefixed by d_token if it was spilled on refilling the buffer.
    if (!d_tok_start)
    {
      d_tok = std::string_view();
    }
    else if (d_token.empty())
    {
      d_tok = std::string_view(d_tok_start, d_cur - d_tok_start);
    }
    else
    {
      d_token.append(d_tok_start, d_cur - d_tok_start);
      d_tok = d_token;
    }
    d_tok_start = nullptr;
    return res;
  }
  /**
   * @return True if lexer parsed a token that has a non-unique string
   *         representation (e.g., symbols, attributes, binary values, etc.).
   *         This string representation can then be queried via token().
   */
  bool has_token() const { return !d_tok.empty(); }
  /**
   * Get a string representation of the last parsed token. Empty if
   * !has_token().
   * @note The returned string is only valid until the next call to
   *       next_token().
   * @return The string representation of the token.
   */
  const char* token() const;
  /**
   * Get a string representation of the last parsed token, without copying it
   * if possible.
   * @note The returned string view is only valid until the next call to
   *       next_token().
   * @return The string representation of the token.
   */
  std::string_view token_view() const { return d_tok; }
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

  /**
   * Initialize lexer to read from given input stream.
   * @param input The input stream.
   */
  void init(std::istream* input);

  /**
   * Configure read buffer.
   * @param buf_size The size of the buffer. A buffer size of 1 configures the
   *                 lexer for interactive input: characters are then read one
   *                 at a time, as reading ahead could block on input that is
   *                 not yet available.
   */
  void configure_buffer(size_t buf_size = s_default_buf_size);

  /**
   * Flush the output stream tied to the input stream (if any).
   * In interactive mode, the input stream is read via its stream buffer, which
   * bypasses the automatic flush of the tied stream on every read. This must
   * be called before the lexer may block on input (e.g., before parsing the
   * next command) to ensure that all responses have been written.
   */
  void flush_tied_output()
  {
    if (d_buf_size == 1 && d_input && d_input->tie())
    {
      d_input->tie()->flush();
    }
  }

  /** The default size of the read buffer. */
  static constexpr size_t s_default_buf_size = 1 << 16;

 private:
  /** Helper for next_token(). */
  Token next_token_aux();

  /**
   * @return The string representation of the token currently being lexed.
   * @note Only for error messages, this is not zero-copy.
   */
  std::string cur_token() const;

  /**
   * Refill the read buffer from the input stream.
   * @return False if the end of the input stream has been reached.
   */
  bool fill_buffer();

  /**
   * @return The next character in the input stream without consuming it, EOF
   *         if the end of the input stream has been reached.
   * @note implemented here for inlining
   */
  int32_t peek_char()
  {
    if (d_cur == d_end && !fill_buffer())
    {
      return EOF;
    }
    return static_cast<unsigned char>(*d_cur);
  }

  /**
   * Consume the current character, which must have been peeked at via
   * peek_char().
   * @note implemented here for inlining
   */
  void consume_char()
  {
    assert(d_cur < d_end);
    if (*d_cur++ == '\n')
    {
      new_line();
    }
  }

  /** Record a new line, d_cur points to the first character of the line. */
  void new_line()
  {
    d_line += 1;
    d_line_start = offset();
  }

  /**
   * Consume the longest sequence of characters of the given class.
   * @note Characters of all classes passed to this function are on a single
   *       line, the current coordinate thus only changes in its column.
   */
  void consume_chars(CharacterClasses::CharacterClass cclass);

  /**
   * Consume the decimal point and the fractional digits of a decimal, the
   * current character must be the decimal point.
   * @return Token::REAL_VALUE, or Token::INVALID if the decimal point is not
   *         followed by at least one digit.
   */
  Token consume_decimal_fraction();

  /** @return The absolute offset of the current character in the input. */
  uint64_t offset() const { return d_buf_offset + (d_cur - d_buffer.data()); }

  /** @return The coordinate of the current character in the input. */
  Coordinate cur_coo() const { return {d_line, offset() - d_line_start + 1}; }

  /**
   * Helper for error().
   * @return String "character '<ch>'".
   */
  std::string err_char(int32_t ch) const;

  /**
   * Helper for error handling.
   * Compiles all data required for aborting on error (coordinate, message).
   * The coordinate of the error is the coordinate of the current character,
   * i.e., the first character that has not yet been consumed.
   * @param error_msg The error message to set.
   * @return The invalid token.
   */
  Token error(const std::string& error_msg);

  /** The input stream. */
  std::istream* d_input = nullptr;
  /** The coordinate of the current token. */
  Coordinate d_coo{1, 1};
  /** The coordinate of the last token. */
  Coordinate d_last_coo{1, 1};
  /** The current line. */
  uint64_t d_line = 1;
  /** The absolute offset of the first character of the current line. */
  uint64_t d_line_start = 0;

  /**
   * The string representation of the last token. Points into the read buffer
   * if the token does not cross a buffer boundary, else to d_token.
   */
  mutable std::string_view d_tok;
  /**
   * Holds the string representation of the current token if it does not fit
   * into the read buffer, i.e., the characters of the token that were
   * consumed before the buffer was refilled. Also used to provide a
   * null-terminated string representation via token().
   */
  mutable std::string d_token;
  /** The first character of the current token in the read buffer. */
  const char* d_tok_start = nullptr;

  /** The size of the chunks to be read into the input file buffer d_buffer. */
  size_t d_buf_size = s_default_buf_size;
  /**
   * The read buffer.
   * Characters are read from the input file into the buffer in d_buf_size
   * chunks, and the lexer then scans the buffer directly. The valid
   * characters in the buffer are followed by a null character as sentinel,
   * which does not belong to any character class.
   */
  std::vector<char> d_buffer;
  /** The current character in the buffer. */
  const char* d_cur = nullptr;
  /** The end of the valid characters in the buffer (the sentinel). */
  const char* d_end = nullptr;
  /** The absolute offset of the first character of the buffer in the input. */
  uint64_t d_buf_offset = 0;
  /** True if the end of the input stream has been reached. */
  bool d_eof = false;

  /** The error message. */
  std::string d_error;
};

/* -------------------------------------------------------------------------- */

}  // namespace parser::smt2
}  // namespace bzla

#endif
