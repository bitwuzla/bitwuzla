/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/smt2/lexer.h"

#include <algorithm>
#include <cassert>
#include <sstream>
#include <vector>

namespace bzla {
namespace parser::smt2 {

/* Lexer public ------------------------------------------------------------- */

constexpr CharacterClasses::CharacterClasses() { init(); }

constexpr void
CharacterClasses::init()
{
  for (size_t i = 0; s_printable_ascii_chars[i] != 0; ++i)
  {
    uint8_t c         = s_printable_ascii_chars[i];
    d_char_classes[c] = static_cast<uint32_t>(CharacterClass::STRING);
    if (c != '\\' && c != '|')
    {
      d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::QUOTED_SYMBOL);
    }
  }
  for (size_t i = 0; s_decimal_digit_chars[i] != 0; ++i)
  {
    uint8_t c = s_decimal_digit_chars[i];
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::DECIMAL_DIGIT);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
  d_char_classes['0'] |= static_cast<uint32_t>(CharacterClass::BINARY_DIGIT);
  d_char_classes['1'] |= static_cast<uint32_t>(CharacterClass::BINARY_DIGIT);
  for (size_t i = 0; s_hexadecimal_digit_chars[i] != 0; ++i)
  {
    uint8_t c = s_hexadecimal_digit_chars[i];
    d_char_classes[c] |=
        static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (size_t i = 0; s_letter_chars[i] != 0; ++i)
  {
    uint8_t c = s_letter_chars[i];
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
  for (size_t i = 0; s_extra_symbol_chars[i] != 0; ++i)
  {
    uint8_t c = s_extra_symbol_chars[i];
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (size_t i = 0; s_extra_keyword_chars[i] != 0; ++i)
  {
    uint8_t c = s_extra_keyword_chars[i];
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
}

const CharacterClasses&
CharacterClasses::get()
{
  static const constexpr CharacterClasses classes;
  return classes;
}

/* Lexer public ------------------------------------------------------------- */

void
Lexer::init(std::istream* input)
{
  assert(input);
  d_input     = input;
  d_cur       = d_buffer.data();
  d_end       = d_cur;
  d_tok_start = nullptr;
  d_tok       = std::string_view();
  d_token.clear();
  d_buf_offset = 0;
  d_eof        = false;
  d_coo        = {1, 1};
  d_last_coo   = {1, 1};
  d_line       = 1;
  d_line_start = 0;
}

void
Lexer::configure_buffer(size_t buf_size)
{
  assert(buf_size > 0);
  d_buf_size = buf_size;
  // reserve space for the sentinel
  d_buffer.assign(d_buf_size + 1, 0);
  d_cur = d_buffer.data();
  d_end = d_cur;
}

const char*
Lexer::token() const
{
  if (d_tok.data() != d_token.data())
  {
    d_token.assign(d_tok);
    d_tok = d_token;
  }
  return d_token.c_str();
}

bool
Lexer::error() const
{
  return !d_error.empty();
}

const std::string&
Lexer::error_msg() const
{
  return d_error;
}

bool
Lexer::is_valid_symbol(const std::string& s)
{
  return std::none_of(s.begin(), s.end(), [](char ch) {
    return !CharacterClasses::is_in_class(
        ch, CharacterClasses::CharacterClass::SYMBOL);
  });
}

bool
Lexer::is_valid_quoted_symbol(const std::string& s)
{
  if (s.size() < 2)
  {
    return false;
  }
  if (s[0] != '|' || s[s.size() - 1] != '|')
  {
    return false;
  }
  for (size_t i = 1, n = s.size() - 1; i < n; ++i)
  {
    if (s[i] == '\\' || s[i] == '|')
    {
      return false;
    }
  }
  return true;
}

/* Lexer private ------------------------------------------------------------ */

bool
Lexer::fill_buffer()
{
  assert(d_cur == d_end);
  if (d_eof)
  {
    return false;
  }
  // spill the characters of the current token, the buffer is overwritten
  if (d_tok_start)
  {
    d_token.append(d_tok_start, d_end - d_tok_start);
  }
  d_buf_offset += d_end - d_buffer.data();
  char* buf = d_buffer.data();
  size_t n  = 0;
  if (d_buf_size == 1)
  {
    // Interactive input: read only a single character, reading ahead could
    // block on input that is not yet available. We read via the stream
    // buffer to bypass the sentry of the input stream, which flushes the tied
    // output stream on every read (see flush_tied_output()).
    std::streambuf* sb = d_input->rdbuf();
    int32_t ch         = sb ? sb->sbumpc() : EOF;
    if (ch != EOF)
    {
      buf[n++] = static_cast<char>(ch);
    }
    else
    {
      d_eof = true;
    }
  }
  else
  {
    d_input->read(buf, d_buf_size);
    n = d_input->gcount();
    // istream::read() only reads less than requested at the end of the input
    d_eof = n < d_buf_size;
  }
  buf[n] = 0;  // sentinel
  d_cur  = buf;
  d_end  = buf + n;
  if (d_tok_start)
  {
    d_tok_start = d_cur;
  }
  return n > 0;
}

void
Lexer::consume_chars(CharacterClasses::CharacterClass cclass)
{
  for (;;)
  {
    // no bounds check required, the sentinel is not in any class
    const char* p = d_cur;
    while (
        CharacterClasses::is_in_class(static_cast<unsigned char>(*p), cclass))
    {
      ++p;
    }
    d_cur = p;
    if (p < d_end || !fill_buffer())
    {
      return;
    }
  }
}

std::string
Lexer::cur_token() const
{
  assert(d_tok_start);
  return d_token + std::string(d_tok_start, d_cur - d_tok_start);
}

Token
Lexer::next_token_aux()
{
  d_token.clear();
  d_tok_start = nullptr;

  // skip whitespace and comments
  int32_t ch;
  for (;;)
  {
    while (d_cur < d_end)
    {
      char c = *d_cur;
      if (c == ' ' || c == '\t' || c == '\r')
      {
        ++d_cur;
      }
      else if (c == '\n')
      {
        ++d_cur;
        new_line();
      }
      else if (c == ';')
      {
        // skip comment
        for (;;)
        {
          const char* nl =
              static_cast<const char*>(std::memchr(d_cur, '\n', d_end - d_cur));
          if (nl)
          {
            d_cur = nl + 1;
            new_line();
            break;
          }
          d_cur = d_end;
          if (!fill_buffer())
          {
            return error("unexpected end of file in comment");
          }
        }
      }
      else
      {
        break;
      }
    }
    if (d_cur < d_end || !fill_buffer())
    {
      break;
    }
  }

  d_coo       = cur_coo();
  d_tok_start = d_cur;
  ch          = peek_char();
  switch (ch)
  {
    case EOF: return Token::ENDOFFILE;

    case '(': consume_char(); return Token::LPAR;

    case ')': consume_char(); return Token::RPAR;

    case '#':
      consume_char();
      ch = peek_char();
      if (ch == EOF)
      {
        return error("unexpected end of file after '#'");
      }
      if (ch == 'b')
      {
        consume_char();
        ch = peek_char();
        if (ch == EOF)
        {
          return error("unexpected end of file after '#b'");
        }
        if (ch != '0' && ch != '1')
        {
          return error("expected '0' or '1' after '#b'");
        }
        consume_chars(CharacterClasses::CharacterClass::BINARY_DIGIT);
        return Token::BINARY_VALUE;
      }
      if (ch == 'x')
      {
        consume_char();
        ch = peek_char();
        if (ch == EOF)
        {
          return error("unexpected end of file after '#x'");
        }
        if (!CharacterClasses::is_in_class(
                ch, CharacterClasses::CharacterClass::HEXADECIMAL_DIGIT))
        {
          return error("expected hexa-decimal digit after '#x'");
        }
        consume_chars(CharacterClasses::CharacterClass::HEXADECIMAL_DIGIT);
        return Token::HEXADECIMAL_VALUE;
      }
      return error("expected 'x' or 'b' after '#'");

    case '"':
      consume_char();
      for (;;)
      {
        ch = peek_char();
        if (ch == EOF)
        {
          return error("unexpected end of file in string");
        }
        if (ch == '"')
        {
          consume_char();
          if (peek_char() != '"')
          {
            return Token::STRING_VALUE;
          }
        }
        else if (!CharacterClasses::is_in_class(
                     ch, CharacterClasses::CharacterClass::STRING))
        {
          if (CharacterClasses::is_printable(ch))
          {
            return error("illegal " + err_char(ch) + " in string");
          }
          return error("illegal (non-printable) character (code "
                       + std::to_string(ch) + ") in string");
        }
        consume_char();
      }

    case '|':
      consume_char();
      for (;;)
      {
        if (d_cur == d_end && !fill_buffer())
        {
          return error("unexpected end of file in quoted symbol");
        }
        const char* p =
            static_cast<const char*>(std::memchr(d_cur, '|', d_end - d_cur));
        if (!p)
        {
          p = d_end;
        }
        // quoted symbols may span multiple lines
        for (const char* nl = d_cur;
             (nl = static_cast<const char*>(std::memchr(nl, '\n', p - nl)));)
        {
          d_line += 1;
          nl += 1;
          d_line_start = d_buf_offset + (nl - d_buffer.data());
        }
        d_cur = p;
        if (p < d_end)
        {
          consume_char();
          return Token::SYMBOL;
        }
      }

    case ':':
      consume_char();
      ch = peek_char();
      if (ch == EOF)
      {
        return error("unexpected end of file after ':'");
      }
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::KEYWORD))
      {
        return error("unexpected " + err_char(ch) + " after ':'");
      }
      consume_chars(CharacterClasses::CharacterClass::KEYWORD);
      return Token::ATTRIBUTE;

    case '0':
      consume_char();
      if (peek_char() == '.')
      {
        consume_char();
        ch = peek_char();
        if (ch == EOF)
        {
          return error("unexpected end of file after '0.'");
        }
        if (!CharacterClasses::is_in_class(
                ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
        {
          return error("expected decimal digit after '0.'");
        }
        consume_chars(CharacterClasses::CharacterClass::DECIMAL_DIGIT);
        return Token::REAL_VALUE;
      }
      return Token::DECIMAL_VALUE;

    default: break;
  }

  if (CharacterClasses::is_in_class(
          ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
  {
    consume_chars(CharacterClasses::CharacterClass::DECIMAL_DIGIT);
    if (peek_char() == '.')
    {
      consume_char();
      if (peek_char() == EOF)
      {
        return error("unexpected end of file after '" + cur_token() + "'");
      }
      consume_char();
      consume_chars(CharacterClasses::CharacterClass::DECIMAL_DIGIT);
      return Token::REAL_VALUE;
    }
    return Token::DECIMAL_VALUE;
  }

  if (CharacterClasses::is_in_class(ch,
                                    CharacterClasses::CharacterClass::SYMBOL))
  {
    consume_chars(CharacterClasses::CharacterClass::SYMBOL);
    size_t len = d_token.size() + (d_cur - d_tok_start);
    if (len == 1 && (d_token.empty() ? *d_tok_start : d_token[0]) == '_')
    {
      return Token::UNDERSCORE;
    }
    return Token::SYMBOL;
  }

  if (CharacterClasses::is_printable(ch))
  {
    return error("illegal " + err_char(ch));
  }
  return error("illegal (non-printable) character (code " + std::to_string(ch)
               + ")");
}

std::string
Lexer::err_char(int32_t ch) const
{
  std::stringstream ss;
  ss << "character '" << static_cast<char>(ch) << "'";
  return ss.str();
}

Token
Lexer::error(const std::string& error_msg)
{
  d_coo   = cur_coo();
  d_error = error_msg;
  return Token::INVALID;
}

}  // namespace parser::smt2
}  // namespace bzla
