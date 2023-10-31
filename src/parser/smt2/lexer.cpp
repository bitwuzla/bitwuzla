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
#include <cctype>
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

Lexer::Lexer(FILE* infile) : d_infile(infile), d_buffer(d_buf_size, 0)
{
  assert(infile);
}

Token
Lexer::next_token()
{
  d_last_coo = d_coo;
  return next_token_aux();
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
    if (s[i] == '\\' || s[i] == '|' || !CharacterClasses::is_printable(s[i]))
    {
      return false;
    }
  }
  return true;
}

/* Lexer private ------------------------------------------------------------ */

Token
Lexer::next_token_aux()
{
  int32_t ch;
  d_token.clear();

  // skip whitespace and comments
  for (;;)
  {
    do
    {
      d_coo = d_cur_coo;
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return Token::ENDOFFILE;
      }
    } while (CharacterClasses::is_printable(ch) && std::isspace(ch));

    if (ch != ';')
    {
      break;
    }
    while ((ch = next_char()) != '\n')
    {
      if (ch == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file in comment");
      }
    }
  }

  if (ch == '(')
  {
    push_char(ch);
    d_token.push_back(0);
    return Token::LPAR;
  }
  if (ch == ')')
  {
    push_char(ch);
    d_token.push_back(0);
    return Token::RPAR;
  }
  if (ch == '#')
  {
    push_char(ch);
    if ((ch = next_char()) == EOF)
    {
      d_token.push_back(0);
      return error(ch, "unexpected end of file after '#'");
    }
    if (ch == 'b')
    {
      push_char(ch);
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file after '#b'");
      }
      if (ch != '0' && ch != '1')
      {
        d_token.push_back(0);
        return error(ch, "expected '0' or '1' after '#b'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (ch != '0' && ch != '1') break;
        push_char(ch);
      }
      save_char(ch);
      d_token.push_back(0);
      return Token::BINARY_VALUE;
    }
    if (ch == 'x')
    {
      push_char(ch);
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file after '#x'");
      }
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::HEXADECIMAL_DIGIT))
      {
        d_token.push_back(0);
        return error(ch, "expected hexa-decimal digit after '#x'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (!CharacterClasses::is_in_class(
                ch, CharacterClasses::CharacterClass::HEXADECIMAL_DIGIT))
        {
          break;
        }
        push_char(ch);
      }
      save_char(ch);
      d_token.push_back(0);
      return Token::HEXADECIMAL_VALUE;
    }
    d_token.push_back(0);
    return error(ch, "expected 'x' or 'b' after '#'");
  }
  if (ch == '"')
  {
    push_char(ch);
    for (;;)
    {
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file in string");
      }
      if (ch == '"')
      {
        push_char(ch);
        ch = next_char();
        if (ch != '"')
        {
          save_char(ch);
          d_token.push_back(0);
          return Token::STRING_VALUE;
        }
      }
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::STRING))
      {
        if (CharacterClasses::is_printable(ch))
        {
          d_token.push_back(0);
          return error(ch, "illegal " + err_char(ch) + " in string");
        }
        d_token.push_back(0);
        return error(ch,
                     "illegal (non-printable) character (code "
                         + std::to_string(static_cast<unsigned char>(ch))
                         + ") in string");
      }
      push_char(ch);
    }
  }
  else if (ch == '|')
  {
    push_char(ch);
    for (;;)
    {
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file in quoted symbol");
      }
      push_char(ch);
      if (ch == '|')
      {
        d_token.push_back(0);
        return Token::SYMBOL;
      }
    }
  }
  else if (ch == ':')
  {
    push_char(ch);
    if ((ch = next_char()) == EOF)
    {
      d_token.push_back(0);
      return error(ch, "unexpected end of file after ':'");
    }
    if (!CharacterClasses::is_in_class(
            ch, CharacterClasses::CharacterClass::KEYWORD))
    {
      d_token.push_back(0);
      return error(ch, "unexpected " + err_char(ch) + " after ':'");
    }
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::KEYWORD))
      {
        break;
      }
      assert(ch != EOF);
      push_char(ch);
    }
    save_char(ch);
    d_token.push_back(0);
    return Token::ATTRIBUTE;
  }
  else if (ch == '0')
  {
    Token res = Token::DECIMAL_VALUE;
    push_char(ch);
    ch = next_char();
    if (ch == '.')
    {
      res = Token::REAL_VALUE;
      push_char(ch);
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(ch, "unexpected end of file after '0.'");
      }
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
      {
        d_token.push_back(0);
        return error(ch, "expected decimal digit after '0.'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (!CharacterClasses::is_in_class(
                ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
        {
          break;
        }
        push_char(ch);
      }
    }
    save_char(ch);
    d_token.push_back(0);
    return res;
  }
  else if (CharacterClasses::is_in_class(
               ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
  {
    Token res = Token::DECIMAL_VALUE;
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
      {
        break;
      }
      push_char(ch);
    }
    if (ch == '.')
    {
      res = Token::REAL_VALUE;
      push_char(ch);
      if ((ch = next_char()) == EOF)
      {
        d_token.push_back(0);
        return error(
            ch, "unexpected end of file after '" + std::string(token()) + "'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (!CharacterClasses::is_in_class(
                ch, CharacterClasses::CharacterClass::DECIMAL_DIGIT))
        {
          break;
        }
        push_char(ch);
      }
    }
    save_char(ch);
    d_token.push_back(0);
    return res;
  }
  else if (CharacterClasses::is_in_class(
               ch, CharacterClasses::CharacterClass::SYMBOL))
  {
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!CharacterClasses::is_in_class(
              ch, CharacterClasses::CharacterClass::SYMBOL))
      {
        break;
      }
      push_char(ch);
    }
    save_char(ch);
    d_token.push_back(0);
    if (d_token[0] == '_' && d_token[1] == 0)
    {
      return Token::UNDERSCORE;
    }
    return Token::SYMBOL;
  }
  d_token.push_back(0);
  if (CharacterClasses::is_printable(ch))
  {
    return error(ch, "illegal " + err_char(ch));
  }
  return error(ch,
               "illegal (non-printable) character (code "
                   + std::to_string(static_cast<unsigned char>(ch)) + ")");
}

std::string
Lexer::err_char(int32_t ch) const
{
  std::stringstream ss;
  ss << "character '" << static_cast<char>(ch) << "'";
  return ss.str();
}

Token
Lexer::error(int32_t ch, const std::string& error_msg)
{
  if (!d_saved)
  {
    save_char(ch);
  }
  d_coo   = d_cur_coo;
  d_error = error_msg;
  return Token::INVALID;
}

}  // namespace parser::smt2
}  // namespace bzla
