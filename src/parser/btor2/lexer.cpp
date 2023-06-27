/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/btor2/lexer.h"

#include <sstream>

namespace bzla {
namespace parser::btor2 {

/* Lexer public ------------------------------------------------------------- */

Lexer::Lexer(FILE* infile) : d_infile(infile)
{
  assert(infile);
  init_char_classes();
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
    } while (is_printable(ch) && std::isspace(ch));

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

  if (is_char_class(ch, CharacterClass::NUMBER))
  {
    Token res = Token::NUMBER;
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::NUMBER))
      {
        break;
      }
      push_char(ch);
    }
    if (ch == '.')
    {
      return error(ch, "unexpected '.' in number");
    }
    save_char(ch);
    d_token.push_back(0);
    return res;
  }
  else if (is_char_class(ch, CharacterClass::SYMBOL))
  {
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::SYMBOL))
      {
        break;
      }
      push_char(ch);
    }
    save_char(ch);
    d_token.push_back(0);
    auto it = d_str2token.find(d_token.data());
    if (it != d_str2token.end())
    {
      return it->second;
    }
    return Token::SYMBOL;
  }
  d_token.push_back(0);
  if (is_printable(ch))
  {
    return error(ch, "illegal " + err_char(ch));
  }
  return error(
      ch,
      "illegal (non-printable) character (code " + std::to_string(ch) + ")");
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

void
Lexer::init_char_classes()
{
  for (auto c : s_number_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::NUMBER);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (auto c : s_letter_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (auto c : s_extra_symbol_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
}

}  // namespace parser::btor2
}  // namespace bzla
