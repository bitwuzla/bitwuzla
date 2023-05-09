#include "parser/smt2/lexer.h"

#include <cassert>
#include <cctype>
#include <sstream>
#include <vector>

namespace bzla {
namespace parser::smt2 {

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
      if (!is_char_class(ch, CharacterClass::HEXADECIMAL_DIGIT))
      {
        d_token.push_back(0);
        return error(ch, "expected hexa-decimal digit after '#x'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (!is_char_class(ch, CharacterClass::HEXADECIMAL_DIGIT))
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
      if (!is_char_class(ch, CharacterClass::STRING))
      {
        if (is_printable(ch))
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
    if (!is_char_class(ch, CharacterClass::KEYWORD))
    {
      d_token.push_back(0);
      return error(ch, "unexpected " + err_char(ch) + " after ':'");
    }
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::KEYWORD))
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
      if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
      {
        d_token.push_back(0);
        return error(ch, "expected decimal digit after '0.'");
      }
      push_char(ch);
      for (;;)
      {
        ch = next_char();
        if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
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
  else if (is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
  {
    Token res = Token::DECIMAL_VALUE;
    push_char(ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
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
        if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
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
    if (d_token[0] == '_' && d_token[1] == 0)
    {
      return Token::UNDERSCORE;
    }
    return Token::SYMBOL;
  }
  d_token.push_back(0);
  if (is_printable(ch))
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

void
Lexer::init_char_classes()
{
  for (auto c : s_printable_ascii_chars)
  {
    d_char_classes[c] = static_cast<uint32_t>(CharacterClass::STRING);
    if (c != '\\' && c != '|')
    {
      d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::QUOTED_SYMBOL);
    }
  }
  for (auto c : s_decimal_digit_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::DECIMAL_DIGIT);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
  for (auto c : s_hexadecimal_digit_chars)
  {
    d_char_classes[c] |=
        static_cast<uint32_t>(CharacterClass::HEXADECIMAL_DIGIT);
  }
  for (auto c : s_letter_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
  for (auto c : s_extra_symbol_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::SYMBOL);
  }
  for (auto c : s_extra_keyword_chars)
  {
    d_char_classes[c] |= static_cast<uint32_t>(CharacterClass::KEYWORD);
  }
}
}  // namespace parser::smt2
}  // namespace bzla
