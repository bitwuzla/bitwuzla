#include "parser/smt2/lexer.h"

#include <cassert>
#include <cctype>
#include <sstream>
#include <vector>

namespace bzla {
namespace parser::smt2 {

Lexer::Lexer(std::istream* infile) : d_infile(infile)
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

const std::string&
Lexer::token() const
{
  return d_token;
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

Token
Lexer::next_token_aux()
{
  // BzlaSMT2Node *node;
  int32_t ch;
  d_token.clear();
  // parser->last_node = 0;
  std::stringstream token;

  for (;;)
  {
    do
    {
      d_coo = d_next_coo;
      if ((ch = next_char()) == EOF)
      {
        assert(EOF < 0);
        return Token::ENDOFFILE;
      }
    } while (std::isspace(ch));

    if (ch != ';')
    {
      break;
    }
    while ((ch = next_char()) != '\n')
    {
      if (ch == EOF)
      {
        d_error = "unexpected end-of-file in comment";
        return Token::INVALID;
      }
    }
  }

  if (ch == '(')
  {
    push_char(token, ch);
    return Token::LPAR;
  }
  if (ch == ')')
  {
    push_char(token, ch);
    return Token::RPAR;
  }
  if (ch == '#')
  {
    push_char(token, ch);
    if ((ch = next_char()) == EOF)
    {
      d_error = "unexpected end-of-file after '#'";
      return Token::INVALID;
    }
    if (ch == 'b')
    {
      push_char(token, ch);
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected end-of-file after '#b'";
        return Token::INVALID;
      }
      if (ch != '0' && ch != '1')
      {
        d_error = "expected '0' or '1' after '#b'";
        return Token::INVALID;
      }
      push_char(token, ch);
      for (;;)
      {
        ch = next_char();
        if (ch != '0' && ch != '1') break;
        push_char(token, ch);
      }
      save_char(ch);
      d_token = token.str();
      return Token::BINARY_CONSTANT;
    }
    else if (ch == 'x')
    {
      push_char(token, ch);
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected end-of-file after '#x'";
        return Token::INVALID;
      }
      if (!is_char_class(ch, CharacterClass::HEXADECIMAL_DIGIT))
      {
        d_error = "expected hexa-decimal digit after '#x'";
        return Token::INVALID;
      }
      push_char(token, ch);
      for (;;)
      {
        ch = next_char();
        if (!is_char_class(ch, CharacterClass::HEXADECIMAL_DIGIT))
        {
          break;
        }
        push_char(token, ch);
      }
      save_char(ch);
      d_token = token.str();
      return Token::HEXADECIMAL_CONSTANT;
    }
    else
    {
      d_error = "expected 'x' or 'b' after '#'";
      return Token::INVALID;
    }
  }
  else if (ch == '"')
  {
    push_char(token, ch);
    for (;;)
    {
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected " + err_char(ch) + " in string";
        return Token::INVALID;
      }
      if (ch == '"')
      {
        push_char(token, ch);
        ch = next_char();
        if (ch != '"')
        {
          save_char(ch);
          d_token = token.str();
          return Token::STRING_CONSTANT;
        }
      }
      if (!is_char_class(ch, CharacterClass::STRING))
      {
        d_error = "invalid " + err_char(ch) + " in string";
        return Token::INVALID;
      }
      push_char(token, ch);
    }
  }
  else if (ch == '|')
  {
    push_char(token, ch);
    for (;;)
    {
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected " + err_char(ch) + " in quoted symbol";
        return Token::INVALID;
      }
      push_char(token, ch);
      if (ch == '|')
      {
        // if (!(node = find_symbol_smt2(parser, parser->token.start)))
        //{
        //   node       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
        //   node->name = bzla_mem_strdup(parser->mem, parser->token.start);
        //   assert(!find_symbol_smt2(parser, node->name));
        //   insert_symbol_smt2(parser, node);
        // }
        // parser->last_node = node;
        d_token = token.str();
        return Token::SYMBOL;
      }
    }
  }
  else if (ch == ':')
  {
    push_char(token, ch);
    if ((ch = next_char()) == EOF)
    {
      d_error = "unexpected end-of-file after ':'";
      return Token::INVALID;
    }
    if (!is_char_class(ch, CharacterClass::KEYWORD))
    {
      d_error = "unexpected " + err_char(ch) + " after ':'";
      return Token::INVALID;
    }
    push_char(token, ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::KEYWORD))
      {
        break;
      }
      assert(ch != EOF);
      push_char(token, ch);
    }
    save_char(ch);
    // if (!(node = find_symbol_smt2(parser, parser->token.start)))
    //{
    //   node       = new_node_smt2(parser, BZLA_ATTRIBUTE_TAG_SMT2);
    //   node->name = bzla_mem_strdup(parser->mem, parser->token.start);
    //   assert(!find_symbol_smt2(parser, node->name));
    //   insert_symbol_smt2(parser, node);
    // }
    // parser->last_node = node;
    d_token = token.str();
    return Token::ATTRIBUTE;
  }
  else if (ch == '0')
  {
    Token res = Token::DECIMAL_CONSTANT;
    push_char(token, ch);
    ch = next_char();
    if (ch == '.')
    {
      res = Token::REAL_CONSTANT;
      push_char(token, ch);
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected end-of-file after '0.'";
        return Token::INVALID;
      }
      if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
      {
        d_error = "expected decimal digit after '0.'";
        return Token::INVALID;
      }
      push_char(token, ch);
      for (;;)
      {
        ch = next_char();
        if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
        {
          break;
        }
        push_char(token, ch);
      }
    }
    save_char(ch);
    d_token = token.str();
    return res;
  }
  else if (is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
  {
    Token res = Token::DECIMAL_CONSTANT;
    push_char(token, ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
      {
        break;
      }
      push_char(token, ch);
    }
    if (ch == '.')
    {
      res = Token::REAL_CONSTANT;
      push_char(token, ch);
      if ((ch = next_char()) == EOF)
      {
        d_error = "unexpected end-of-file after '" + token.str() + "'";
        return Token::INVALID;
      }
      push_char(token, ch);
      for (;;)
      {
        ch = next_char();
        if (!is_char_class(ch, CharacterClass::DECIMAL_DIGIT))
        {
          break;
        }
        push_char(token, ch);
      }
    }
    save_char(ch);
    d_token = token.str();
    return res;
  }
  else if (is_char_class(ch, CharacterClass::SYMBOL))
  {
    push_char(token, ch);
    for (;;)
    {
      ch = next_char();
      if (!is_char_class(ch, CharacterClass::SYMBOL))
      {
        break;
      }
      push_char(token, ch);
    }
    save_char(ch);
    if (token.str() == "_")
    {
      return Token::UNDERSCORE;
    }
    // if (!(node = find_symbol_smt2(parser, parser->token.start)))
    //{
    //   node       = new_node_smt2(parser, BZLA_SYMBOL_TAG_SMT2);
    //   node->name = bzla_mem_strdup(parser->mem, parser->token.start);
    //   assert(!find_symbol_smt2(parser, node->name));
    //   insert_symbol_smt2(parser, node);
    // }
    // parser->last_node = node;
    d_token = token.str();
    return Token::SYMBOL;
  }
  else
  {
    d_error = "illegal " + err_char(ch);
    return Token::INVALID;
  }

  d_error = "internal tokenizer error";
  return Token::INVALID;
}

int32_t
Lexer::next_char()
{
  int32_t res;
  if (d_saved)
  {
    res     = d_saved_char;
    d_saved = false;
  }
  else
  {
    res = d_infile->get();
  }
  if (res == '\n')
  {
    d_next_coo.line++;
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

void
Lexer::push_char(std::stringstream& token, int32_t ch)
{
  assert(ch != EOF);
  assert(ch >= 0 && ch < 256);
  token << static_cast<char>(ch);
}

void
Lexer::save_char(int32_t ch)
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

std::string
Lexer::err_char(int32_t ch) const
{
  std::stringstream ss;
  ss << "character '" << static_cast<char>(ch) << "'";
  return ss.str();
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

uint32_t
Lexer::char_class(int32_t ch) const
{
  if (ch < 0 || ch >= 256)
  {
    return 0;
  }
  return d_char_classes[ch];
}

bool
Lexer::is_char_class(int32_t ch, CharacterClass cclass) const
{
  return char_class(ch) & static_cast<uint32_t>(cclass);
}

}  // namespace parser::smt2
}  // namespace bzla
