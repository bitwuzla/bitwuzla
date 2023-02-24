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
Lexer::token()
{
  return d_token;
}

bool
Lexer::error()
{
  return !d_error.empty();
}

const std::string&
Lexer::error_msg()
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

RESTART:
  do
  {
    d_coo = d_next_coo;
    if ((ch = next_char()) == EOF)
    {
      assert(EOF < 0);
      return Token::ENDOFFILE;
    }
  } while (std::isspace(ch));

  if (ch == ';')
  {
    while ((ch = next_char()) != '\n')
    {
      if (ch == EOF)
      {
        d_error = "unexpected end-of-file in comment";
        return Token::INVALID;
      }
    }
    goto RESTART;
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
Lexer::err_char(int32_t ch)
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
Lexer::char_class(int32_t ch)
{
  if (ch < 0 || ch >= 256)
  {
    return 0;
  }
  return d_char_classes[ch];
}

bool
Lexer::is_char_class(int32_t ch, CharacterClass cclass)
{
  return char_class(ch) & static_cast<uint32_t>(cclass);
}

std::ostream&
operator<<(std::ostream& out, Token token)
{
  switch (token)
  {
    case Token::INVALID: out << "TOKEN_INVALID"; break;
    case Token::ENDOFFILE: out << "TOKEN_EOF"; break;
    case Token::PARENT: out << "TOKEN_PARENT"; break;
    case Token::LPAR: out << "TOKEN_LPAR"; break;
    case Token::RPAR: out << "TOKEN_RPAR"; break;
    case Token::SYMBOL: out << "TOKEN_SYMBOL"; break;
    case Token::ATTRIBUTE: out << "TOKEN_ATTRIBUTE"; break;
    case Token::EXP: out << "TOKEN_EXP"; break;
    case Token::LETBIND: out << "TOKEN_LETBIND"; break;
    case Token::PARLETBIND: out << "TOKEN_PARLETBIND"; break;
    case Token::SORTED_VAR: out << "TOKEN_SORTED_VAR"; break;
    case Token::SORTED_VARS: out << "TOKEN_SORTED_VARS"; break;
    case Token::DECIMAL_CONSTANT: out << "TOKEN_DECIMAL_CONSTANT"; break;
    case Token::HEXADECIMAL_CONSTANT:
      out << "TOKEN_HEXADECIMAL_CONSTANT";
      break;
    case Token::BINARY_CONSTANT: out << "TOKEN_BINARY_CONSTANT"; break;
    case Token::STRING_CONSTANT: out << "TOKEN_STRING_CONSTANT"; break;
    case Token::REAL_CONSTANT: out << "TOKEN_REAL_CONSTANT"; break;
    case Token::PAR: out << "TOKEN_PAR"; break;
    case Token::NUMERAL_RESERVED_WORD:
      out << "TOKEN_NUMERAL_RESERVED_WORD";
      break;
    case Token::DECIMAL_RESERVED_WORD:
      out << "TOKEN_DECIMAL_RESERVED_WORD";
      break;
    case Token::STRING_RESERVED_WORD:
      out << "TOKEN_STRING_RESERVED_WORD";
      break;
    case Token::UNDERSCORE: out << "TOKEN_UNDERSCORE"; break;
    case Token::BANG: out << "TOKEN_BANG"; break;
    case Token::AS: out << "TOKEN_AS"; break;
    case Token::LET: out << "TOKEN_LET"; break;
    case Token::FORALL: out << "TOKEN_FORALL"; break;
    case Token::EXISTS: out << "TOKEN_EXISTS"; break;
    case Token::SET_LOGIC: out << "TOKEN_SET_LOGIC"; break;
    case Token::SET_OPTION: out << "TOKEN_SET_OPTION"; break;
    case Token::SET_INFO: out << "TOKEN_SET_INFO"; break;
    case Token::DECLARE_SORT: out << "TOKEN_DECLARE_SORT"; break;
    case Token::DEFINE_SORT: out << "TOKEN_DEFINE_SORT"; break;
    case Token::DECLARE_FUN: out << "TOKEN_DECLARE_SORT"; break;
    case Token::DEFINE_FUN: out << "TOKEN_DEFINE_FUN"; break;
    case Token::DECLARE_CONST: out << "TOKEN_DECLARE_CONST"; break;
    case Token::PUSH: out << "TOKEN_PUSH"; break;
    case Token::POP: out << "TOKEN_POP"; break;
    case Token::ASSERT: out << "TOKEN_ASSERT"; break;
    case Token::CHECK_SAT: out << "TOKEN_CHECK_SAT"; break;
    case Token::CHECK_SAT_ASSUMING: out << "TOKEN_CHECK_SAT_ASSUMING"; break;
    case Token::GET_ASSERTIONS: out << "TOKEN_GET_ASSERTIONS"; break;
    case Token::GET_ASSIGNMENT: out << "TOKEN_GET_ASSIGNMENT"; break;
    case Token::GET_INFO: out << "TOKEN_GET_INFO"; break;
    case Token::GET_OPTION: out << "TOKEN_GET_OPTION"; break;
    case Token::GET_PROOF: out << "TOKEN_GET_PROOF"; break;
    case Token::GET_UNSAT_ASSUMPTIONS:
      out << "TOKEN_GET_UNSAT_ASSUMPTIONS";
      break;
    case Token::GET_UNSAT_CORE: out << "TOKEN_GET_UNSAT_CORE"; break;
    case Token::GET_VALUE: out << "TOKEN_GET_VALUE"; break;
    case Token::EXIT: out << "TOKEN_EXIT"; break;
    case Token::GET_MODEL: out << "TOKEN_GET_MODEL"; break;
    case Token::ECHO: out << "TOKEN_ECHO"; break;
    case Token::ALL_STATISTICS: out << "TOKEN_ALL_STATISTICS"; break;
    case Token::AUTHORS: out << "TOKEN_AUTHORS"; break;
    case Token::AXIOMS: out << "TOKEN_AXIOMS"; break;
    case Token::CHAINABLE: out << "TOKEN_CHAINABLE"; break;
    case Token::DEFINITION: out << "TOKEN_DEFINITION"; break;
    case Token::DIAG_OUTPUT_CHANNEL: out << "TOKEN_DIAG_OUTPUT_CHANNEL"; break;
    case Token::ERROR_BEHAVIOR: out << "TOKEN_ERROR_BEHAVIOR"; break;
    case Token::EXPAND_DEFINITIONS: out << "TOKEN_EXPAND_DEFINITIONS"; break;
    case Token::EXTENSIONS: out << "TOKEN_EXTENSIONS"; break;
    case Token::FUNS: out << "TOKEN_FUNS"; break;
    case Token::FUNS_DESCRIPTION: out << "TOKEN_FUNS_DESCRIPTION"; break;
    case Token::INTERACTIVE_MODE: out << "TOKEN_INTERACTIVE_MODE"; break;
    case Token::PRODUCE_ASSERTIONS: out << "TOKEN_PRODUCE_ASSERTIONS"; break;
    case Token::LANGUAGE: out << "TOKEN_LANGUAGE"; break;
    case Token::LEFT_ASSOC: out << "TOKEN_LEFT_ASSOC"; break;
    case Token::NAME: out << "TOKEN_NAME"; break;
    case Token::NAMED: out << "TOKEN_NAMED"; break;
    case Token::NOTES: out << "TOKEN_NOTES"; break;
    case Token::PRINT_SUCCESS: out << "TOKEN_PRINT_SUCCESS"; break;
    case Token::PRODUCE_ASSIGNMENTS: out << "TOKEN_PRODUCE_ASSIGNMENTS"; break;
    case Token::PRODUCE_MODELS: out << "TOKEN_PRODUCE_MODELS"; break;
    case Token::PRODUCE_PROOFS: out << "TOKEN_PRODUCE_PROOFS"; break;
    case Token::PRODUCE_UNSAT_ASSUMPTIONS:
      out << "TOKEN_PRODUCE_UNSAT_ASSUMPTIONS";
      break;
    case Token::PRODUCE_UNSAT_CORES: out << "TOKEN_PRODUCE_UNSAT_CORES"; break;
    case Token::RANDOM_SEED: out << "TOKEN_PRODUCE_RANDOM_SEED"; break;
    case Token::REASON_UNKNOWN: out << "TOKEN_REASON_UNKNOWN"; break;
    case Token::REGULAR_OUTPUT_CHANNEL:
      out << "TOKEN_REGULAR_OUTPUT_CHANNEL";
      break;
    case Token::RIGHT_ASSOC: out << "TOKEN_RIGHT_ASSOC"; break;
    case Token::SORTS: out << "TOKEN_SORTS"; break;
    case Token::SORTS_DESCRIPTION: out << "TOKEN_SORTS_DESCRIPTION"; break;
    case Token::STATUS: out << "TOKEN_STATUS"; break;
    case Token::THEORIES: out << "TOKEN_THEORIES"; break;
    case Token::VALUES: out << "TOKEN_VALUES"; break;
    case Token::VERBOSITY: out << "TOKEN_VERBOSITY"; break;
    case Token::VERSION: out << "TOKEN_VERSION"; break;
    case Token::GLOBAL_DECLARATIONS: out << "TOKEN_GLOBAL_DECLARATIONS"; break;
  }
  return out;
}

}  // namespace parser::smt2
}  // namespace bzla
