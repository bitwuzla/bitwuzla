/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PARSER_BTOR2_LEXER_H_INCLUDED
#define BZLA_PARSER_BTOR2_LEXER_H_INCLUDED

#include <array>
#include <cassert>
#include <cstring>
#include <unordered_map>
#include <vector>

#include "parser/btor2/token.h"

namespace bzla {
namespace parser::btor2 {

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

  /**
   * Get the next character that will be parsed by the lexer.
   * This call is internally handled as a look-ahead and mainly needed because
   * the parser needs to determine if a line has ended or if there is still
   * an (optional) symbol to parse.
   * @return The look-ahead character.
   */
  int32_t look_ahead()
  {
    int32_t ch = next_char();
    save_char(ch);
    return ch;
  }

 private:
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
  /** The set of number characters. */
  inline static const std::string s_number_chars = "-0123456789";
  /** The set of non-letter/non-digit characters that may occur in symbols. */
  inline static const std::string s_extra_symbol_chars =
      "!\"#'()+-/*:<=>%?!.$_~&^<>@[\\]^_`{|}~";

  inline static std::unordered_map<std::string, Token> d_str2token = {
      {"add", Token::ADD},         {"and", Token::AND},
      {"array", Token::ARRAY},     {"bad", Token::BAD},
      {"bitvec", Token::BITVEC},   {"concat", Token::CONCAT},
      {"const", Token::CONST},     {"constraint", Token::CONSTRAINT},
      {"constd", Token::CONSTD},   {"consth", Token::CONSTH},
      {"dec", Token::DEC},         {"eq", Token::EQ},
      {"fair", Token::FAIR},       {"iff", Token::IFF},
      {"implies", Token::IMPLIES}, {"inc", Token::INC},
      {"init", Token::INIT},       {"input", Token::INPUT},
      {"ite", Token::ITE},         {"justice", Token::JUSTICE},
      {"mul", Token::MUL},         {"nand", Token::NAND},
      {"neq", Token::NEQ},         {"neg", Token::NEG},
      {"nego", Token::NEGO},       {"next", Token::NEXT},
      {"nor", Token::NOR},         {"not", Token::NOT},
      {"one", Token::ONE},         {"ones", Token::ONES},
      {"or", Token::OR},           {"outpu", Token::OUTPUT},
      {"read", Token::READ},       {"redand", Token::REDAND},
      {"redor", Token::REDOR},     {"redxor", Token::REDXOR},
      {"rol", Token::ROL},         {"ror", Token::ROR},
      {"saddo", Token::SADDO},     {"sdiv", Token::SDIV},
      {"sdivo", Token::SDIVO},     {"sext", Token::SEXT},
      {"sgt", Token::SGT},         {"sgte", Token::SGTE},
      {"slice", Token::SLICE},     {"sll", Token::SLL},
      {"slt", Token::SLT},         {"slte", Token::SLTE},
      {"sort", Token::SORT},       {"smod", Token::SMOD},
      {"smulo", Token::SMULO},     {"sra", Token::SRA},
      {"srem", Token::SREM},       {"srl", Token::SRL},
      {"ssubo", Token::SSUBO},     {"state", Token::STATE},
      {"sub", Token::SUB},         {"uaddo", Token::UADDO},
      {"udiv", Token::UDIV},       {"uext", Token::UEXT},
      {"ugt", Token::UGT},         {"ugte", Token::UGTE},
      {"ult", Token::ULT},         {"ulte", Token::ULTE},
      {"umulo", Token::UMULO},     {"urem", Token::UREM},
      {"usubo", Token::USUBO},     {"write", Token::WRITE},
      {"xnor", Token::XNOR},       {"xor", Token::XOR},
      {"zero", Token::ZERO},
  };

  /** The classification of a character according to where it may appear. */
  enum class CharacterClass
  {
    NUMBER = (1 << 0),
    SYMBOL = (1 << 3),
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
    d_saved      = true;
    d_saved_char = ch;
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
  /** True if we have a saved character that has not been consumed yet. */
  bool d_saved = false;
  /** The saved character. */
  int32_t d_saved_char = 0;

  /** The error message. */
  std::string d_error;
};

}  // namespace parser::btor2
}  // namespace bzla

#endif
