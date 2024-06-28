/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <iostream>
#include <sstream>

#include "parser/btor2/lexer.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace bzla::parser::btor2;

class TestBtor2Lexer : public ::testing::Test
{
 protected:
  inline static constexpr const char* s_out_prefix = "/tmp/bitwuzla_regress_";
  void next_token(Lexer& lexer,
                  Token expected,
                  const std::string& expected_str = "")
  {
    Token lex_expected = Token::SYMBOL;
    if (expected == Token::NUMBER_BIN || expected == Token::NUMBER_DEC
        || expected == Token::NUMBER_HEX)
    {
      lex_expected = expected;
    }
    Token token = lexer.next_token(lex_expected);
    if (lexer.error())
    {
      std::cout << "error: " << lexer.error_msg() << std::endl;
    }
    assert(token == expected);
    ASSERT_EQ(token, expected);
    if (!expected_str.empty())
    {
      ASSERT_EQ(lexer.token(), expected_str);
    }
  }

  void open_file(const std::stringstream& input, std::ifstream& infile)
  {
    std::string infile_name = s_out_prefix + std::string("lexer.btor2");
    std::ofstream ofile(infile_name);
    ofile << input.str();
    ofile.close();
    infile.open(infile_name, std::ifstream::in);
  }
};

TEST_F(TestBtor2Lexer, comments)
{
  std::stringstream input;
  input << "   " << std::endl
        << "; foo" << std::endl
        << "; bar" << std::endl
        << "  ; foo" << std::endl
        << "    " << std::endl
        << std::endl
        << "foobar";
  std::ifstream infile;
  open_file(input, infile);
  Lexer lexer;
  lexer.init(&infile);
  next_token(lexer, Token::SYMBOL, "foobar");
  infile.close();
}

TEST_F(TestBtor2Lexer, sort)
{
  std::stringstream input;
  input << "1 sort bitvec 32";
  std::ifstream infile;
  open_file(input, infile);
  Lexer lexer;
  lexer.init(&infile);
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::SORT, "sort");
  next_token(lexer, Token::BITVEC, "bitvec");
  next_token(lexer, Token::NUMBER_DEC, "32");
  next_token(lexer, Token::ENDOFFILE);
  infile.close();
}

TEST_F(TestBtor2Lexer, input)
{
  std::stringstream input;
  input << "4 input 1 x";
  std::ifstream infile;
  open_file(input, infile);
  Lexer lexer;
  lexer.init(&infile);
  next_token(lexer, Token::NUMBER_DEC, "4");
  next_token(lexer, Token::INPUT, "input");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::SYMBOL, "x");
  next_token(lexer, Token::ENDOFFILE);
  infile.close();
}

TEST_F(TestBtor2Lexer, neg)
{
  std::stringstream input;
  input << "6 add 1 -2 -5";
  std::ifstream infile;
  open_file(input, infile);
  Lexer lexer;
  lexer.init(&infile);
  next_token(lexer, Token::NUMBER_DEC, "6");
  next_token(lexer, Token::ADD, "add");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_DEC, "-2");
  next_token(lexer, Token::NUMBER_DEC, "-5");
  next_token(lexer, Token::ENDOFFILE);
  infile.close();
}

TEST_F(TestBtor2Lexer, formula)
{
  std::stringstream input;
  input << "1 sort bitvec 32" << std::endl;
  input << "2 const 1 11111111111111111111111111111110 ; asdf" << std::endl;
  input << "; foo" << std::endl;
  input << "3 const 1 00000000000000000000000000000010" << std::endl;
  input << "4 input 1 x" << std::endl;
  input << "5 mul 1 3 4" << std::endl;
  input << "6 add 1 -2 -5" << std::endl;
  input << "7 mul 1 2 4" << std::endl;
  input << "8 sort bitvec 1" << std::endl;
  input << "9 eq 8 6 7" << std::endl;
  input << "10 constraint -9";
  std::ifstream infile;
  open_file(input, infile);
  Lexer lexer;
  lexer.init(&infile);
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::SORT, "sort");
  next_token(lexer, Token::BITVEC, "bitvec");
  next_token(lexer, Token::NUMBER_DEC, "32");
  next_token(lexer, Token::NUMBER_DEC, "2");
  next_token(lexer, Token::CONST, "const");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_BIN, "11111111111111111111111111111110");
  next_token(lexer, Token::NUMBER_DEC, "3");
  next_token(lexer, Token::CONST, "const");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_BIN, "00000000000000000000000000000010");
  next_token(lexer, Token::NUMBER_DEC, "4");
  next_token(lexer, Token::INPUT, "input");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::SYMBOL, "x");
  next_token(lexer, Token::NUMBER_DEC, "5");
  next_token(lexer, Token::MUL, "mul");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_DEC, "3");
  next_token(lexer, Token::NUMBER_DEC, "4");
  next_token(lexer, Token::NUMBER_DEC, "6");
  next_token(lexer, Token::ADD, "add");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_DEC, "-2");
  next_token(lexer, Token::NUMBER_DEC, "-5");
  next_token(lexer, Token::NUMBER_DEC, "7");
  next_token(lexer, Token::MUL, "mul");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_DEC, "2");
  next_token(lexer, Token::NUMBER_DEC, "4");
  next_token(lexer, Token::NUMBER_DEC, "8");
  next_token(lexer, Token::SORT, "sort");
  next_token(lexer, Token::BITVEC, "bitvec");
  next_token(lexer, Token::NUMBER_DEC, "1");
  next_token(lexer, Token::NUMBER_DEC, "9");
  next_token(lexer, Token::EQ, "eq");
  next_token(lexer, Token::NUMBER_DEC, "8");
  next_token(lexer, Token::NUMBER_DEC, "6");
  next_token(lexer, Token::NUMBER_DEC, "7");
  next_token(lexer, Token::NUMBER_DEC, "10");
  next_token(lexer, Token::CONSTRAINT, "constraint");
  next_token(lexer, Token::NUMBER_DEC, "-9");
  next_token(lexer, Token::ENDOFFILE);
  infile.close();
}
}  // namespace bzla::test
