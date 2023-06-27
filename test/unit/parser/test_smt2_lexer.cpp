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

#include "parser/smt2/lexer.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace bzla::parser::smt2;

class TestSmt2Lexer : public ::testing::Test
{
 protected:
  inline static constexpr const char* s_out_prefix = "/tmp/bitwuzla_regress_";
  void next_token(Lexer& lexer,
                  Token expected,
                  const std::string& expected_str = "")
  {
    Token token = lexer.next_token();
    if (lexer.error())
    {
      std::cout << "error: " << lexer.error_msg() << std::endl;
    }
    ASSERT_EQ(token, expected);
    if (!expected_str.empty())
    {
      ASSERT_EQ(lexer.token(), expected_str);
    }
  }

  FILE* open_file(const std::stringstream& input)
  {
    std::string infile_name = s_out_prefix + std::string("lexer.smt2");
    std::ofstream ofile(infile_name);
    ofile << input.str();
    ofile.close();
    return fopen(infile_name.c_str(), "r");
  }
};

TEST_F(TestSmt2Lexer, comments)
{
  std::stringstream input;
  input << "   " << std::endl
        << "; foo" << std::endl
        << "; bar" << std::endl
        << "  ; foo" << std::endl
        << "    " << std::endl
        << std::endl
        << "foobar";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::SYMBOL, "foobar");
}

TEST_F(TestSmt2Lexer, command1)
{
  std::stringstream input;
  input << "(declare-fun a () (_ BitVec 1))";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "declare-fun");
  next_token(lexer, Token::SYMBOL, "a");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "BitVec");
  next_token(lexer, Token::DECIMAL_VALUE, "1");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command2)
{
  std::stringstream input;
  input << "(assert (bvsle a b))";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "assert");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "bvsle");
  next_token(lexer, Token::SYMBOL, "a");
  next_token(lexer, Token::SYMBOL, "b");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command3)
{
  std::stringstream input;
  input << "(assert (= e (fp #b0 #b011 #b0000)))";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "assert");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "=");
  next_token(lexer, Token::SYMBOL, "e");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp");
  next_token(lexer, Token::BINARY_VALUE, "#b0");
  next_token(lexer, Token::BINARY_VALUE, "#b011");
  next_token(lexer, Token::BINARY_VALUE, "#b0000");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command4)
{
  std::stringstream input;
  input << "(set-info :source |" << std::endl
        << "of 10 clock cycles." << std::endl
        << "Fifo inputs: 'enqueue', (active low)" << std::endl
        << "Bit-width: 32" << std::endl
        << std::endl
        << "(foo.bar@gmail.com)." << std::endl
        << "|)";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "set-info");
  next_token(lexer, Token::ATTRIBUTE, ":source");
  next_token(lexer,
             Token::SYMBOL,
             "|\nof 10 clock cycles.\nFifo inputs: 'enqueue', (active "
             "low)\nBit-width: 32\n\n(foo.bar@gmail.com).\n|");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command5)
{
  std::stringstream input;
  input << "(get-value (((_ to_fp 5 11) RTP (/ 1.2 5)))";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "get-value");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "to_fp");
  next_token(lexer, Token::DECIMAL_VALUE, "5");
  next_token(lexer, Token::DECIMAL_VALUE, "11");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "RTP");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "/");
  next_token(lexer, Token::REAL_VALUE, "1.2");
  next_token(lexer, Token::DECIMAL_VALUE, "5");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
}

TEST_F(TestSmt2Lexer, input1)
{
  std::stringstream input;
  input << "(set-info :status unsat)" << std::endl
        << "(declare-const y (_ FloatingPoint 8 24))" << std::endl
        << "(assert" << std::endl
        << " (distinct" << std::endl
        << "  ((_ fp.to_ubv 32) roundTowardZero y)" << std::endl
        << "  ((_ fp.to_ubv 32) roundTowardZero (fp.add roundTowardPositive y "
           "(_ +zero 8 24)))"
        << std::endl
        << " )" << std::endl
        << ")" << std::endl
        << "(check-sat)" << std::endl;
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "set-info");
  next_token(lexer, Token::ATTRIBUTE, ":status");
  next_token(lexer, Token::SYMBOL, "unsat");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "declare-const");
  next_token(lexer, Token::SYMBOL, "y");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "FloatingPoint");
  next_token(lexer, Token::DECIMAL_VALUE, "8");
  next_token(lexer, Token::DECIMAL_VALUE, "24");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "assert");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "distinct");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "fp.to_ubv");
  next_token(lexer, Token::DECIMAL_VALUE, "32");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "roundTowardZero");
  next_token(lexer, Token::SYMBOL, "y");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "fp.to_ubv");
  next_token(lexer, Token::DECIMAL_VALUE, "32");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "roundTowardZero");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp.add");
  next_token(lexer, Token::SYMBOL, "roundTowardPositive");
  next_token(lexer, Token::SYMBOL, "y");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "+zero");
  next_token(lexer, Token::DECIMAL_VALUE, "8");
  next_token(lexer, Token::DECIMAL_VALUE, "24");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "check-sat");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, input2)
{
  std::stringstream input;
  input << "(declare-fun ~ () Float64)" << std::endl
        << "(assert (= x (fp.add c ~ (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))";
  FILE* infile = open_file(input);
  Lexer lexer(infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "declare-fun");
  next_token(lexer, Token::SYMBOL, "~");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "Float64");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "assert");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "=");
  next_token(lexer, Token::SYMBOL, "x");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp.add");
  next_token(lexer, Token::SYMBOL, "c");
  next_token(lexer, Token::SYMBOL, "~");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "bv0");
  next_token(lexer, Token::DECIMAL_VALUE, "1");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "bv0");
  next_token(lexer, Token::DECIMAL_VALUE, "11");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "bv0");
  next_token(lexer, Token::DECIMAL_VALUE, "52");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

}  // namespace bzla::test
