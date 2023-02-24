#include <iostream>
#include <sstream>

#include "parser/smt2/lexer.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace bzla::parser::smt2;

class TestSmt2Lexer : public ::testing::Test
{
 protected:
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
};

TEST_F(TestSmt2Lexer, comments)
{
  std::stringstream infile;
  infile << "   " << std::endl
         << "; foo" << std::endl
         << "; bar" << std::endl
         << "  ; foo" << std::endl
         << "    " << std::endl
         << std::endl
         << "foobar";
  Lexer lexer(&infile);
  next_token(lexer, Token::SYMBOL, "foobar");
}

TEST_F(TestSmt2Lexer, command1)
{
  std::stringstream infile;
  infile << "(declare-fun a () (_ BitVec 1))";
  Lexer lexer(&infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "declare-fun");
  next_token(lexer, Token::SYMBOL, "a");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "BitVec");
  next_token(lexer, Token::DECIMAL_CONSTANT, "1");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command2)
{
  std::stringstream infile;
  infile << "(assert (bvsle a b))";
  Lexer lexer(&infile);
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
  std::stringstream infile;
  infile << "(assert (= e (fp #b0 #b011 #b0000)))";
  Lexer lexer(&infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "assert");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "=");
  next_token(lexer, Token::SYMBOL, "e");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp");
  next_token(lexer, Token::BINARY_CONSTANT, "#b0");
  next_token(lexer, Token::BINARY_CONSTANT, "#b011");
  next_token(lexer, Token::BINARY_CONSTANT, "#b0000");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

TEST_F(TestSmt2Lexer, command4)
{
  std::stringstream infile;
  infile << "(set-info :source |" << std::endl
         << "of 10 clock cycles." << std::endl
         << "Fifo inputs: 'enqueue', (active low)" << std::endl
         << "Bit-width: 32" << std::endl
         << std::endl
         << "(foo.bar@gmail.com)." << std::endl
         << "|)";
  Lexer lexer(&infile);
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
  std::stringstream infile;
  infile << "(get-value (((_ to_fp 5 11) RTP (/ 1.2 5)))";
  Lexer lexer(&infile);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "get-value");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "to_fp");
  next_token(lexer, Token::DECIMAL_CONSTANT, "5");
  next_token(lexer, Token::DECIMAL_CONSTANT, "11");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "RTP");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "/");
  next_token(lexer, Token::REAL_CONSTANT, "1.2");
  next_token(lexer, Token::DECIMAL_CONSTANT, "5");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
}

TEST_F(TestSmt2Lexer, input1)
{
  std::stringstream infile;
  infile << "(set-info :status unsat)" << std::endl
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
  Lexer lexer(&infile);
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
  next_token(lexer, Token::DECIMAL_CONSTANT, "8");
  next_token(lexer, Token::DECIMAL_CONSTANT, "24");
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
  next_token(lexer, Token::DECIMAL_CONSTANT, "32");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "roundTowardZero");
  next_token(lexer, Token::SYMBOL, "y");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "fp.to_ubv");
  next_token(lexer, Token::DECIMAL_CONSTANT, "32");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::SYMBOL, "roundTowardZero");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::SYMBOL, "fp.add");
  next_token(lexer, Token::SYMBOL, "roundTowardPositive");
  next_token(lexer, Token::SYMBOL, "y");
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "+zero");
  next_token(lexer, Token::DECIMAL_CONSTANT, "8");
  next_token(lexer, Token::DECIMAL_CONSTANT, "24");
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
  std::stringstream infile;
  infile << "(declare-fun ~ () Float64)" << std::endl
         << "(assert (= x (fp.add c ~ (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)))))";
  Lexer lexer(&infile);
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
  next_token(lexer, Token::DECIMAL_CONSTANT, "1");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "bv0");
  next_token(lexer, Token::DECIMAL_CONSTANT, "11");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::LPAR);
  next_token(lexer, Token::UNDERSCORE);
  next_token(lexer, Token::SYMBOL, "bv0");
  next_token(lexer, Token::DECIMAL_CONSTANT, "52");
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::RPAR);
  next_token(lexer, Token::ENDOFFILE);
}

}  // namespace bzla::test
