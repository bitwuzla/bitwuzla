/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "parser/smt2/symbol_table.h"
#include "test/unit/test.h"

namespace bzla::test {

using namespace bzla::parser::smt2;

class TestSmt2SymbolTable : public ::testing::Test
{
};

TEST_F(TestSmt2SymbolTable, insert)
{
  SymbolTable table;
  table.insert(Token::SYMBOL, "x", 0);
  SymbolTable::Node* x = table.find("x");
  table.insert(Token::SYMBOL, "y", 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "x");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "y");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "x", 1);
  SymbolTable::Node* x1 = table.find("x");
  ASSERT_NE(x, x1);
  ASSERT_EQ(x1->d_symbol, "x");
  ASSERT_EQ(x1->d_assertion_level, 1);
  table.remove(x1);
  x1 = table.find("x");
  ASSERT_EQ(x, x1);
  ASSERT_EQ(x1->d_symbol, "x");
  ASSERT_EQ(x1->d_assertion_level, 0);
  table.remove(x1);
  ASSERT_EQ(table.find("x"), nullptr);
}

TEST_F(TestSmt2SymbolTable, insert_quoted1)
{
  SymbolTable table;
  table.insert(Token::SYMBOL, "x", 0);
  SymbolTable::Node* x = table.find("x");
  ASSERT_NE(x, nullptr);
  table.insert(Token::SYMBOL, "y", 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "x");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "y");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "|x|", 1);
  table.insert(Token::SYMBOL, "|y|", 1);
  table.insert(Token::SYMBOL, "| x|", 2);
  table.insert(Token::SYMBOL, "|y |", 2);
  SymbolTable::Node* x_quoted = table.find("|x|");
  ASSERT_NE(x_quoted, nullptr);
  ASSERT_NE(x, x_quoted);
  ASSERT_EQ(x_quoted->d_symbol, "|x|");
  ASSERT_EQ(x_quoted->d_assertion_level, 1);
  SymbolTable::Node* y_quoted = table.find("|y|");
  ASSERT_NE(y_quoted, nullptr);
  ASSERT_NE(y, y_quoted);
  ASSERT_EQ(y_quoted->d_symbol, "|y|");
  ASSERT_EQ(y_quoted->d_assertion_level, 1);
  SymbolTable::Node* x_new = table.find("| x|");
  ASSERT_NE(x_new, nullptr);
  ASSERT_EQ(table.find(" x"), x_new);
  ASSERT_NE(x, x_new);
  ASSERT_NE(x_quoted, x_new);
  ASSERT_EQ(x_new->d_symbol, "| x|");
  ASSERT_EQ(x_new->d_assertion_level, 2);
  SymbolTable::Node* y_new = table.find("|y |");
  ASSERT_NE(y_new, nullptr);
  ASSERT_EQ(table.find("y "), y_new);
  ASSERT_NE(y, y_new);
  ASSERT_NE(y_quoted, y_new);
  ASSERT_EQ(y_new->d_symbol, "|y |");
  ASSERT_EQ(y_new->d_assertion_level, 2);
  table.remove(x_quoted);
  x_quoted = table.find("|x|");
  assert(x_quoted != nullptr);
  ASSERT_NE(x_quoted, nullptr);
  ASSERT_EQ(x, x_quoted);
  ASSERT_EQ(x_quoted->d_symbol, "x");
  ASSERT_EQ(x_quoted->d_assertion_level, 0);
  y_quoted = table.find("|y|");
  ASSERT_NE(y_quoted, nullptr);
  ASSERT_NE(y, y_quoted);
  ASSERT_EQ(y_quoted->d_symbol, "|y|");
  ASSERT_EQ(y_quoted->d_assertion_level, 1);
  table.remove(x_new);
  ASSERT_EQ(table.find(" x"), nullptr);
}

TEST_F(TestSmt2SymbolTable, insert_quoted2)
{
  SymbolTable table;
  table.insert(Token::SYMBOL, "|x|", 0);
  SymbolTable::Node* x = table.find("x");
  ASSERT_NE(x, nullptr);
  table.insert(Token::SYMBOL, "|y|", 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "|x|");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "|y|");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "x", 1);
  table.insert(Token::SYMBOL, "|y|", 1);
  table.insert(Token::SYMBOL, " x", 2);
  table.insert(Token::SYMBOL, "y ", 2);
  SymbolTable::Node* x_quoted = table.find("|x|");
  ASSERT_NE(x_quoted, nullptr);
  ASSERT_NE(x, x_quoted);
  ASSERT_EQ(x_quoted->d_symbol, "x");
  ASSERT_EQ(x_quoted->d_assertion_level, 1);
  SymbolTable::Node* y_quoted = table.find("|y|");
  ASSERT_NE(y_quoted, nullptr);
  ASSERT_NE(y, y_quoted);
  ASSERT_EQ(y_quoted->d_symbol, "|y|");
  ASSERT_EQ(y_quoted->d_assertion_level, 1);
  SymbolTable::Node* x_new = table.find("| x|");
  ASSERT_NE(x_new, nullptr);
  ASSERT_EQ(table.find(" x"), x_new);
  ASSERT_NE(x, x_new);
  ASSERT_NE(x_quoted, x_new);
  ASSERT_EQ(x_new->d_symbol, " x");
  ASSERT_EQ(x_new->d_assertion_level, 2);
  SymbolTable::Node* y_new = table.find("|y |");
  ASSERT_NE(y_new, nullptr);
  ASSERT_EQ(table.find("y "), y_new);
  ASSERT_NE(y, y_new);
  ASSERT_NE(y_quoted, y_new);
  ASSERT_EQ(y_new->d_symbol, "y ");
  ASSERT_EQ(y_new->d_assertion_level, 2);
  table.remove(x_quoted);
  x_quoted = table.find("|x|");
  ASSERT_NE(x_quoted, nullptr);
  ASSERT_EQ(x, x_quoted);
  ASSERT_EQ(x_quoted->d_symbol, "|x|");
  ASSERT_EQ(x_quoted->d_assertion_level, 0);
  table.remove(y_quoted);
  y_quoted = table.find("|y|");
  ASSERT_NE(y_quoted, nullptr);
  ASSERT_EQ(y, y_quoted);
  ASSERT_EQ(y_quoted->d_symbol, "|y|");
  ASSERT_EQ(y_quoted->d_assertion_level, 0);
  table.remove(x_new);
  ASSERT_EQ(table.find(" x"), nullptr);
}
}  // namespace bzla::test
