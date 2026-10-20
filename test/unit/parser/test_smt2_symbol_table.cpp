/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <string_view>

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
  table.insert(Token::SYMBOL, "x", false, 0);
  SymbolTable::Node* x = table.find("x");
  table.insert(Token::SYMBOL, "y", false, 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "x");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "y");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "x", false, 1);
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
  table.insert(Token::SYMBOL, "x", false, 0);
  SymbolTable::Node* x = table.find("x");
  ASSERT_NE(x, nullptr);
  table.insert(Token::SYMBOL, "y", false, 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "x");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "y");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "|x|", false, 1);
  table.insert(Token::SYMBOL, "|y|", false, 1);
  table.insert(Token::SYMBOL, "| x|", false, 2);
  table.insert(Token::SYMBOL, "|y |", false, 2);
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
  table.insert(Token::SYMBOL, "|x|", false, 0);
  SymbolTable::Node* x = table.find("x");
  ASSERT_NE(x, nullptr);
  table.insert(Token::SYMBOL, "|y|", false, 0);
  SymbolTable::Node* y = table.find("y");
  ASSERT_NE(y, nullptr);
  ASSERT_NE(x, y);
  ASSERT_EQ(x->d_symbol, "|x|");
  ASSERT_EQ(x->d_assertion_level, 0);
  ASSERT_EQ(y->d_symbol, "|y|");
  ASSERT_EQ(y->d_assertion_level, 0);
  table.insert(Token::SYMBOL, "x", false, 1);
  table.insert(Token::SYMBOL, "|y|", false, 1);
  table.insert(Token::SYMBOL, " x", false, 2);
  table.insert(Token::SYMBOL, "y ", false, 2);
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

// Lookups must be possible without constructing a heap std::string for the
// key (transparent/heterogeneous find). This guards the string_view-based
// find against accidentally reintroducing a per-token std::string temporary
// and against relying on null-termination at the symbol boundary.
TEST_F(TestSmt2SymbolTable, find_transparent)
{
  SymbolTable table;
  table.insert(Token::SYMBOL, "foo", false, 0);
  table.insert(Token::SYMBOL, "bar", false, 0);
  SymbolTable::Node* foo = table.find("foo");
  ASSERT_NE(foo, nullptr);

  // Look up via a string_view into a larger buffer: the view ends at the
  // symbol boundary even though the underlying buffer continues, so the
  // lookup must not read past the view (no null-termination assumption) and
  // must not allocate a std::string.
  std::string buf = "fooBAR";
  ASSERT_EQ(table.find(std::string_view(buf.data(), 3)), foo);

  // const char* lookups resolve without an intermediate std::string.
  ASSERT_EQ(table.find("bar")->d_symbol, "bar");
  ASSERT_EQ(table.find(std::string_view("baz")), nullptr);

  // Quoted/unquoted equivalence still holds through the transparent
  // comparator, again with a non-null-terminated string_view ("|foo|").
  std::string qbuf = "|foo|baz";
  ASSERT_EQ(table.find(std::string_view(qbuf.data(), 5)), foo);
}

// Quoted reserved words and keywords are symbols distinct from the reserved
// word or keyword, only quoted simple symbols equal their unquoted version.
TEST_F(TestSmt2SymbolTable, quoted_reserved)
{
  SymbolTable table;
  for (const char* s : {"|par|", "|assert|", "|:named|", "|_|"})
  {
    ASSERT_EQ(table.find(s), nullptr);
  }
  SymbolTable::Node* par    = table.find("par");
  SymbolTable::Node* assert = table.find("assert");
  SymbolTable::Node* named  = table.find(":named");
  ASSERT_EQ(par->d_token, Token::PAR);
  ASSERT_EQ(assert->d_token, Token::ASSERT);
  ASSERT_EQ(named->d_token, Token::NAMED);

  table.insert(Token::SYMBOL, "|par|", false, 0);
  table.insert(Token::SYMBOL, "|:named|", false, 0);
  SymbolTable::Node* qpar   = table.find("|par|");
  SymbolTable::Node* qnamed = table.find("|:named|");
  ASSERT_NE(qpar, nullptr);
  ASSERT_NE(qnamed, nullptr);
  ASSERT_EQ(qpar->d_token, Token::SYMBOL);
  ASSERT_EQ(qnamed->d_token, Token::SYMBOL);
  ASSERT_EQ(table.find("par"), par);
  ASSERT_EQ(table.find(":named"), named);
  ASSERT_EQ(table.find("|assert|"), nullptr);

  // shadowing and removal of quoted reserved words
  table.insert(Token::SYMBOL, "|par|", false, 1);
  SymbolTable::Node* qpar1 = table.find("|par|");
  ASSERT_NE(qpar1, qpar);
  ASSERT_EQ(qpar1->d_assertion_level, 1);
  table.pop_level(1);
  ASSERT_EQ(table.find("|par|"), qpar);
  table.remove(qpar);
  ASSERT_EQ(table.find("|par|"), nullptr);
  ASSERT_EQ(table.find("par"), par);

  // keywords not known to the table are inserted when parsed, in any order
  // relative to the quoted symbol
  table.insert(Token::ATTRIBUTE, ":foo", false, 0);
  ASSERT_EQ(table.find("|:foo|"), nullptr);
  table.insert(Token::SYMBOL, "|:foo|", false, 0);
  table.insert(Token::SYMBOL, "|:bar|", false, 0);
  ASSERT_EQ(table.find(":foo")->d_token, Token::ATTRIBUTE);
  ASSERT_EQ(table.find("|:foo|")->d_token, Token::SYMBOL);
  ASSERT_EQ(table.find(":bar"), nullptr);

  // theory symbols are simple symbols
  table.init_bv_symbols();
  ASSERT_EQ(table.find("|bvadd|"), table.find("bvadd"));
  ASSERT_EQ(table.find("|bvadd|")->d_token, Token::BV_ADD);
}
}  // namespace bzla::test
