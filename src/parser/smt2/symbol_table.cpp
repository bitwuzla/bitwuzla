#include "parser/smt2/symbol_table.h"

#include <cassert>

namespace bzla {
namespace parser::smt2 {

SymbolTable::Node::Node(Token token,
                        const std::string& symbol,
                        uint64_t scope_level)
    : d_token(token),
      d_is_bound(false),
      d_is_sort(false),
      d_scope_level(scope_level),
      d_coo({0, 0}),
      d_symbol(symbol)
{
}

SymbolTable::Node*
SymbolTable::insert(Token token,
                    const std::string& symbol,
                    uint64_t scope_level)
{
  Node* node;
  if (symbol[0] == '|' && symbol[symbol.size() - 1] == '|')
  {
    std::string sym = symbol.substr(1, symbol.size() - 2);
    node            = new Node(token, sym, scope_level);
    d_table[sym].emplace_back(node);
  }
  else
  {
    node = new Node(token, symbol, scope_level);
    d_table[symbol].emplace_back(node);
  }
  return node;
}

void
SymbolTable::remove(Node* node)
{
  const std::string& symbol = node->d_symbol;
  assert(d_table.find(symbol) != d_table.end());
  auto& chain = d_table.find(symbol)->second;
  assert(chain.size() > 0);
  for (size_t i = 0, size = chain.size(); i < size; ++i)
  {
    size_t idx = size - i - 1;
    Node* n    = chain[idx].get();
    if (node == n)
    {
      assert(n->d_symbol == symbol);
      chain.erase(chain.begin() + idx);
      break;
    }
  }
}

SymbolTable::Node*
SymbolTable::find(const std::string& symbol) const
{
  auto it = d_table.find(symbol[0] == '|' && symbol[symbol.size() - 1] == '|'
                             ? symbol.substr(1, symbol.size() - 2)
                             : symbol);
  if (it == d_table.end())
  {
    return nullptr;
  }

  const std::string& sym = it->first;
  auto& chain            = it->second;
  if (chain.size() == 0)
  {
    return nullptr;
  }

  for (size_t i = 0, size = chain.size(); i < size; ++i)
  {
    size_t idx = size - i - 1;
    Node* n    = chain[idx].get();
    if (n->d_symbol == sym)
    {
      return n;
    }
  }
  return nullptr;
}

/* SymbolTable private ------------------------------------------------------ */

SymbolTable::Node*
SymbolTable::insert(Token token)
{
  insert(token, std::to_string(token));
}

void
SymbolTable::init_reserved_words()
{
  insert(Token::BANG);
  insert(Token::UNDERSCORE);
  insert(Token::AS);
  insert(Token::BINARY_RESERVED_WORD);
  insert(Token::DECIMAL_RESERVED_WORD);
  insert(Token::EXISTS);
  insert(Token::HEXADECIMAL_RESERVED_WORD);
  insert(Token::FORALL);
  insert(Token::LET);
  insert(Token::NUMERAL_RESERVED_WORD);
  insert(Token::PAR);
  insert(Token::STRING_RESERVED_WORD);
}

void
SymbolTable::init_commands()
{
  insert(Token::ASSERT);
  insert(Token::CHECK_SAT);
  insert(Token::CHECK_SAT_ASSUMING);
  insert(Token::DECLARE_CONST);
  insert(Token::DECLARE_FUN);
  insert(Token::DECLARE_SORT);
  insert(Token::DEFINE_FUN);
  insert(Token::DEFINE_SORT);
  insert(Token::ECHO);
  insert(Token::EXIT);
  insert(Token::GET_ASSERTIONS);
  insert(Token::GET_ASSIGNMENT);
  insert(Token::GET_INFO);
  insert(Token::GET_MODEL);
  insert(Token::GET_OPTION);
  insert(Token::GET_PROOF);
  insert(Token::GET_UNSAT_ASSUMPTIONS);
  insert(Token::GET_UNSAT_CORE);
  insert(Token::GET_VALUE);
  insert(Token::POP);
  insert(Token::PUSH);
  insert(Token::RESET);
  insert(Token::RESET_ASSERTIONS);
  insert(Token::SET_INFO);
  insert(Token::SET_LOGIC);
  insert(Token::SET_OPTION);
}

void
SymbolTable::init_keywords()
{
  insert(Token::ALL_STATISTICS);
  insert(Token::AUTHORS);
  insert(Token::ASSERTION_STACK_LEVELS);
  insert(Token::CATEGORY);
  insert(Token::CHAINABLE);
  insert(Token::DEFINITION);
  insert(Token::DIAG_OUTPUT_CHANNEL);
  insert(Token::ERROR_BEHAVIOR);
  insert(Token::EXTENSIONS);
  insert(Token::FUNS);
  insert(Token::FUNS_DESCRIPTION);
  insert(Token::GLOBAL_DECLARATIONS);
  insert(Token::INTERACTIVE_MODE);
  insert(Token::LANGUAGE);
  insert(Token::LEFT_ASSOC);
  insert(Token::LICENSE);
  insert(Token::NAME);
  insert(Token::NAMED);
  insert(Token::NOTES);
  insert(Token::PATTERN);
  insert(Token::PRINT_SUCCESS);
  insert(Token::PRODUCE_ASSIGNMENTS);
  insert(Token::PRODUCE_MODELS);
  insert(Token::PRODUCE_PROOFS);
  insert(Token::PRODUCE_UNSAT_ASSUMPTIONS);
  insert(Token::PRODUCE_UNSAT_CORES);
  insert(Token::RANDOM_SEED);
  insert(Token::REASON_UNKNOWN);
  insert(Token::REGULAR_OUTPUT_CHANNEL);
  insert(Token::REPRODUCIBLE_RESOURCE_LIMIT);
  insert(Token::RIGHT_ASSOC);
  insert(Token::SMTLIB_VERSION);
  insert(Token::SORTS);
  insert(Token::SORTS_DESCRIPTION);
  insert(Token::SOURCE);
  insert(Token::STATUS);
  insert(Token::THEORIES);
  insert(Token::VALUES);
  insert(Token::VERBOSITY);
  insert(Token::VERSION);
}

void
SymbolTable::init_core_symbols()
{
  insert(Token::AND);
  insert(Token::BOOL);
  insert(Token::DISTINCT);
  insert(Token::EQUAL);
  insert(Token::FALSE);
  insert(Token::IMPLIES);
  insert(Token::ITE);
  insert(Token::NOT);
  insert(Token::OR);
  insert(Token::TRUE);
  insert(Token::XOR);
}

}  // namespace parser::smt2
}  // namespace bzla
