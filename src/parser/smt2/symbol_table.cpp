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

void
SymbolTable::init_reserved_words()
{
  insert(Token::BANG, "!");
  insert(Token::UNDERSCORE, "_");
  insert(Token::AS, "as");
  insert(Token::BINARY_RESERVED_WORD, "BINARY");
  insert(Token::DECIMAL_RESERVED_WORD, "DECIMAL");
  insert(Token::EXISTS, "exists");
  insert(Token::HEXADECIMAL_RESERVED_WORD, "HEXADECIMAL");
  insert(Token::FORALL, "forall");
  insert(Token::LET, "let");
  insert(Token::NUMERAL_RESERVED_WORD, "NUMERAL");
  insert(Token::PAR, "par");
  insert(Token::STRING_RESERVED_WORD, "STRING");
}

void
SymbolTable::init_commands()
{
  insert(Token::ASSERT, "assert");
  insert(Token::CHECK_SAT, "check-sat");
  insert(Token::CHECK_SAT_ASSUMING, "check-sat-assuming");
  insert(Token::DECLARE_CONST, "declare-const");
  insert(Token::DECLARE_FUN, "declare-fun");
  insert(Token::DECLARE_SORT, "declare-sort");
  insert(Token::DEFINE_FUN, "define-fun");
  insert(Token::DEFINE_SORT, "define-sort");
  insert(Token::ECHO, "echo");
  insert(Token::EXIT, "exit");
  insert(Token::GET_ASSERTIONS, "get-assertions");
  insert(Token::GET_ASSIGNMENT, "get-assignment");
  insert(Token::GET_INFO, "get-info");
  insert(Token::GET_MODEL, "get-model");
  insert(Token::GET_OPTION, "get-option");
  insert(Token::GET_PROOF, "get-proof");
  insert(Token::GET_UNSAT_ASSUMPTIONS, "get-unsat-assumptions");
  insert(Token::GET_UNSAT_CORE, "get-unsat-core");
  insert(Token::GET_VALUE, "get-value");
  insert(Token::POP, "pop");
  insert(Token::PUSH, "push");
  insert(Token::RESET, "reset");
  insert(Token::RESET_ASSERTIONS, "reset-assertions");
  insert(Token::SET_INFO, "set-info");
  insert(Token::SET_LOGIC, "set-logic");
  insert(Token::SET_OPTION, "set-option");
}

void
SymbolTable::init_keywords()
{
  insert(Token::ALL_STATISTICS, ":all-statistics");
  insert(Token::AUTHORS, ":authors");
  insert(Token::ASSERTION_STACK_LEVELS, ":assertion-stack-levels");
  insert(Token::CATEGORY, ":category");
  insert(Token::CHAINABLE, ":chainable");
  insert(Token::DEFINITION, ":definition");
  insert(Token::DIAG_OUTPUT_CHANNEL, ":diagnostic-output-channel");
  insert(Token::ERROR_BEHAVIOR, ":error-behavior");
  insert(Token::EXTENSIONS, ":extensions");
  insert(Token::FUNS, ":funs");
  insert(Token::FUNS_DESCRIPTION, ":funs-description");
  insert(Token::GLOBAL_DECLARATIONS, ":global-declarations");
  insert(Token::INTERACTIVE_MODE, ":interactive-mode");
  insert(Token::LANGUAGE, ":language");
  insert(Token::LEFT_ASSOC, ":left-assoc");
  insert(Token::LICENSE, ":license");
  insert(Token::NAME, ":name");
  insert(Token::NAMED, ":named");
  insert(Token::NOTES, ":notes");
  insert(Token::PATTERN, ":pattern");
  insert(Token::PRINT_SUCCESS, ":print-success");
  insert(Token::PRODUCE_ASSIGNMENTS, ":produce-assignments");
  insert(Token::PRODUCE_MODELS, ":produce-models");
  insert(Token::PRODUCE_PROOFS, ":produce-proofs");
  insert(Token::PRODUCE_UNSAT_ASSUMPTIONS, ":produce-unsat-assumptions");
  insert(Token::PRODUCE_UNSAT_CORES, ":produce-unsat-cores");
  insert(Token::RANDOM_SEED, ":random-seed");
  insert(Token::REASON_UNKNOWN, ":reason-unknown");
  insert(Token::REGULAR_OUTPUT_CHANNEL, ":regular-output-channel");
  insert(Token::REPRODUCIBLE_RESOURCE_LIMIT, ":reproducible-resource-limit");
  insert(Token::RIGHT_ASSOC, ":right-assoc");
  insert(Token::SMTLIB_VERSION, ":smt-lib-version");
  insert(Token::SORTS, ":sorts");
  insert(Token::SORTS_DESCRIPTION, ":sorts-description");
  insert(Token::SOURCE, ":source");
  insert(Token::STATUS, ":status");
  insert(Token::THEORIES, ":theories");
  insert(Token::VALUES, ":values");
  insert(Token::VERBOSITY, ":verbosity");
  insert(Token::VERSION, ":version");
}

void
SymbolTable::init_core_symbols()
{
  insert(Token::AND, "and");
  insert(Token::BOOL, "Bool");
  insert(Token::DISTINCT, "distinct");
  insert(Token::EQUAL, "=");
  insert(Token::FALSE, "false");
  insert(Token::IMPLIES, "=>");
  insert(Token::ITE, "ite");
  insert(Token::NOT, "not");
  insert(Token::OR, "or");
  insert(Token::TRUE, "true");
  insert(Token::XOR, "xor");
}

}  // namespace parser::smt2
}  // namespace bzla
