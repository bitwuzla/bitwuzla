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

bool
SymbolTable::Node::has_symbol() const
{
  return !d_symbol.empty();
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

void
SymbolTable::pop_scope(uint64_t scope_level)
{
  for (auto& p : d_table)
  {
    while (p.second.back()->d_scope_level >= scope_level)
    {
      p.second.pop_back();
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
  insert(Token::REPR_RESOURCE_LIMIT);
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

void
SymbolTable::init_array_symbols()
{
  insert(Token::ARRAY);
  insert(Token::ARRAY_SELECT);
  insert(Token::ARRAY_STORE);
}

void
SymbolTable::init_bv_symbols()
{
  insert(Token::BV_BITVEC);
  insert(Token::BV_ADD);
  insert(Token::BV_AND);
  insert(Token::BV_ASHR);
  insert(Token::BV_COMP);
  insert(Token::BV_CONCAT);
  insert(Token::BV_EXTRACT);
  insert(Token::BV_LSHR);
  insert(Token::BV_MUL);
  insert(Token::BV_NAND);
  insert(Token::BV_NEG);
  insert(Token::BV_NOR);
  insert(Token::BV_NOT);
  insert(Token::BV_OR);
  insert(Token::BV_REPEAT);
  insert(Token::BV_ROTATE_LEFT);
  insert(Token::BV_ROTATE_RIGHT);
  insert(Token::BV_SDIV);
  insert(Token::BV_SGE);
  insert(Token::BV_SGT);
  insert(Token::BV_SHL);
  insert(Token::BV_SIGN_EXTEND);
  insert(Token::BV_SLE);
  insert(Token::BV_SLT);
  insert(Token::BV_SMOD);
  insert(Token::BV_SREM);
  insert(Token::BV_SUB);
  insert(Token::BV_UDIV);
  insert(Token::BV_UGE);
  insert(Token::BV_UGT);
  insert(Token::BV_ULE);
  insert(Token::BV_ULT);
  insert(Token::BV_UREM);
  insert(Token::BV_XNOR);
  insert(Token::BV_XOR);
  insert(Token::BV_ZERO_EXTEND);
  insert(Token::BV_REDOR);
  insert(Token::BV_REDAND);
  insert(Token::BV_REDXOR);
  insert(Token::BV_SADDO);
  insert(Token::BV_UADDO);
  insert(Token::BV_SDIVO);
  insert(Token::BV_SMULO);
  insert(Token::BV_UMULO);
  insert(Token::BV_SSUBO);
  insert(Token::BV_USUBO);
}

void
SymbolTable::init_fp_symbols()
{
  insert(Token::FP_FLOATINGPOINT);
  insert(Token::FP_FLOAT16);
  insert(Token::FP_FLOAT32);
  insert(Token::FP_FLOAT64);
  insert(Token::FP_FLOAT128);
  insert(Token::FP_ROUNDINGMODE);
  insert(Token::FP_RM_RNA);
  insert(Token::FP_RM_RNA_LONG);
  insert(Token::FP_RM_RNE);
  insert(Token::FP_RM_RNE_LONG);
  insert(Token::FP_RM_RTN);
  insert(Token::FP_RM_RTN_LONG);
  insert(Token::FP_RM_RTP);
  insert(Token::FP_RM_RTP_LONG);
  insert(Token::FP_RM_RTZ);
  insert(Token::FP_RM_RTZ_LONG);
  insert(Token::FP_ABS);
  insert(Token::FP_ADD);
  insert(Token::FP_DIV);
  insert(Token::FP_EQ);
  insert(Token::FP_FMA);
  insert(Token::FP_FP);
  insert(Token::FP_GEQ);
  insert(Token::FP_GT);
  insert(Token::FP_IS_INF);
  insert(Token::FP_IS_NAN);
  insert(Token::FP_IS_NEG);
  insert(Token::FP_IS_NORMAL);
  insert(Token::FP_IS_POS);
  insert(Token::FP_IS_SUBNORMAL);
  insert(Token::FP_IS_ZERO);
  insert(Token::FP_LEQ);
  insert(Token::FP_LT);
  insert(Token::FP_MAX);
  insert(Token::FP_MIN);
  insert(Token::FP_MUL);
  insert(Token::FP_NAN);
  insert(Token::FP_NEG);
  insert(Token::FP_NEG_INF);
  insert(Token::FP_NEG_ZERO);
  insert(Token::FP_POS_INF);
  insert(Token::FP_POS_ZERO);
  insert(Token::FP_REM);
  insert(Token::FP_RTI);
  insert(Token::FP_SQRT);
  insert(Token::FP_SUB);
  insert(Token::FP_TO_FP);
  insert(Token::FP_TO_FP_UNSIGNED);
  insert(Token::FP_TO_SBV);
  insert(Token::FP_TO_UBV);
  insert(Token::REAL_DIV);
}

}  // namespace parser::smt2
}  // namespace bzla
