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

void
SymbolTable::insert(Token token,
                    const std::string& symbol,
                    uint64_t scope_level)
{
  if (symbol[0] == '|' && symbol[symbol.size() - 1] == '|')
  {
    std::string sym = symbol.substr(1, symbol.size() - 2);
    d_table[sym].emplace_back(new Node(token, sym, scope_level));
  }
  else
  {
    d_table[symbol].emplace_back(new Node(token, symbol, scope_level));
  }
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

}  // namespace parser::smt2
}  // namespace bzla
