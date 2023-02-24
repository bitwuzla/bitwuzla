#include "parser/smt2/symbol_table.h"

namespace bzla {
namespace parser::smt2 {

SymbolTable::Node::Node(Token token,
                        const std::string& name,
                        uint64_t scope_level)
    : d_token(token),
      d_is_bound(false),
      d_is_sort(false),
      d_scope_level(scope_level),
      d_coo({0, 0}),
      d_name(name)
{
}

void
SymbolTable::insert(Token token, const std::string& name, uint64_t scope_level)
{
  d_table[name].emplace_back(token, name, scope_level);
}

}  // namespace parser::smt2
}  // namespace bzla
