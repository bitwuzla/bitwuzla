#include "solver.h"

namespace bzla {

void
Solver::cache_value(const Node& term, const Node& value)
{
  d_value_cache.emplace(term, value);
}

const Node&
Solver::get_cached_value(const Node& term) const
{
  auto it = d_value_cache.find(term);
  if (it == d_value_cache.end())
  {
    static Node null_term;
    return null_term;
  }
  return it->second;
}

}  // namespace bzla
