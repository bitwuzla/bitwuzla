#include "solver.h"

#include "env.h"

namespace bzla {

Solver::Solver(Env& env, SolverState& state)
    : d_env(env), d_logger(env.logger()), d_solver_state(state){};

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

void
Solver::reset_cached_values()
{
  d_value_cache.clear();
}

}  // namespace bzla
