#ifndef BZLA_SOLVER_SOLVER_H_INCLUDED
#define BZLA_SOLVER_SOLVER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"
#include "solver/result.h"

namespace bzla {

class SolvingContext;

class Solver
{
 public:
  Solver(SolvingContext& context) : d_context(context){};

  /** Check satisfiability for current solving context. */
  virtual Result check() = 0;

  /** Compute value for given term. */
  virtual Node value(const Node& term) = 0;

 protected:
  /** Associated solving context. */
  SolvingContext& d_context;

  /**
   * Store value for term.
   *
   * @param term Term to store the cached value for.
   * @param value The value to cache.
   */
  void cache_value(const Node& term, const Node& value);

  /**
   * Get cached value for term.
   *
   * @param term Term to get the cached value for.
   * @return Cached value if term was cached, otherwise null term.
   */
  const Node& get_cached_value(const Node& term) const;

 private:
  /** Cache to store computed values. */
  std::unordered_map<Node, Node> d_value_cache;
};

}  // namespace bzla
#endif
