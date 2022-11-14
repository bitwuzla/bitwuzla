#ifndef BZLA_SOLVER_SOLVER_H_INCLUDED
#define BZLA_SOLVER_SOLVER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"
#include "solver/result.h"

namespace bzla {

class SolverEngine;

class Solver
{
 public:
  Solver(SolverEngine& solver_engine) : d_solver_engine(solver_engine){};

  /** Check satisfiability for current solving context. */
  virtual Result check() = 0;

  /** Compute value for given term. */
  virtual Node value(const Node& term) = 0;

  /** Register term relevant to this solver. */
  virtual void register_term(const Node& term){};

 protected:
  /** Associated solver engine. */
  SolverEngine& d_solver_engine;

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
