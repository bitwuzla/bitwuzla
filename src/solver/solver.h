/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_SOLVER_H_INCLUDED
#define BZLA_SOLVER_SOLVER_H_INCLUDED

#include <unordered_map>

#include "node/node.h"
#include "solver/result.h"
#include "solver/solver_state.h"

namespace bzla {

namespace util {
class Logger;
}

class Env;

class Solver
{
 public:
  Solver(Env& env, SolverState& state);
  virtual ~Solver(){};

  /**
   * Check theory consistency of current solving context.
   *
   * @return True if solver check is complete.
   */
  virtual bool check() { assert(false); return false; };

  /** Compute value for given term. */
  virtual Node value(const Node& term) = 0;

  /** Register term relevant to this solver. */
  virtual void register_term(const Node& term)
  {
    (void) term;
    assert(false);
  }

 protected:
  /** Associated environment. */
  Env& d_env;
  /** Logger instance. */
  util::Logger& d_logger;

  /** Associated solver state. */
  SolverState& d_solver_state;

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

  /** Reset value cache. */
  void reset_cached_values();

 private:
  /** Cache to store computed values. */
  std::unordered_map<Node, Node> d_value_cache;
};

}  // namespace bzla
#endif
