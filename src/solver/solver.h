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

#include <cassert>
#include <vector>

#include "node/node.h"
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

  virtual void register_eq_heuristic(const std::vector<Node>& nodes)
  {
    (void) nodes;
  }

  virtual void register_distinct_heuristic(const std::vector<Node>& nodes)
  {
    (void) nodes;
  }

 protected:
  /** Associated environment. */
  Env& d_env;
  /** Logger instance. */
  util::Logger& d_logger;
  /** Associated solver state. */
  SolverState& d_solver_state;
};

}  // namespace bzla
#endif
