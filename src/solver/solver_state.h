/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_SOLVER_STATE_H_INCLUDED
#define BZLA_SOLVER_SOLVER_STATE_H_INCLUDED

#include "backtrack/unordered_set.h"
#include "node/node.h"

namespace bzla {

namespace backtrack {
class BacktrackManager;
}
namespace fp {
class FpSolver;
}

class SolverEngine;

class SolverState
{
 public:
  SolverState(SolverEngine& solver_engine);

  /** Get value of given term. Queries corresponding solver for value. */
  Node value(const Node& term);

  /** Add a lemma. */
  bool lemma(const Node& lemma);

  /** @return Solver engine backtrack manager. */
  backtrack::BacktrackManager* backtrack_mgr();

  /** Throw Unsupported exception to terminate solver. */
  void unsupported(const std::string& msg);

  /** Print solver engine statistics. */
  void print_statistics();

  /** @return The associated floating-point solver instance. */
  const fp::FpSolver& fp_solver() const;

  /** @return The current set of lemmas. */
  const backtrack::unordered_set<Node>& lemma_cache() const;

 private:
  /** Associated solver engine. */
  SolverEngine& d_solver_engine;
};

}  // namespace bzla

#endif
