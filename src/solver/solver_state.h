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

#include "node/node.h"

namespace bzla {

namespace backtrack {
class BacktrackManager;
}

class SolverEngine;

class SolverState
{
 public:
  SolverState(SolverEngine& solver_engine);

  /** Get value of given term. Queries corresponding solver for value. */
  Node value(const Node& term);

  /** Add a lemma. */
  void lemma(const Node& lemma);

  /** @return Solver engine backtrack manager. */
  backtrack::BacktrackManager* backtrack_mgr();

 private:
  /** Associated solver engine. */
  SolverEngine& d_solver_engine;
};

}  // namespace bzla

#endif
