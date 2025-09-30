/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/solver_state.h"

#include "solver/fp/fp_solver.h"
#include "solver/solver.h"
#include "solver/solver_engine.h"
#include "util/exceptions.h"

namespace bzla {

SolverState::SolverState(SolverEngine& solver_engine)
    : d_solver_engine(solver_engine)
{
}

Node
SolverState::value(const Node& term)
{
  return d_solver_engine.value(term);
}

bool
SolverState::lemma(const Node& lemma)
{
  return d_solver_engine.lemma(lemma);
}

backtrack::BacktrackManager*
SolverState::backtrack_mgr()
{
  return d_solver_engine.backtrack_mgr();
}

void
SolverState::unsupported(const std::string& msg)
{
  throw Unsupported(msg);
}

void
SolverState::print_statistics()
{
  d_solver_engine.print_statistics();
}

const fp::FpSolver&
SolverState::fp_solver() const
{
  return d_solver_engine.fp_solver();
}

const backtrack::unordered_set<Node>&
SolverState::lemma_cache() const
{
  return d_solver_engine.lemma_cache();
}

}  // namespace bzla
