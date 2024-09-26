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

#include "solver/solver_engine.h"

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

bool
SolverState::is_relevant(const Node& term) const
{
  return d_solver_engine.is_relevant(term);
}

void
SolverState::unsupported(const std::string& msg)
{
  throw UnsupportedException(msg);
}

void
SolverState::print_statistics()
{
  d_solver_engine.print_statistics();
}

void
SolverState::process_term(const Node& term)
{
  d_solver_engine.process_term(term, true);
}

}  // namespace bzla
