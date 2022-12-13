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

void
SolverState::lemma(const Node& lemma)
{
  d_solver_engine.lemma(lemma);
}

backtrack::BacktrackManager*
SolverState::backtrack_mgr()
{
  return d_solver_engine.backtrack_mgr();
}

}  // namespace bzla
