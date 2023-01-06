#include "solver/quant/quant_solver.h"

#include "node/node.h"

namespace bzla::quant {

using namespace node;

/* --- QuantSolver public --------------------------------------------------- */

bool
QuantSolver::is_theory_leaf(const Node& term)
{
  return term.kind() == Kind::FORALL;
}

QuantSolver::QuantSolver(Env& env, SolverState& state)
    : Solver(env, state), d_quantifiers(state.backtrack_mgr())
{
}

QuantSolver::~QuantSolver() {}

void
QuantSolver::check()
{
  assert(d_quantifiers.empty());
}

Node
QuantSolver::value(const Node& term)
{
  assert(false);
  return Node();
}

void
QuantSolver::register_term(const Node& term)
{
  assert(term.kind() == Kind::FORALL);
  d_quantifiers.push_back(term);
}

/* --- QuantSolver private -------------------------------------------------- */

}  // namespace bzla::quant
