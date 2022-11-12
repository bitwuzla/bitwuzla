#include "solver/fp/fp_solver.h"

#include "node/node_manager.h"
#include "solver/fp/floating_point.h"
#include "solver/fp/rounding_mode.h"

namespace bzla::fp {

Node
FpSolver::default_value(const Type& type)
{
  NodeManager& nm = NodeManager::get();
  if (type.is_fp())
  {
    return nm.mk_value(FloatingPoint::fpzero(type, false));
  }
  assert(type.is_rm());
  return nm.mk_value(RoundingMode::RNE);
}

FpSolver::FpSolver(SolvingContext& context) : Solver(context)
{
  // TODO
}

FpSolver::~FpSolver() {}

Result
FpSolver::check()
{
  // TODO
}

Node
FpSolver::value(const Node& term)
{
  // TODO
}

}  // namespace bzla::fp
