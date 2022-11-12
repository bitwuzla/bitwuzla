#ifndef BZLA_SOLVER_FP_FP_SOLVER_H_INCLUDED
#define BZLA_SOLVER_FP_FP_SOLVER_H_INCLUDED

#include "option/option.h"
#include "solver/solver.h"

namespace bzla::fp {

class FpSolver : public Solver
{
 public:
  /** Construct default value for given floating-point type. */
  static Node default_value(const Type& type);

  FpSolver(SolvingContext& context);
  ~FpSolver();

  Result check() override;

  Node value(const Node& term) override;

 private:
};

}  // namespace bzla::fp

#endif
