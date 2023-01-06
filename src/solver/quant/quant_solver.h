#ifndef BZLA_SOLVER_QUANT_QUANT_SOLVER_H_INCLUDED
#define BZLA_SOLVER_QUANT_QUANT_SOLVER_H_INCLUDED

#include "backtrack/vector.h"
#include "solver/solver.h"

namespace bzla::quant {

class QuantSolver : public Solver
{
 public:
  /**
   * Determine if given term is a leaf node for other solvers than the
   * quant solver.
   * @param term The term to query.
   */
  static bool is_theory_leaf(const Node& term);

  QuantSolver(Env& env, SolverState& state);
  ~QuantSolver();

  void check() override;

  Node value(const Node& term) override;

  void register_term(const Node& term) override;

 private:
  backtrack::vector<Node> d_quantifiers;
};

}  // namespace bzla::quant

#endif
