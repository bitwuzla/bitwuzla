#ifndef BZLA_SOLVER_FP_FP_SOLVER_H_INCLUDED
#define BZLA_SOLVER_FP_FP_SOLVER_H_INCLUDED

#include "solver/fp/word_blaster.h"
#include "solver/solver.h"

namespace bzla::fp {

class FpSolver : public Solver
{
 public:
  /** Determine if `term` is a leaf node for the floating-point solver. */
  static bool is_leaf(const Node& term);
  /** Construct default value for given floating-point type. */
  static Node default_value(const Type& type);

  FpSolver(Env& env, SolverState& state);
  ~FpSolver();

  void check() override;

  Node value(const Node& term) override;

  void register_term(const Node& term) override;

 private:
  /** The word blaster. */
  WordBlaster d_word_blaster;
  /** The current queue of nodes to word-blast on the next check() call. */
  std::vector<Node> d_word_blast_queue;
};

}  // namespace bzla::fp

#endif
