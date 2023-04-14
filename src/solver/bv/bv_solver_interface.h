#ifndef BZLA_SOLVER_BV_BV_SOLVER_INTERFACE_H_INCLUDED
#define BZLA_SOLVER_BV_BV_SOLVER_INTERFACE_H_INCLUDED

#include "node/node.h"
#include "solver/result.h"

namespace bzla::bv {

/**
 * Required interface for bit-vector solvers.
 *
 * Bit-vector solvers are the only solvers that handle the Boolean skeleton
 * in addition to the bit-vector terms and therefore need additional methods
 * to handle assertions (and solve them).
 */
class BvSolverInterface
{
 public:
  virtual ~BvSolverInterface(){};
  /** Register assertion in current scope level. */
  virtual void register_assertion(const Node& assertion,
                                  bool top_level,
                                  bool is_lemma) = 0;
  /** Solve current set of registered assertions. */
  virtual Result solve() = 0;

  /** Get unsat core of last solve() call. */
  virtual void unsat_core(std::vector<Node>& core) const = 0;
};

}  // namespace bzla::bv

#endif
