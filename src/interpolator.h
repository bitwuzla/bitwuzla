/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_INTERPOLATOR_H_INCLUDED
#define BZLA_INTERPOLATOR_H_INCLUDED

#include "backtrack/assertion_stack.h"
#include "backtrack/vector.h"
#include "env.h"
#include "node/node.h"
#include "solving_context.h"

namespace bzla {

class Interpolator
{
 public:
  Interpolator(SolvingContext& ctx);
  /**
   * Get interpolant I given the current set of assertions, partitioned into
   * A and B such that (and A B) is unsat and (=> A I) and (=> I (not B)).
   * Partition A is the given set of assertions, partition B consists of the
   * remaining assertions that are not in A.
   * @note Assertions in A and B must be currently asserted formulas.
   * @note Current SAT state must be unsat.
   * @param A The set of formulas representing partition A. This must be
   *          a strict subset of the set of current assertions.
   */
  Node get_interpolant(const std::unordered_set<Node>& A);

 private:
  Node interpolant_by_substitution(const std::unordered_set<Node>& A,
                                   const std::unordered_set<Node>& B,
                                   const std::vector<Node>& ppA,
                                   const std::vector<Node>& ppB);

  std::unordered_set<Node> get_consts(const std::unordered_set<Node>& nodes);
  std::unordered_set<Node> shared_consts(const std::unordered_set<Node>& A,
                                         const std::unordered_set<Node>& B);
  Node apply_substs(Env& env,
                    const std::vector<Node>& assertions,
                    const std::unordered_set<Node>& shared);

  /** The associated solving context. */
  SolvingContext& d_ctx;
  /** The associated environnment. */
  Env& d_env;
  /** The associated logger instance. */
  util::Logger& d_logger;
  /** The set of original assertions. */
  const backtrack::vector<Node>& d_original_assertions;
  /** The set of preprocessed assertions. */
  const backtrack::AssertionView& d_pp_assertions;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_get_interpolant;
    uint64_t& interpolant_substA;
    uint64_t& interpolant_substB;
    uint64_t& interpolant_bitlevel;
  } d_stats;
};

}  // namespace bzla
#endif
