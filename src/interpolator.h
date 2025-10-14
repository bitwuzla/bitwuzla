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
   * @note Assertions in A must be currently asserted formulas.
   * @note Current SAT state must be unsat.
   * @param A The set of formulas representing partition A. This must be
   *          a strict subset of the set of current assertions.
   * @return The interpolant.
   */
  Node get_interpolant(const std::unordered_set<Node>& A);

  /**
   * Get an inductive sequence of interpolants <I_1, ..., I_n> given the current
   * set of assertions F and a sequence of partitions.
   *
   * The sequence of partition is given as a list of set increments of asserted
   * formulas {F_1, F_2, ..., F_n}, which expands into sets of partitions
   * {(A_1, B_1), (A_2, B_2), ..., (A_n, B_n)} such that
   *
   *   A_1 = F_1
   *   A_2 = F_1 \cup F_2
   *   ...
   *   A_n = F_1 \cup F_2 \cup ... \cup F_n
   *
   * and B_i = F \ A_i with (and A_i B_i) unsat.
   *
   * The resulting sequence of interpolants is inductive, i.e., it holds that
   * (=> (and I_i F_{i+1}) I_{i+1}).
   *
   * @note Assertions in A_i must be currently asserted formulas.
   * @note Current SAT state must be unsat.
   * @param partitions The set of partitions.
   * @return The interpolation sequence.
   */
  std::vector<Node> get_interpolants(
      const std::vector<std::unordered_set<Node>>& partitions);

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
