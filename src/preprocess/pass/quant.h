/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_QUANT_H_INCLUDED
#define BZLA_PREPROCESS_PASS_QUANT_H_INCLUDED

#include "backtrack/unordered_set.h"
#include "preprocess/preprocessing_pass.h"
#include "solver/bv/bv_inverter.h"
#include "type/type.h"

namespace bzla::preprocess::pass {

class PassQuant : public PreprocessingPass
{
 public:
  PassQuant(Env& env, backtrack::BacktrackManager* backtrack_mgr);
  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  /**
   * Make binding of quantified variables unique, i.e., no binders are shared,
   * neither nested nor across assertions.
   *
   * @note This is already guaranteed through the parser, but via the API,
   *       sharing binders is not disallowed.
   *
   * @params assertions The current set of assertions.
   */
  void uniquify_variables(AssertionVector& assertions);
  void uniquify_variable(const Node& node, const Node& fresh_var);
  /**
   * Alpha-normalize given node.
   * @param node The node to process.
   */
  void alpha_normalize(const Node& node);
  /**
   * Eliminate quantifier based on inverse computation.
   *
   * Given a formula (forall x. (or (not A) B)). If there is a non-negated
   * equality a = b in A (where x appears in either a or b) for which we can
   * derive an inverse x = t and x does not occur in t, we replace the body C
   * with C[x/t].
   *
   * This is a more general version of destructive equality resolution (DER)
   * where a body (or (not (= x t) B) can be simplified to B[x/t] if x does
   * not occur in t.
   *
   * @note Currently, we only have inverse computation for bool/bit-vectors.
   *       However, this also handles the common DER case for non-BV vars.
   *
   * @param node The node to process.
   * @return The resulting node with quantified variable x eliminated, or
   *         the original node if no elimination was possible.
   */
  Node eliminate(const Node& node);
  /**
   * Helper for eliminate. Try to compute an unconditional inverse for an
   * equalite a = b in `body` where `var` occurs in either a or b.
   *
   * Given a formula (forall x. (or (not A) B)), if we find a non-negated
   * equality x = t in A  and x does not occur in t, we can replace the body
   * C with C[x/t]. This is also referred to as destructive equality resolution
   * (DER) in the literature.
   *
   * If x is a bit-vector variable, we can generalize by means of inverse
   * computation: if we find a non-negated equality a = b in A (where x appears
   * in either a or b) and can derive an inverse x = t for this equality and x
   * does not occur in t, we can replace the body C with C[x/t].
   *
   * @param body The body of a quantifer to process.
   * @param var  The quantified variable of the quantifier.
   * @return The unconditional inverse, if there is one, and a null node
   *         otherwise.
   */
  Node find_inverse(const Node& body, const Node& var, bool negated = true);

  std::pair<bool, std::unordered_set<Node>> has_free_vars(
      const Node& node, const std::unordered_set<Node>& closed_quants) const;

  Node get_canonical_var(const Node& var);
  void release_canonical_var(const Node& var);

  /** The associated bit-vector inverter instance. */
  bv::BvInverter d_bv_inverter;

  /** Traversal cache (not persistent across calls to apply()). */
  std::unordered_map<Node, Node> d_cache;
  /** Alpha variable cache (not persistent across calls to apply()). */
  std::unordered_map<Type, std::vector<std::pair<Node, bool>>> d_alpha_vars;

  /** Cache which variables are already bound in assertions. */
  backtrack::unordered_set<uint64_t> d_bound_vars;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_alpha_elim;
    uint64_t& num_inv_elim;
    uint64_t& num_quants;
    util::TimerStatistic& time_alpha_elim;
    util::TimerStatistic& time_inv_elim;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
