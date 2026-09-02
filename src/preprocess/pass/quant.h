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
   * Rebuild given quantifier with `fresh_var` in place of its variable.
   *
   * @note Expects the body of `node` to be cached in d_cache.
   *
   * @param node      The quantifier whose variable is already bound elsewhere.
   * @param fresh_var The variable to bind instead, of the same type as the
   *                  variable of `node`.
   * @return `node` with its variable replaced by `fresh_var`.
   */
  Node uniquify_variable(const Node& node, const Node& fresh_var);
  /**
   * Alpha-normalize given node.
   *
   * Two quantifiers are alpha-equivalent iff they are equal up to renaming of
   * their bound variables. We determine this by computing their alpha-normal
   * form, i.e., by renaming the variable of every binder to the canonical
   * variable of its type. All quantifiers with the same alpha-normal form are
   * mapped to the first one encountered.
   *
   * @note `node` does not have to be a quantifier itself, it may be any node
   *       with quantifiers below it. It must, however, be closed: the
   *       alpha-normal form of `node` is registered in d_alpha_reps, and
   *       has_free_vars() relies on the nodes registered there being closed.
   *
   * @param node The closed node to process.
   * @return The representative of the alpha-equivalence class of `node`.
   */
  Node alpha_normalize(const Node& node);
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

  /**
   * Determine whether given node has free variables.
   *
   * @note Does not descend into nodes cached in d_alpha_reps (except `node`
   *       itself), which are already normalized.
   *
   * @param node The node to check.
   * @return A pair of a flag for whether `node` has free variables, and the set
   *         of variables bound below `node` (empty if it has free variables).
   */
  std::pair<bool, std::unordered_set<Node>> has_free_vars(
      const Node& node) const;

  Node get_canonical_var(const Node& var);
  void release_canonical_var(const Node& var);

  /** The associated bit-vector inverter instance. */
  bv::BvInverter d_bv_inverter;

  /**
   * Traversal cache.
   * @note Not persistent across calls to apply().
   */
  std::unordered_map<Node, Node> d_cache;

  /**
   * Maps node to its alpha-normal form.
   * @note Not persistent across calls to apply().
   */
  std::unordered_map<Node, Node> d_alpha_cache;
  /**
   * Alpha variable cache.
   * The pool of canonical variables per type, with a flag for whether a
   * variable is currently in use by a binder.
   * @note Persistent across calls to apply().
   */
  std::unordered_map<Type, std::vector<std::pair<Node, bool>>> d_alpha_vars;
  /**
   * Map alpha-normalized assertions and quantifiers to their representative.
   * @note All registered alpha-normal forms are closed, has_free_vars()
   *       relies on this.
   * @note Not persistent across calls to apply().
   */
  std::unordered_map<Node, Node> d_alpha_reps;

  /** Cache which variables are already bound in assertions. */
  backtrack::unordered_set<uint64_t> d_bound_vars;

  /** Cache option to enable alpha equivalence processing. */
  bool d_opt_quant_alpha;

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
