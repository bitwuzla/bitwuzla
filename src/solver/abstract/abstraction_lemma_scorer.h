/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_BV_ABSTRACTION_LEMMA_SCORER_H_INCLUDED
#define BZLA_SOLVER_BV_ABSTRACTION_LEMMA_SCORER_H_INCLUDED

#include <unordered_map>

#include "env.h"
#include "node/node_kind.h"
#include "solver/abstract/abstraction_lemmas.h"

namespace bzla::abstract {

class AbstractionLemmaScorer
{
 public:
  /**
   * Constructor.
   * @param env  The associated environment.
   * @param kind The operator kind of the configured lemma scheme.
   */
  AbstractionLemmaScorer(
      Env& env,
      std::unordered_map<node::Kind,
                         std::vector<std::unique_ptr<AbstractionLemma>>>&
          abstr_lemmas)
      : d_env(env), d_rewriter(env.rewriter()), d_abstr_lemmas(abstr_lemmas)
  {
  }

  /** Compute score of lemma schema for configured kind. */
  void score_lemmas(node::Kind kind, uint64_t bv_size) const;

  void rank_lemmas_by_circuit_size();
  void rank_lemmas_by_score();

  void verify_lemmas() const;

 private:
  void score_lemmas_aux(
      node::Kind kind,
      uint64_t bv_size,
      std::unordered_map<LemmaKind, uint64_t>& rank_map) const;

  Env& d_env;
  Rewriter& d_rewriter;
  std::unordered_map<node::Kind,
                     std::vector<std::unique_ptr<AbstractionLemma>>>&
      d_abstr_lemmas;
};

}  // namespace bzla::abstract
#endif
