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

#include <cstdint>
#include <memory>
#include <unordered_map>
#include <utility>
#include <vector>

#include "env.h"
#include "node/node_kind.h"
#include "solver/abstract/abstraction_lemmas.h"

namespace bzla::abstract {

/**
 * Utility to score, rank and verify the abstraction lemma schemas of
 * bit-vector operators.
 */
class AbstractionLemmaScorer
{
 public:
  /**
   * Constructor.
   * @param env   The associated environment.
   * @param kinds The operator kinds to instantiate the lemma schemas for.
   */
  AbstractionLemmaScorer(Env& env, const std::vector<node::Kind>& kinds);

  /**
   * Compute and print the score of the lemma schemas of the configured kinds.
   * @param bv_size The bit-width to compute the score for.
   */
  void score_lemmas(uint64_t bv_size) const;

  /**
   * Rank the lemma schemas of the configured kinds by their score and print
   * the ranking.
   * @param bv_size The bit-width to compute the score for.
   */
  void rank_lemmas_by_score(uint64_t bv_size);

  /**
   * Rank the lemma schemas of the configured kinds by the size of their
   * bit-blasted circuit and print the ranking.
   * @param bv_size         The bit-width to compute the score of the ranked
   *                        schemas for.
   * @param circuit_bv_size The bit-width to measure the circuit size of the
   *                        lemma schemas for.
   */
  void rank_lemmas_by_circuit_size(uint64_t bv_size, uint64_t circuit_bv_size);

  /**
   * Verify the lemma schemas of the configured kinds, i.e., check that they
   * are implied by the semantics of the corresponding operator.
   * @param bv_size The bit-width to verify the lemma schemas for.
   */
  void verify_lemmas(uint64_t bv_size) const;

 private:
  using Lemmas = std::vector<std::unique_ptr<AbstractionLemma>>;
  /** Maps lemma kind to its score/circuit size. */
  using RankMap = std::unordered_map<LemmaKind, uint64_t>;

  /**
   * Compute and print the score of the given lemma schemas.
   * @param kind     The operator kind of the given lemma schemas.
   * @param lemmas   The lemma schemas to score.
   * @param bv_size  The bit-width to compute the score for.
   * @param rank_map The map to record the score of each lemma schema in.
   */
  void score_lemmas(node::Kind kind,
                    const Lemmas& lemmas,
                    uint64_t bv_size,
                    RankMap& rank_map) const;

  /** Print given ranking as C++ map, to be copied into the source code. */
  void print_rank_map(const RankMap& rank_map) const;

  Env& d_env;
  Rewriter& d_rewriter;
  /** The lemma schemas to score, per operator kind. */
  std::vector<std::pair<node::Kind, Lemmas>> d_lemmas;
};

}  // namespace bzla::abstract
#endif
