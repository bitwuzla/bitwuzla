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
  void alpha_normalize(AssertionVector& assertions);
  void alpha_normalize(const Node& node);
  Node eliminate(const Node& node);
  Node find_inverse(const Node& body, const Node& var, bool negated = true);
  bool has_var(const Node& node, const Node& var) const;
  std::pair<bool, std::unordered_set<Node>> has_free_vars(
      const Node& node) const;

  Node get_canonical_var(const Node& var);
  void release_canonical_var(const Node& var);
  Node substitute(const Node& node,
                  const std::unordered_map<Node, Node>& substitutions,
                  std::unordered_map<Node, Node>& cache);

  bv::BvInverter d_bv_inverter;
  std::unordered_map<Node, Node> d_cache;

  std::unordered_map<Type, std::vector<std::pair<Node, bool>>> d_alpha_vars;

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
