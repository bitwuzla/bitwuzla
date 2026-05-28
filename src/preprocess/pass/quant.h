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

namespace bzla::preprocess::pass {

class PassQuant : public PreprocessingPass
{
 public:
  PassQuant(Env& env, backtrack::BacktrackManager* backtrack_mgr);
  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  Node eliminate(const Node& node);
  Node find_inverse(const Node& body, const Node& var, bool negated = true);
  bool has_var(const Node& node, const Node& var) const;

  bv::BvInverter d_bv_inverter;
  std::unordered_map<Node, Node> d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats);
    uint64_t& num_elim;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
