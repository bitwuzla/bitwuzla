/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_UDIV_ELIM_H_INCLUDED
#define BZLA_PREPROCESS_PASS_UDIV_ELIM_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to eliminate bit-vector unsigned division.
 */
class PassElimUdiv : public PreprocessingPass
{
 public:
  PassElimUdiv(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  Node process(const Node& assertion) override;

 private:
  const Node& quotient(const Node& node);
  const Node& remainder(const Node& node);

  std::unordered_map<Node, Node> d_cache;
  std::unordered_map<Node, Node> d_quot_cache;
  std::unordered_map<Node, Node> d_rem_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_eliminated;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
