/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_REWRITE_H_INCLUDED
#define BZLA_PREPROCESS_PASS_REWRITE_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "rewrite/rewriter.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to perform rewriting on all assertions.
 */
class PassRewrite : public PreprocessingPass
{
 public:
  PassRewrite(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

  Node process(const Node& term) override;

 private:
  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
