/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED
#define BZLA_PREPROCESS_PASS_FLATTEN_AND_H_INCLUDED

#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to flatten AND nodes.
 */
class PassFlattenAnd : public PreprocessingPass
{
 public:
  PassFlattenAnd(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;

 private:
  struct Statistics
  {
    Statistics(util::Statistics& stats);
    util::TimerStatistic& time_apply;
    uint64_t& num_flattened;
    uint64_t& num_assertions;
  } d_stats;
};

}  // namespace bzla::preprocess::pass
#endif
