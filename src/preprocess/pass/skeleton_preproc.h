/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_SKELETON_PREPROC_H_INCLUDED
#define BZLA_PREPROCESS_PASS_SKELETON_PREPROC_H_INCLUDED

#include <memory>

#include "backtrack/unordered_set.h"
#include "backtrack/vector.h"
#include "bitblast/aig/aig_cnf.h"
#include "preprocess/preprocessing_pass.h"
#include "sat/sat_solver.h"
#include "solver/bv/aig_bitblaster.h"
#include "util/statistics.h"

namespace bzla {

namespace sat {
class Cadical;
}

namespace preprocess::pass {

#ifdef BZLA_USE_CADICAL
class FixedListener;

/**
 * Utility class to determine whether assertions were popped.
 */
class ResetSkel : public backtrack::Backtrackable
{
 public:
  ResetSkel() = delete;
  ResetSkel(backtrack::BacktrackManager* mgr) : backtrack::Backtrackable(mgr) {}
  void push() override {}
  void pop() override { d_flag = true; }
  bool operator()() const { return d_flag; }
  void operator=(bool flag) { d_flag = flag; }

 private:
  bool d_flag = true;
};

/**
 * Preprocessing pass to perform SAT preprocessing on the boolean skeleton.
 */
class PassSkeletonPreproc : public PreprocessingPass
{
 public:
  PassSkeletonPreproc(Env& env, backtrack::BacktrackManager* backtrack_mgr);
  ~PassSkeletonPreproc();

  void apply(AssertionVector& assertions) override;

 private:
  int64_t lit(const Node& term);

  std::unique_ptr<sat::Cadical> d_sat_solver;
  std::unique_ptr<FixedListener> d_fixed_listener;
  std::unordered_map<Node, bool> d_encode_cache;
  backtrack::unordered_set<int64_t> d_assertion_lits;
  backtrack::vector<Node> d_assertions;
  ResetSkel d_reset;
  bool d_done = false;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    util::TimerStatistic& time_sat;
    util::TimerStatistic& time_encode;
    uint64_t& num_new_assertions;
    uint64_t& num_resets;
    uint64_t& num_cnf_lits;
    uint64_t& num_cnf_clauses;
    uint64_t& num_fixed_unused;
  } d_stats;
};

#else

class PassSkeletonPreproc : public PreprocessingPass
{
 public:
  PassSkeletonPreproc(Env& env, backtrack::BacktrackManager* backtrack_mgr)
      : PreprocessingPass(env, backtrack_mgr, "sp", "skeleton_preproc")
  {
  }
  void apply(AssertionVector& assertions) override { (void) assertions; }
};

#endif
}  // namespace preprocess::pass
}  // namespace bzla
#endif
