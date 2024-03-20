/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/* -------------------------------------------------------------------------- */

#include "ls.h"
#include "util/logger.h"
#include "util/statistics.h"

namespace bzla::ls {

template <class VALUE>
struct LocalSearch<VALUE>::StatisticsInternal
{
  StatisticsInternal(util::Statistics& stats, const std::string& prefix);
  uint64_t& num_roots;
  uint64_t& num_roots_ineq;
  uint64_t& num_roots_sat;
  uint64_t& num_roots_unsat;
  uint64_t& num_props;
  uint64_t& num_updates;
  uint64_t& num_moves;

  uint64_t& num_props_inv;
  uint64_t& num_props_cons;

  uint64_t& num_conflicts;

#ifndef NDEBUG
  util::HistogramStatistic& num_inv_values;
  util::HistogramStatistic& num_cons_values;
  util::HistogramStatistic& num_conflicts_per_kind;
  util::HistogramStatistic& num_sineq_parents_per_kind;
  util::HistogramStatistic& num_uineq_parents_per_kind;
  util::HistogramStatistic& num_sbounds_per_kind;
  util::HistogramStatistic& num_ubounds_per_kind;
#endif
  util::TimerStatistic& time_move;
  util::TimerStatistic& time_update_cone;
};

template <class VALUE>
LocalSearch<VALUE>::StatisticsInternal::StatisticsInternal(
    util::Statistics& stats, const std::string& prefix)
    : num_roots(stats.new_stat<uint64_t>(prefix + "num_roots")),
      num_roots_ineq(stats.new_stat<uint64_t>(prefix + "num_roots_ineq")),
      num_roots_sat(stats.new_stat<uint64_t>(prefix + "num_roots_sat")),
      num_roots_unsat(stats.new_stat<uint64_t>(prefix + "num_roots_unsat")),
      num_props(stats.new_stat<uint64_t>(prefix + "num_props")),
      num_updates(stats.new_stat<uint64_t>(prefix + "num_updates")),
      num_moves(stats.new_stat<uint64_t>(prefix + "num_moves")),
      num_props_inv(stats.new_stat<uint64_t>(prefix + "num_props_inv")),
      num_props_cons(stats.new_stat<uint64_t>(prefix + "num_props_cons")),
      num_conflicts(stats.new_stat<uint64_t>(prefix + "num_conflicts")),
#ifndef NDEBUG
      num_inv_values(
          stats.new_stat<util::HistogramStatistic>(prefix + "num_inv_values")),
      num_cons_values(
          stats.new_stat<util::HistogramStatistic>(prefix + "num_cons_values")),
      num_conflicts_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_conflicts_per_kind")),
      num_sineq_parents_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_sineq_parents_per_kind")),
      num_uineq_parents_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_uineq_parents_per_kind")),
      num_sbounds_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_sbounds_per_kind")),
      num_ubounds_per_kind(stats.new_stat<util::HistogramStatistic>(
          prefix + "num_ubounds_per_kind")),
#endif
      time_move(stats.new_stat<util::TimerStatistic>(prefix + "time_move")),
      time_update_cone(
          stats.new_stat<util::TimerStatistic>(prefix + "time_update_cone"))
{
}

template <class VALUE>
struct LocalSearch<VALUE>::Internal
{
  Internal(util::Statistics& stats,
           const std::string& stats_prefix,
           uint32_t log_level,
           uint32_t verbosity_level,
           const std::string& name)
      : d_stats(stats, stats_prefix), d_logger(log_level, verbosity_level, name)
  {
  }
  StatisticsInternal d_stats;
  util::Logger d_logger;
};

/* -------------------------------------------------------------------------- */

}  // namespace bzla::ls
