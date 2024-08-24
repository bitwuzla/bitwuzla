/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/preprocessor.h"

#include "env.h"
#include "solving_context.h"
#include "util/logger.h"
#include "util/resources.h"

namespace bzla::preprocess {

#ifndef NDEBUG
namespace {
void
count_nodes(const Node& node, std::unordered_set<Node>& cache)
{
  node::node_ref_vector visit{node};
  do
  {
    const Node& cur = visit.back();
    visit.pop_back();
    auto [it, inserted] = cache.insert(cur);
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}
}  // namespace
#endif

Preprocessor::Preprocessor(SolvingContext& context)
    : d_env(context.env()),
      d_logger(d_env.logger()),
      d_assertions(context.assertions()),
      d_global_backtrack_mgr(*context.backtrack_mgr()),
      d_pop_callback(context.backtrack_mgr(), &d_backtrack_mgr),
      d_assertion_tracker(d_env.options().produce_unsat_cores()
                              ? new AssertionTracker(&d_backtrack_mgr)
                              : nullptr),
      d_pass_rewrite(d_env, &d_backtrack_mgr),
      d_pass_contr_ands(d_env, &d_backtrack_mgr),
      d_pass_elim_lambda(d_env, &d_backtrack_mgr),
      d_pass_elim_bvudiv(d_env, &d_backtrack_mgr),
      d_pass_elim_uninterpreted(d_env, &d_backtrack_mgr),
      d_pass_embedded_constraints(d_env, &d_backtrack_mgr),
      d_pass_variable_substitution(d_env, &d_backtrack_mgr),
      d_pass_flatten_and(d_env, &d_backtrack_mgr),
      d_pass_skeleton_preproc(d_env, &d_backtrack_mgr),
      d_pass_normalize(d_env, &d_backtrack_mgr),
      d_pass_elim_extract(d_env, &d_backtrack_mgr),
      d_stats(d_env.statistics())
{
}

Result
Preprocessor::preprocess()
{
  util::Timer timer(d_stats.time_preprocess);

  // Set of already preprocessed assertions is inconsistent
  if (d_assertions.is_inconsistent())
  {
    return Result::UNSAT;
  }

  // No assertions to process, return.
  if (d_assertions.empty())
  {
    return Result::UNKNOWN;
  }

  if (d_logger.is_msg_enabled(1))
  {
    d_num_printed_stats = 0;
    print_statistics("--");
  }

  // Process assertions by level
  while (!d_assertions.empty() && !d_assertions.is_inconsistent())
  {
    size_t level = d_assertions.level(d_assertions.begin());

    // Sync backtrack manager to level. This is required if there are levels
    // that do not contain any assertions.
    sync_scope(level);

    // Create vector for current level
    AssertionVector assertions(d_assertions, d_assertion_tracker.get());
    assert(assertions.d_level == level);

    // Apply preprocessing passes until fixed-point
    apply(assertions);

    // Advance assertions to next level
    d_assertions.set_index(d_assertions.begin() + assertions.size());
  }
  assert(d_assertions.empty() || d_assertions.is_inconsistent());

  // Sync backtrack manager to level. This is required if there are levels
  // that do not contain any assertions.
  sync_scope(d_global_backtrack_mgr.num_levels());

  if (d_logger.is_msg_enabled(1))
  {
    print_statistics("**");
  }

  // Clear rewriter and preprocessing pass caches
  d_env.rewriter().clear_cache();
  d_pass_rewrite.clear_cache();
  d_pass_contr_ands.clear_cache();
  d_pass_elim_lambda.clear_cache();
  d_pass_elim_bvudiv.clear_cache();
  d_pass_elim_uninterpreted.clear_cache();
  d_pass_embedded_constraints.clear_cache();
  d_pass_variable_substitution.clear_cache();
  d_pass_flatten_and.clear_cache();
  d_pass_skeleton_preproc.clear_cache();
  d_pass_normalize.clear_cache();
  d_pass_elim_extract.clear_cache();

  if (d_assertions.is_inconsistent())
  {
    return Result::UNSAT;
  }
  return Result::UNKNOWN;
}

Node
Preprocessor::process(const Node& term)
{
  util::Timer timer(d_stats.time_process);
  // TODO: add more passes
  Node processed = d_pass_rewrite.process(term);
  processed      = d_pass_variable_substitution.process(processed);
  processed      = d_pass_elim_lambda.process(processed);
  processed      = d_pass_embedded_constraints.process(processed);
  processed      = d_pass_rewrite.process(processed);
  return processed;
}

std::vector<Node>
Preprocessor::post_process_unsat_core(
    const std::vector<Node>& assertions,
    const std::unordered_set<Node>& original_assertions) const
{
  assert(d_assertion_tracker != nullptr);
  std::vector<Node> unsat_core, traced_back;
  d_assertion_tracker->find_original(
      assertions, original_assertions, traced_back);

  // Find involved substitution assertions.
  // TODO: add support for more preprocessing passes (right now disabled)
  std::unordered_set<Node> cache, core_cache;
  std::vector<Node> visit;
  const auto& substs = substitutions();
  for (size_t i = 0; i < traced_back.size(); ++i)
  {
    const Node& assertion = traced_back[i];
    visit.push_back(assertion);
    auto [it, inserted] = core_cache.insert(assertion);
    if (inserted)
    {
      unsat_core.push_back(assertion);
    }
    do
    {
      Node cur = visit.back();
      visit.pop_back();
      auto [it, inserted] = cache.insert(cur);
      if (inserted)
      {
        if (substs.find(cur) != substs.end())
        {
          const Node& substitution_assertion =
              d_pass_variable_substitution.substitution_assertion(cur);
          d_assertion_tracker->find_original(
              {substitution_assertion}, original_assertions, traced_back);
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    } while (!visit.empty());
  }

#ifndef NDEBUG
  for (const Node& a : unsat_core)
  {
    // We should always be able to trace back to the original assertion, if
    // not, some information is not properly tracked in the preprocessor.
    assert(original_assertions.find(a) != original_assertions.end());
  }
#endif

  return unsat_core;
}

const std::unordered_map<Node, Node>&
Preprocessor::substitutions() const
{
  return d_pass_variable_substitution.substitutions();
}

/* --- Preprocessor private ------------------------------------------------- */

void
Preprocessor::apply(AssertionVector& assertions)
{
  // Msg(1) << "Preprocessing " << assertions.size() << " assertions";
  if (assertions.size() == 0)
  {
    return;
  }

#ifndef NDEBUG
  std::unordered_set<Node> cache_pre;
  if (d_env.options().dbg_pp_node_thresh())
  {
    for (size_t i = 0; i < assertions.size(); ++i)
    {
      count_nodes(assertions[i], cache_pre);
    }
  }
#endif

  auto& options = d_env.options();
  // Only apply skeleton preprocessing once to the initial assertions to
  // limit the overhead.
  bool skel_done          = !assertions.initial_assertions();
  bool uninterpreted_done = !assertions.initial_assertions();
  // fixed-point passes
  do
  {
    // Reset changed flag.
    assertions.reset_modified();
    ++d_stats.num_iterations;

    size_t cnt;
    cnt = assertions.num_modified();
    d_pass_rewrite.apply(assertions);
    if (d_logger.is_msg_enabled(1))
    {
      print_statistics(d_pass_rewrite, assertions);
    }
    if (assertions.is_inconsistent())
    {
      break;
    }

    if (options.pp_flatten_and())
    {
      cnt = assertions.num_modified();
      d_pass_flatten_and.apply(assertions);
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_flatten_and, assertions);
      }
      if (assertions.is_inconsistent())
      {
        break;
      }
    }

    if (options.pp_variable_subst())
    {
      do
      {
        assertions.reset_modified();
        cnt = assertions.num_modified();
        d_pass_variable_substitution.apply(assertions);
        if (d_logger.is_msg_enabled(1))
        {
          print_statistics(d_pass_variable_substitution, assertions);
        }
      } while (assertions.modified() && !assertions.is_inconsistent());
      if (assertions.is_inconsistent())
      {
        break;
      }
    }

    if (options.pp_skeleton_preproc() && !skel_done)
    {
      cnt = assertions.num_modified();
      d_pass_skeleton_preproc.apply(assertions);
      skel_done = true;
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_skeleton_preproc, assertions);
      }
      if (assertions.is_inconsistent())
      {
        break;
      }
    }

    if (options.pp_embedded_constr())
    {
      cnt = assertions.num_modified();
      d_pass_embedded_constraints.apply(assertions);
      Msg(2) << assertions.num_modified() - cnt
             << " after embedded constraints";
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_embedded_constraints, assertions);
      }
      if (assertions.is_inconsistent())
      {
        break;
      }
    }

    if (options.pp_contr_ands())
    {
      cnt = assertions.num_modified();
      d_pass_contr_ands.apply(assertions);
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_contr_ands, assertions);
      }
    }

    cnt = assertions.num_modified();
    d_pass_elim_lambda.apply(assertions);
    if (d_logger.is_msg_enabled(1))
    {
      print_statistics(d_pass_elim_lambda, assertions);
    }

    if (options.pp_elim_bv_udiv())
    {
      cnt = assertions.num_modified();
      d_pass_elim_bvudiv.apply(assertions);
      Msg(2) << assertions.num_modified() - cnt
             << " after bvudiv/bvurem elimination";
    }

    // This pass is not supported if incremental is enabled.
    if (false && !uninterpreted_done)
    {
      cnt = assertions.num_modified();
      d_pass_elim_uninterpreted.apply(assertions);
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_elim_uninterpreted, assertions);
      }
      uninterpreted_done = true;
    }

    if (options.rewrite_level() >= 2 && options.pp_normalize())
    {
      cnt = assertions.num_modified();
      d_pass_normalize.apply(assertions);
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_normalize, assertions);
      }
      if (d_assertions.is_inconsistent())
      {
        break;
      }
    }

    if (options.pp_elim_bv_extracts())
    {
      cnt = assertions.num_modified();
      d_pass_elim_extract.apply(assertions);
      if (d_logger.is_msg_enabled(1))
      {
        print_statistics(d_pass_elim_extract, assertions);
      }
      if (d_assertions.is_inconsistent())
      {
        break;
      }
    }

  } while (assertions.modified() && !assertions.is_inconsistent()
           && !d_env.terminate());

#ifndef NDEBUG
  if (d_env.options().dbg_pp_node_thresh())
  {
    double thresh = 1 + d_env.options().dbg_pp_node_thresh() / 100.0;
    std::unordered_set<Node> cache_post;
    for (size_t i = 0; i < assertions.size(); ++i)
    {
      count_nodes(assertions[i], cache_post);
    }
    double ratio = cache_post.size() / static_cast<double>(cache_pre.size());
    Warn(ratio >= thresh) << "Preprocessed assertions contain "
                          << std::setprecision(3) << (ratio - 1) * 100
                          << "% more nodes than original assertions ("
                          << cache_pre.size() << " vs. " << cache_post.size()
                          << ")";
  }
#endif
}

void
Preprocessor::sync_scope(size_t level)
{
  while (d_backtrack_mgr.num_levels() < level)
  {
    d_backtrack_mgr.push();
  }
}

void
Preprocessor::print_statistics_header() const
{
  // clang-format off
    Msg(1);
    Msg(1) << std::left << std::setw(36) << "preprocessing"
           << std::left << std::setw(24) << " assertions"
           << std::left << std::setw(18) << "     nodes";
    Msg(1) << std::setw(4) << "pass"
           << std::setw(8) << "seconds"
           << std::setw(8) << "sum"
           << std::setw(8) << "%"
           << std::setw(8) << "MB"
           << std::setw(8) << "process"
           << std::setw(8) << "changed"
           << std::setw(8) << "simp"
           << std::setw(10) << "alloc"
           << std::setw(10) << "dealloc"
           << std::setw(8) << "MB";
    Msg(1);
  // clang-format on
}

void
Preprocessor::print_statistics(const std::string& pass)
{
  if (d_num_printed_stats % 20 == 0)
  {
    print_statistics_header();
  }

  ++d_num_printed_stats;

  double time_preproc = d_stats.time_preprocess.elapsed() / 1000.0;
  const auto& nm_stats = d_env.nm().statistics();
  double mb            = static_cast<double>(1 << 20);

  // clang-format off
  Msg(1) << std::setw(4) << pass
         << std::setw(8) << std::setprecision(1)
         << std::fixed << time_preproc
         << std::setw(8) << time_preproc
         << std::setw(8) << " "
         << std::setw(8) << util::current_memory_usage() / mb
         << std::setw(8) << d_assertions.size()
         << std::setw(8) << ""
         << std::setw(8) << ""
         << std::setw(10) << nm_stats.d_num_node_data
         << std::setw(10) << nm_stats.d_num_node_data_dealloc
         << std::setw(8)
         // Note: this is just a lower bound since it does not consider the
         //       payload memory of node data.
         << nm_stats.d_num_node_data * sizeof(node::NodeData) / mb;
  // clang-format on
}

void
Preprocessor::print_statistics(const PreprocessingPass& pass,
                               const AssertionVector& assertions)
{
  if (d_num_printed_stats % 20 == 0)
  {
    print_statistics_header();
  }

  std::string pid = pass.id();
  if (assertions.is_inconsistent())
  {
    pid += "*";
  }

  double time_preproc = d_stats.time_preprocess.elapsed();
  double time_pass    = pass.statistics().time_apply.elapsed();
  double time_pass_perc =
      time_preproc > 0.0 ? time_pass / time_preproc * 100.0 : 0;

  ++d_num_printed_stats;

  const auto& nm_stats = d_env.nm().statistics();
  double mb            = static_cast<double>(1 << 20);

  // clang-format off
  Msg(1) << std::setw(4) << pid
         << std::setw(8) << std::setprecision(1)
         << std::fixed << time_preproc / 1000.0
         << std::setw(8) << time_pass / 1000.0
         << std::setw(8) << time_pass_perc
         << std::setw(8) << util::current_memory_usage() / mb
         << std::setw(8) << assertions.size()
         << std::setw(8) << assertions.num_modified()
         << std::setw(8) << assertions.num_simplified()
         << std::setw(10) << nm_stats.d_num_node_data
         << std::setw(10) << nm_stats.d_num_node_data_dealloc
         << std::setw(8)
         << nm_stats.d_num_node_data * sizeof(node::NodeData) / mb;
  // clang-format on
}

Preprocessor::Statistics::Statistics(util::Statistics& stats)
    : time_preprocess(
        stats.new_stat<util::TimerStatistic>("preprocessor::time_preprocess")),
      time_process(
          stats.new_stat<util::TimerStatistic>("preprocessor::time_process")),
      num_iterations(stats.new_stat<uint64_t>("preprocessor::num_iterations"))
{
}

}  // namespace bzla::preprocess
