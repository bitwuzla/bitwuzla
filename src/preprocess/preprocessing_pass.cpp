/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/preprocessing_pass.h"

#include "env.h"
#include "node/node_utils.h"

namespace bzla::preprocess {

/* --- PreprocessingPass public --------------------------------------------- */

PreprocessingPass::PreprocessingPass(Env& env,
                                     backtrack::BacktrackManager* backtrack_mgr,
                                     const std::string& id,
                                     const std::string& name)
    : d_env(env),
      d_logger(env.logger()),
      d_stats_pass(d_env.statistics(), "preprocess::" + name + "::"),
      d_id(id),
      d_name(name)

{
  (void) backtrack_mgr;  // suppress warning, may be needed in the future
}

void
PreprocessingPass::clear_cache()
{
  d_processed_assertions.clear();
}

/* --- PreprocessingPass protected ------------------------------------------ */

std::pair<Node, uint64_t>
PreprocessingPass::substitute(const Node& node,
                              const SubstitutionMap& substitutions,
                              std::unordered_map<Node, Node>& cache) const
{
  uint64_t num_substs = 0;
  Node res            = node::utils::substitute(
      d_env.nm(), node, substitutions.map(), cache, false, &num_substs);
  return std::make_pair(res, num_substs);
}

Node
PreprocessingPass::substitute(
    const Node& node,
    const std::unordered_map<Node, Node>& substitutions,
    std::unordered_map<Node, Node>& cache) const
{
  return node::utils::substitute(d_env.nm(), node, substitutions, cache);
}

bool
PreprocessingPass::cache_assertion(const Node& assertion)
{
  return d_processed_assertions.insert(assertion).second;
}

bool
PreprocessingPass::processed(const Node& assertion)
{
  return d_processed_assertions.find(assertion) != d_processed_assertions.end();
}

PreprocessingPass::Statistics::Statistics(util::Statistics& stats,
                                          const std::string& prefix)
    : time_apply(stats.new_stat<util::TimerStatistic>(prefix + "time_apply"))
{
}

}  // namespace bzla::preprocess
