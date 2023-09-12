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

#include "backtrack/assertion_stack.h"
#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"

namespace bzla::preprocess {

/* --- PreprocessingPass public --------------------------------------------- */

PreprocessingPass::PreprocessingPass(Env& env,
                                     backtrack::BacktrackManager* backtrack_mgr)
    : d_env(env), d_logger(env.logger())
{
  (void) backtrack_mgr;  // suppress warning, may be needed in the future
}

void
PreprocessingPass::clear_cache()
{
  d_processed_assertions.clear();
}

/* --- PreprocessingPass protected ------------------------------------------ */

void
PreprocessingPass::count_parents(const Node& node,
                                 std::unordered_map<Node, uint64_t>& parents,
                                 std::unordered_set<Node>& cache)
{
  node::node_ref_vector visit{node};
  parents.emplace(node, 0);
  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.insert(cur);
    visit.pop_back();
    if (inserted)
    {
      for (auto& child : cur)
      {
        parents[child] += 1;
        visit.push_back(child);
      }
    }
  } while (!visit.empty());
}

std::pair<Node, uint64_t>
PreprocessingPass::substitute(const Node& node,
                              const SubstitutionMap& substitutions,
                              std::unordered_map<Node, Node>& cache) const
{
  node::node_ref_vector visit{node};
  uint64_t num_substs = 0;

  do
  {
    const Node& cur     = visit.back();
    auto [it, inserted] = cache.emplace(cur, Node());
    if (inserted)
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    else if (it->second.is_null())
    {
      auto its = substitutions.find(cur);
      if (its != substitutions.end())
      {
        it->second = its->second;
        num_substs += 1;
      }
      else
      {
        std::vector<Node> children;
        for (const Node& child : cur)
        {
          auto itc = cache.find(child);
          assert(itc != cache.end());
          assert(!itc->second.is_null());
          children.push_back(itc->second);
        }
        it->second = node::utils::rebuild_node(cur, children);
      }
    }
    visit.pop_back();
  } while (!visit.empty());
  auto it = cache.find(node);
  assert(it != cache.end());
  return std::make_pair(it->second, num_substs);
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

}  // namespace bzla::preprocess
