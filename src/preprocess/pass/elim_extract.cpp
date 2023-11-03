/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/pass/elim_extract.h"

#include <unordered_set>

#include "env.h"
#include "node/node_manager.h"
#include "node/node_ref_vector.h"
#include "node/node_utils.h"
#include "node/unordered_node_ref_map.h"
#include "node/unordered_node_ref_set.h"
#include "util/hash_pair.h"

namespace bzla::preprocess::pass {

using namespace node;

/* --- PassElimExtract public ------------------------------------------------
 */

PassElimExtract::PassElimExtract(Env& env,
                                 backtrack::BacktrackManager* backtrack_mgr)
    : PreprocessingPass(env, backtrack_mgr), d_stats(env.statistics())
{
}

void
PassElimExtract::apply(AssertionVector& assertions)
{
  // Disabled if unsat cores enabled.
  if (d_env.options().produce_unsat_cores())
  {
    return;
  }

  util::Timer timer(d_stats.time_apply);
  d_cache.clear();

  std::unordered_map<Node, std::vector<Node>> extract_map;

  for (size_t i = 0, size = assertions.size(); i < size; ++i)
  {
    const Node& assertion = assertions[i];
    if (cache_assertion(assertion))
    {
      collect_extracts(assertion, extract_map);
    }
  }

  NodeManager& nm = NodeManager::get();
  for (const auto& [c, extracts] : extract_map)
  {
    if (processed(c))
    {
      continue;
    }
    std::unordered_set<std::pair<uint64_t, uint64_t>> indices;
    uint64_t size = c.type().bv_size();

    for (const Node& extract : extracts)
    {
      indices.emplace(extract.index(0), extract.index(1));
    }

    indices.emplace(size - 1, 0);
    bool normalized = compute_non_overlapping(indices);
    if (!normalized)
    {
      continue;
    }

    std::vector<std::pair<uint64_t, uint64_t>> non_overlapping(indices.begin(),
                                                               indices.end());
    std::sort(
        non_overlapping.begin(), non_overlapping.end(), [](auto& p1, auto& p2) {
          return p1.first > p2.first
                 || (p1.first == p2.first && p1.second > p2.second);
        });

    std::vector<Node> consts;
    for (auto [upper, lower] : non_overlapping)
    {
      Type t = nm.mk_bv_type(upper - lower + 1);
      consts.push_back(nm.mk_const(t));
      cache_assertion(consts.back());
    }

    Node concat = utils::mk_nary(Kind::BV_CONCAT, consts);
    Node null;
    assertions.push_back(nm.mk_node(Kind::EQUAL, {c, concat}), null);
    cache_assertion(c);
  }

  d_cache.clear();
}

Node
PassElimExtract::process(const Node& term)
{
  assert(false);
  return term;
}

/* --- PassElimExtract private -----------------------------------------------
 */

void
PassElimExtract::collect_extracts(
    const Node& assertion,
    std::unordered_map<Node, std::vector<Node>>& extracts)
{
  node_ref_vector visit{assertion};

  do
  {
    const Node& cur = visit.back();
    visit.pop_back();

    if (d_cache.insert(cur).second)
    {
      if (cur.kind() == Kind::BV_EXTRACT && cur[0].is_const())
      {
        extracts[cur[0]].push_back(cur);
        continue;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

bool
PassElimExtract::compute_non_overlapping(
    std::unordered_set<std::pair<uint64_t, uint64_t>>& indices)
{
  bool normalized = false;
  bool restart    = false;
  do
  {
    for (auto s1 : indices)
    {
      restart       = false;
      auto [hi, lo] = s1;
      for (auto s2 : indices)
      {
        if (s1 == s2)
        {
          continue;
        }
        auto [h, l] = s2;

        // not overlapping?
        if (lo > h || hi < l || l > hi || h < lo)
        {
          continue;
        }
        // overlapping
        if (hi == h)
        {
          uint64_t max = std::max(lo, l);
          uint64_t min = std::min(lo, l);
          if (min == lo)
          {
            indices.erase(s1);
          }
          else
          {
            indices.erase(s2);
          }
          indices.emplace(max - 1, min);
          restart = true;
          break;
        }
        else if (lo == l)
        {
          uint64_t max = std::max(hi, h);
          uint64_t min = std::min(hi, h);
          if (max == hi)
          {
            indices.erase(s1);
          }
          else
          {
            indices.erase(s2);
          }
          indices.emplace(max, min + 1);
          restart = true;
          break;
        }
        else
        {
          std::vector<uint64_t> idxs = {hi, lo, h, l};
          std::sort(idxs.begin(), idxs.end());
          // we have to copy s to ensure that we erase the expected element
          // after slice has been erased (both are references)
          indices.erase(s1);
          indices.erase(s2);
          indices.emplace(idxs[3], idxs[2] + 1);
          indices.emplace(idxs[2], idxs[1]);
          indices.emplace(idxs[1] - 1, idxs[0]);
          restart = true;
          break;
        }
      }
      if (restart)
      {
        normalized = true;
        break;
      }
    }
  } while (restart);
  return normalized;
}

PassElimExtract::Statistics::Statistics(util::Statistics& stats)
    : time_apply(stats.new_stat<util::TimerStatistic>(
        "preprocess::elim_extract::time_apply")),
      num_elim(stats.new_stat<uint64_t>("preprocess::elim_extract::num_elim"))
{
}

}  // namespace bzla::preprocess::pass
