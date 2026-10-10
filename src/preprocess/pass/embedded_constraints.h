/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED
#define BZLA_PREPROCESS_PASS_EMBEDDED_CONSTRAINTS_H_INCLUDED

#include <optional>

#include "backtrack/backtrackable.h"
#include "backtrack/unordered_map.h"
#include "backtrack/vector.h"
#include "preprocess/preprocessing_pass.h"
#include "util/statistics.h"

namespace bzla::preprocess::pass {

/**
 * Preprocessing pass to substitute embedded constraints with true.
 */
class PassEmbeddedConstraints : public PreprocessingPass
{
 public:
  PassEmbeddedConstraints(Env& env, backtrack::BacktrackManager* backtrack_mgr);

  void apply(AssertionVector& assertions) override;
  Node process(const Node& node) override;

 private:
  /**
   * Substitute embedded constraints in `node`. Rebuilt nodes are only
   * rewritten locally, which requires `node` to be rewritten.
   */
  Node substitute(const Node& node);

  /** Backtrackable substitution map. */
  backtrack::unordered_map<Node, Node> d_substitutions;
  /**
   * Lower bound of the node ids of the substitutions added by each call to
   * apply() that added substitutions.
   */
  backtrack::vector<uint64_t> d_batch_min_id;
  /**
   * Maps the number of batches of substitutions to the lower bound of the node
   * ids of the substitutions added by later batches. Recomputed whenever
   * d_batch_min_id changes.
   */
  std::vector<uint64_t> d_later_min_id;
  /** Number of batches added so far, to detect changes of d_batch_min_id. */
  uint64_t d_num_batches_added = 0;
  /** The value of d_num_batches_added d_later_min_id was computed for. */
  uint64_t d_later_min_id_version = 0;
  /**
   * Lower bound of the node ids of all substitutions. Nodes with smaller ids
   * cannot contain any of them.
   */
  uint64_t d_min_subst_id = UINT64_MAX;

  /**
   * Substitution cache. Entries stay valid across calls as long as no
   * substitution added later can occur in the cached node, entries added at a
   * scope level are removed when the level is popped. Entries of lower levels
   * overwritten at a popped level are restored, since they are valid again
   * once the substitutions of the popped level are removed.
   */
  class Cache : public backtrack::Backtrackable
  {
   public:
    struct Entry
    {
      Node result;
      /** Number of batches of substitutions the result was computed for. */
      size_t num_batches;
    };

    Cache(backtrack::BacktrackManager* mgr) : Backtrackable(mgr) {}

    void push() override { d_undo.emplace_back(); }

    void pop() override
    {
      assert(!d_undo.empty());
      // Undo in reverse order, a node may be inserted several times.
      auto& undo = d_undo.back();
      for (auto it = undo.rbegin(); it != undo.rend(); ++it)
      {
        if (it->second)
        {
          d_map.insert_or_assign(it->first, *it->second);
        }
        else
        {
          d_map.erase(it->first);
        }
      }
      d_undo.pop_back();
    }

    const Entry* find(const Node& node) const
    {
      auto it = d_map.find(node);
      return it == d_map.end() ? nullptr : &it->second;
    }

    void insert(const Node& node, const Node& result, size_t num_batches)
    {
      auto [it, inserted] = d_map.try_emplace(node, Entry{result, num_batches});
      if (!d_undo.empty())
      {
        d_undo.back().emplace_back(
            node, inserted ? std::nullopt : std::optional<Entry>(it->second));
      }
      if (!inserted)
      {
        it->second = Entry{result, num_batches};
      }
    }

   private:
    std::unordered_map<Node, Entry> d_map;
    /** Nodes inserted at each scope level with the entries they overwrote. */
    std::vector<std::vector<std::pair<Node, std::optional<Entry>>>> d_undo;
  } d_cache;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    /**
     * Number of substituted nodes. Results are cached across calls, hence a
     * node is counted again only if its cached result was invalidated.
     */
    uint64_t& num_substs;
  } d_stats;
};

}  // namespace bzla::preprocess::pass

#endif
