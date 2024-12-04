/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_PREPROCESS_PREPROCESSOR_CACHE_H_INCLUDED
#define BZLA_PREPROCESS_PREPROCESSOR_CACHE_H_INCLUDED

#include "backtrack/backtrackable.h"
#include "node/node.h"
#include "util/statistics.h"

namespace bzla {
class Env;
}

namespace bzla::preprocess {

/**
 * Incremental union-find data structure for storing substitutions.
 *
 * This class is used to store node substitutions. It automatically performs
 * path compression if applicable.
 * For example, if we add substitutions w -> x, x -> y, y -> z, we update the
 * representative for w, x, y to z. If x and y become local to the cache (i.e.,
 * have a reference count of one), we delete the entries for x and y.
 */
class SimplifyCache : public backtrack::Backtrackable
{
 public:
  enum class Cacher
  {
    REWRITER = 0,
    VARSUBST = 1,
  };
  struct ProcessedFlags
  {
    uint8_t rewriter : 1;
    uint8_t varsubst : 1;

    ProcessedFlags() : rewriter(0), varsubst(0) {}
  };

  SimplifyCache(Env& env,
                backtrack::BacktrackManager* backtrack_mgr,
                const std::string& id = "preprocessor");

  /** Add new substition `node` -> `subst`. */
  // TEMPORARY default
  void add(const Node& node,
           const Node& subst,
           const Cacher cacher = Cacher::REWRITER);

  /**
   * @return The representative of `node`.
   *
   * This will perform path compression if applicable.
   */
  const Node& get(const Node& node);

  /** @return Whether `node` is already in the cache. */
  bool cached(const Node& node, const Cacher cacher) const;

  /**
   * @return Whether `node` can still be processed.
   */
  bool frozen(const Node& node) const;

  /**
   * Freeze `node` to make it permanent in the cache.
   */
  void freeze(const Node& node);

  /** @return  The number of entries in the cache. */
  size_t size() const;

  /** Increase the assertion level. */
  void push() override;

  /**
   * Decrease the assertion level. Remove substitution entries added in popped
   * level.
   */
  void pop() override;

  /**
   * Rebuild node with same kind and indices but new children taken from cache.
   *
   * @param nm The node manager to use.
   * @param node The node to rebuild.
   * @return Rebuilt node.
   */
  Node rebuild_node(NodeManager& nm, const Node& node);

 private:
  /**
   * Struct to hold additional information.
   */
  struct CacheInfo
  {
    /** Substitition node. */
    Node d_subst;
    /** Assertion stack level when substitution happend. */
    uint32_t d_level;
    ProcessedFlags d_flags;
    bool d_frozen = false;

    CacheInfo(const Node& subst, uint32_t level)
        : d_subst(subst), d_level(level)
    {
    }
  };

  /**
   * Compress substitution path.
   *
   * For each element in the path of start to end, we set the substitution to
   * `repr`.
   */
  void compress_path(const Node& start, const Node& end, const Node& repr);

  /** Current assertion stack level. */
  uint32_t d_level = 0;

  std::string d_id;

  /** Maps nodes to their substitutions with corrsponding assertion level. */
  std::unordered_map<Node, CacheInfo> d_simplified;

  struct Statistics
  {
    Statistics(util::Statistics& stats, const std::string& prefix);
    uint64_t& num_added;
    uint64_t& num_updated;
    uint64_t& num_not_updated;
    uint64_t& num_popped;
    uint64_t& num_compressed;
    uint64_t& num_deleted;
    uint64_t& num_frozen;
  } d_stats;
};

}  // namespace bzla::preprocess

#endif
