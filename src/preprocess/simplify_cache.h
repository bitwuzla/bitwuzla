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
  enum class Cacher : uint8_t
  {
    REWRITER    = 0,
    VARSUBST    = 1,
    ELIM_LAMBDA = 2,
  };
  struct ProcessedFlags
  {
    ProcessedFlags() : d_flags(0) {}

    void set(const Cacher c) { d_flags |= 1 << static_cast<uint8_t>(c); }

    bool processed(const Cacher c) const
    {
      return ((d_flags >> static_cast<uint8_t>(c)) & 1) == 1;
    }

   private:
    uint8_t d_flags;
  };

  SimplifyCache(Env& env,
                backtrack::BacktrackManager* backtrack_mgr,
                const std::string& id = "preprocessor");

  /** Add new substition `node` -> `subst`. */
  void add(const Node& node, const Node& subst, const Cacher cacher);

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

  void gc();

 private:
  /**
   * Class to manage substitutions for a node.
   */
  class CacheNode
  {
   public:
    CacheNode(const Node& subst, uint32_t level)
    {
      d_substs.emplace_back(subst, level, ProcessedFlags());
    }

    const Node& subst() const
    {
      assert(!d_substs.empty());
      return d_substs.back().d_subst;
    }

    uint32_t level() const
    {
      assert(!d_substs.empty());
      return d_substs.back().d_level;
    }

    bool pop()
    {
      assert(!d_substs.empty());
      d_substs.pop_back();
      return d_substs.empty();
    }

    void update(const Node& subst, uint32_t lvl)
    {
      assert(level() <= lvl);
      if (lvl == level())
      {
        update(subst);
      }
      else
      {
        d_substs.emplace_back(subst, lvl, d_substs.back().d_flags);
      }
    }

    void update(const Node& subst)
    {
      assert(!d_substs.empty());
      d_substs.back().d_subst = subst;
    }

    void freeze(uint32_t level)
    {
      d_frozen       = true;
      d_frozen_level = level;
    }

    bool frozen() const { return d_frozen; }

    uint32_t frozen_level() const { return d_frozen_level; }

    void unfreeze()
    {
      assert(d_frozen);
      d_frozen       = false;
      d_frozen_level = 0;
    }

    ProcessedFlags& flags() { return d_substs.back().d_flags; }

    const ProcessedFlags& flags() const { return d_substs.back().d_flags; }

   private:
    struct State
    {
      State(const Node& subst, uint32_t level, const ProcessedFlags& flags)
          : d_subst(subst), d_level(level), d_flags(flags)
      {
      }
      Node d_subst;
      uint32_t d_level;
      ProcessedFlags d_flags;
    };

    /** Substitition node and level it was substituted. */
    std::vector<State> d_substs;
    /** Is node frozen? */
    bool d_frozen = false;
    /** Assertion stack level when node was frozen. */
    uint32_t d_frozen_level = 0;
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
  std::unordered_map<Node, CacheNode> d_simplified;

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
    uint64_t& num_gc;
  } d_stats;
};

std::ostream& operator<<(std::ostream& os, const SimplifyCache::Cacher cacher);

}  // namespace bzla::preprocess

#endif
