/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/simplify_cache.h"

#include "env.h"
#include "node/node_utils.h"

//#define SIMPLIFY_CACHE_DEBUG

namespace bzla::preprocess {

/* --- PreprocessorCache public --------------------------------------------- */

SimplifyCache::SimplifyCache(Env& env,
                             backtrack::BacktrackManager* backtrack_mgr,
                             const std::string& id)
    : Backtrackable(backtrack_mgr),
      d_id(id),
      d_stats(env.statistics(), id + "::cache::")
{
}

void
SimplifyCache::add(const Node& node, const Node& subst, const Cacher cacher)
{
  assert(!node.is_null());
  assert(!subst.is_null());
  assert(node.type() == subst.type());

  const Node& cached  = get(subst);
  auto [it, inserted] = d_simplified.try_emplace(node, cached, d_level);
  if (!inserted)
  {
    if (!it->second.d_frozen) // && cached != it->second.d_subst)
    {
#ifdef SIMPLIFY_CACHE_DEBUG
      std::cout << this << " cache update @" << d_level << ": " << node << " -> "
                << cached << " (before: " << it->second.d_subst << " @ "
                << it->second.d_level
                << ", who: " << static_cast<uint32_t>(cacher) << ")"
                << std::endl;
#endif
      it->second.d_subst = cached;
      it->second.d_level = d_level;
      ++d_stats.num_updated;
    }
    else
    {
      ++d_stats.num_not_updated;
    }
  }
  else
  {
#ifdef SIMPLIFY_CACHE_DEBUG
    std::cout << this << " cache add @" << d_level << ": " << node << " -> " << cached
              << " (who: " << static_cast<uint32_t>(cacher) << ")" << std::endl;
#endif
    ++d_stats.num_added;
  }

  switch (cacher)
  {
    case Cacher::REWRITER: it->second.d_flags.rewriter = 1; break;
    case Cacher::VARSUBST: it->second.d_flags.varsubst = 1; break;
  }
}

const Node&
SimplifyCache::get(const Node& node)
{
  auto it = d_simplified.find(node);
  if (it == d_simplified.end())
  {
    return node;
  }

  Node cur_node    = node;
  size_t cur_level = it->second.d_level;
  auto prev_it     = it;
  // Get representative for each level
  do
  {
    if (it->first == it->second.d_subst)
    {
      break;
    }
    // Found representative for this current level
    if (cur_level != it->second.d_level)
    {
      // Compress path if length > 1 for cur_level
      compress_path(cur_node, prev_it->first, prev_it->second.d_subst);

      // Continue with next level
      cur_node  = it->first;
      cur_level = it->second.d_level;
    }

    prev_it = it;
    it      = d_simplified.find(it->second.d_subst);
  } while (it != d_simplified.end());

  // If level did not change, compress path
  if (cur_node == node)
  {
    const Node& repr = prev_it->second.d_subst;
    compress_path(cur_node, prev_it->first, repr);

    auto it = d_simplified.find(cur_node);
    assert(it != d_simplified.end());
    return it->second.d_subst;
  }

  // Return representative
  return prev_it->second.d_subst;
}

bool
SimplifyCache::cached(const Node& node, const Cacher cacher) const
{
  auto it = d_simplified.find(node);
  if (it == d_simplified.end())
  {
    return false;
  }
  switch (cacher)
  {
    case Cacher::REWRITER: return it->second.d_flags.rewriter;
    case Cacher::VARSUBST: return it->second.d_flags.varsubst;
  }
  return false;
}

bool
SimplifyCache::frozen(const Node& node) const
{
  auto it = d_simplified.find(node);
  if (it == d_simplified.end())
  {
    return false;
  }
  return it->second.d_frozen;
}

void
SimplifyCache::freeze(const Node& node)
{
  auto [it, inserted] = d_simplified.try_emplace(node, node, d_level);
  if (!it->second.d_frozen)
  {
#ifdef SIMPLIFY_CACHE_DEBUG
    std::cout << this << " cache freeze @ " << d_level << ": " << node << std::endl;
#endif
    it->second.d_frozen = true;
    ++d_stats.num_frozen;
  }
}

size_t
SimplifyCache::size() const
{
  return d_simplified.size();
}

void
SimplifyCache::push()
{
  ++d_level;
}

void
SimplifyCache::pop()
{
  // Remove all entries with the current level
  for (auto it = d_simplified.cbegin(); it != d_simplified.cend();)
  {
    if (it->second.d_level == d_level)
    {
#ifdef SIMPLIFY_CACHE_DEBUG
      std::cout << this << " cache remove @" << d_level << ": " << it->first << " -> "
                << it->second.d_subst << std::endl;
#endif
      it = d_simplified.erase(it);
      ++d_stats.num_popped;
    }
    // If the cache holds the last reference to this node, delete it.
    else if (it->first.refs() == 1
             || (it->first == it->second.d_subst && it->first.refs() == 2))
    {
      if (it->second.d_frozen)
      {
        --d_stats.num_frozen;
      }
#ifdef SIMPLIFY_CACHE_DEBUG
      std::cout << this << " cache cleanup @" << d_level << ": " << it->first << " -> "
                << it->second.d_subst << std::endl;
#endif
      it = d_simplified.erase(it);
      ++d_stats.num_deleted;
    }
    else
    {
      ++it;
    }
  }
  --d_level;
}

Node
SimplifyCache::rebuild_node(NodeManager& nm, const Node& node)
{
  std::vector<Node> children;

  bool changed = false;
  for (const Node& child : node)
  {
    children.push_back(get(child));
    changed |= children.back() != child;
  }

  if (!changed)
  {
    return get(node);
  }
  return node::utils::rebuild_node(nm, node, children);
}

/* --- PreprocessorCache private -------------------------------------------- */

void
SimplifyCache::compress_path(const Node& start,
                             const Node& end,
                             const Node& repr)
{
  if (start == end)
  {
    return;
  }

  auto itc = d_simplified.find(start);
  while (true)
  {
    assert(itc->second.d_level == d_simplified.find(start)->second.d_level);
    assert(itc->first != repr);
    bool done = itc->first == end;
    Node next = itc->second.d_subst;
    // If the cache holds the last reference to this node, delete it.
    if (itc->first.refs() == 1
        || (itc->first == itc->second.d_subst && itc->first.refs() == 2))
    {
      if (itc->second.d_frozen)
      {
        --d_stats.num_frozen;
      }
      d_simplified.erase(itc);
      ++d_stats.num_deleted;
    }
    else
    {
      itc->second.d_subst = repr;
    }
    ++d_stats.num_compressed;
    if (done)
    {
      break;
    }
    itc = d_simplified.find(next);
    assert(itc != d_simplified.end());
  }
}

SimplifyCache::Statistics::Statistics(util::Statistics& stats,
                                      const std::string& prefix)
    : num_added(stats.new_stat<uint64_t>(prefix + "num_added")),
      num_updated(stats.new_stat<uint64_t>(prefix + "num_updated")),
      num_not_updated(stats.new_stat<uint64_t>(prefix + "num_not_updated")),
      num_popped(stats.new_stat<uint64_t>(prefix + "num_popped")),
      num_compressed(stats.new_stat<uint64_t>(prefix + "num_compressed")),
      num_deleted(stats.new_stat<uint64_t>(prefix + "num_deleted")),
      num_frozen(stats.new_stat<uint64_t>(prefix + "num_frozen"))
{
}

}  // namespace bzla::preprocess
