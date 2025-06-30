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

// #define SIMPLIFY_CACHE_DEBUG

namespace bzla::preprocess {

std::ostream&
operator<<(std::ostream& os, const SimplifyCache::Cacher cacher)
{
  switch (cacher)
  {
    case SimplifyCache::Cacher::REWRITER: os << "rewriter"; break;
    case SimplifyCache::Cacher::VARSUBST: os << "varsubst"; break;
  }
  return os;
}

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
    if (!it->second.frozen() && cached != it->second.subst())
    {
#ifdef SIMPLIFY_CACHE_DEBUG
      std::cout << this << " cache update @" << d_level << ": " << node
                << " -> " << cached << " (before: " << it->second.subst()
                << " @ " << it->second.level() << ", who: " << cacher << ")"
                << std::endl;
#endif
      it->second.update(cached, d_level);
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
    std::cout << this << " cache add @" << d_level << ": " << node << " -> "
              << cached << " (who: " << cacher << ")" << std::endl;
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
  size_t cur_level = it->second.level();
  auto prev_it     = it;
  // Get representative for each level
  do
  {
    if (it->first == it->second.subst())
    {
      break;
    }
    // Found representative for this current level
    if (cur_level != it->second.level())
    {
      // Compress path if length > 1 for cur_level
      compress_path(cur_node, prev_it->first, prev_it->second.subst());

      // Continue with next level
      cur_node  = it->first;
      cur_level = it->second.level();
    }

    prev_it = it;
    it      = d_simplified.find(it->second.subst());
  } while (it != d_simplified.end());

  // If level did not change, compress path
  if (cur_node == node)
  {
    const Node& repr = prev_it->second.subst();
    compress_path(cur_node, prev_it->first, repr);

    auto it = d_simplified.find(cur_node);
    assert(it != d_simplified.end());
    return it->second.subst();
  }

  // Return representative
  return prev_it->second.subst();
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
  return it->second.frozen();
}

void
SimplifyCache::freeze(const Node& node)
{
  auto [it, inserted] = d_simplified.try_emplace(node, node, d_level);
  if (!it->second.frozen())
  {
#ifdef SIMPLIFY_CACHE_DEBUG
    std::cout << this << " cache freeze @ " << d_level << ": " << node
              << std::endl;
#endif
    it->second.freeze(d_level);
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
#ifdef SIMPLIFY_CACHE_DEBUG
  std::cout << this << " cache::push: " << d_level << std::endl;
#endif
}

void
SimplifyCache::pop()
{
#ifdef SIMPLIFY_CACHE_DEBUG
  std::cout << this << " cache::pop: " << d_level << std::endl;
#endif
  // Remove all entries with the current level
  for (auto it = d_simplified.begin(); it != d_simplified.end();)
  {
    if (it->second.level() == d_level)
    {
      if (it->second.pop())
      {
#ifdef SIMPLIFY_CACHE_DEBUG
        std::cout << this << " cache remove @" << d_level << ": " << it->first
                  << std::endl;
#endif
        it = d_simplified.erase(it);
      }
      else
      {
#ifdef SIMPLIFY_CACHE_DEBUG
        std::cout << this << " cache restore @" << d_level << ": " << it->first
                  << " -> " << it->second.subst() << " @ " << it->second.level()
                  << std::endl;
#endif
      }
      ++d_stats.num_popped;
    }
    else
    {
      // If the cache holds the last reference to this node, delete it.
      auto refs = it->first.refs();
      if (refs == 1 || (it->first == it->second.subst() && refs == 2))
      {
        if (it->second.frozen())
        {
          --d_stats.num_frozen;
        }
#ifdef SIMPLIFY_CACHE_DEBUG
        std::cout << this << " cache cleanup @" << d_level << ": " << it->first
                  << " -> " << it->second.subst() << std::endl;
#endif
        it = d_simplified.erase(it);
        ++d_stats.num_deleted;
      }
      else
      {
        // If node was frozen in current level but added in lower level, we can
        // unfreeze the node.
        if (it->second.frozen_level() == d_level)
        {
          it->second.unfreeze();
          --d_stats.num_frozen;
        }
        ++it;
      }
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
    assert(itc->second.level() == d_simplified.find(start)->second.level());
    assert(itc->first != repr);
    bool done = itc->first == end;
    Node next = itc->second.subst();
    // If the cache holds the last reference to this node, delete it.
    auto refs = itc->first.refs();
    if (refs == 1 || (itc->first == itc->second.subst() && refs == 2))
    {
      if (itc->second.frozen())
      {
        --d_stats.num_frozen;
      }
      if (itc->second.pop())
      {
        d_simplified.erase(itc);
        ++d_stats.num_deleted;
      }
    }
    else
    {
      // Update in-place, same level
      itc->second.update(repr);
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
