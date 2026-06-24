/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2026 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_VECTOR_MAP_H_INCLUDED
#define BZLA_BACKTRACK_VECTOR_MAP_H_INCLUDED

#include <cassert>
#include <unordered_map>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

/**
 * A backtrackable map from keys to vectors of values that supports appending
 * values to a key's vector via add().
 *
 * Each append is recorded on a trail and undone on pop(), so the map always
 * mirrors the current scope. Unlike backtrack::unordered_map, which only rolls
 * back whole key insertions, this container rolls back individual appends: a
 * key's vector may be extended across several scopes and is truncated again
 * (and the key removed once its vector becomes empty) when those scopes are
 * popped.
 */
template <class K, class V>
class vector_map : public Backtrackable
{
 public:
  vector_map() = delete;
  vector_map(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /** Append `value` to the vector associated with `key`. */
  void add(const K& key, const V& value)
  {
    d_data[key].push_back(value);
    d_trail.push_back(key);
  }

  auto find(const K& key) const { return d_data.find(key); }

  auto begin() const { return d_data.begin(); }

  auto end() const { return d_data.end(); }

  bool empty() const { return d_data.empty(); }

  std::size_t size() const { return d_data.size(); }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_trail.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_trail.size());
    d_control.pop_back();

    while (d_trail.size() > pop_to)
    {
      auto it = d_data.find(d_trail.back());
      assert(it != d_data.end());
      assert(!it->second.empty());
      it->second.pop_back();
      if (it->second.empty())
      {
        d_data.erase(it);
      }
      d_trail.pop_back();
    }
  }

 private:
  std::unordered_map<K, std::vector<V>> d_data;
  /** Trail of appended keys, in order, used to undo add() on pop(). */
  std::vector<K> d_trail;
};

}  // namespace bzla::backtrack
#endif
