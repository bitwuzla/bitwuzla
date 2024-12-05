/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_UNORDERED_MAP_H_INCLUDED
#define BZLA_BACKTRACK_UNORDERED_MAP_H_INCLUDED

#include <cassert>
#include <unordered_map>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class K, class V>
class unordered_map : public Backtrackable
{
 public:
  using iterator       = typename std::unordered_map<K, V>::iterator;
  using const_iterator = typename std::unordered_map<K, V>::const_iterator;

  unordered_map() = delete;
  unordered_map(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /* --- std::unordered_map interface --------------------------------------- */

  std::size_t size() const { return d_data.size(); }

  bool empty() const { return d_data.empty(); }

  auto find(const K& key) const { return d_data.find(key); }

  template <class... Args>
  std::pair<const_iterator, bool> emplace(Args&&... args)
  {
    auto [it, inserted] = d_data.emplace(std::forward<Args>(args)...);
    if (inserted)
    {
      d_keys.emplace_back(it->first);
    }
    return std::make_pair(it, inserted);
  }

  template <class... Args>
  std::pair<const_iterator, bool> try_emplace(Args&&... args)
  {
    auto [it, inserted] = d_data.try_emplace(std::forward<Args>(args)...);
    if (inserted)
    {
      d_keys.emplace_back(it->first);
    }
    return std::make_pair(it, inserted);
  }

  auto begin() const { return d_data.begin(); }

  auto end() const { return d_data.end(); }

  void clear()
  {
    d_data.clear();
    d_keys.clear();
    for (std::size_t i = 0, size = d_control.size(); i < size; ++i)
    {
      d_control[i] = 0;
    }
  }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_keys.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_keys.size());
    d_control.pop_back();

    while (d_keys.size() > pop_to)
    {
      d_data.erase(d_keys.back());
      d_keys.pop_back();
    }
  }

 private:
  std::unordered_map<K, V> d_data;
  std::vector<std::reference_wrapper<const K>> d_keys;
};

}  // namespace bzla::backtrack
#endif
