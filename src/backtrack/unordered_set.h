/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_UNORDERED_SET_H_INCLUDED
#define BZLA_BACKTRACK_UNORDERED_SET_H_INCLUDED

#include <cassert>
#include <unordered_set>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class T>
class unordered_set : public Backtrackable
{
 public:
  unordered_set() = delete;
  unordered_set(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /* --- std::unordered_map interface --------------------------------------- */

  std::size_t size() const { return d_data.size(); }

  bool empty() const { return d_data.empty(); }

  auto find(const T& value) const { return d_data.find(value); }

  auto insert(const T& value)
  {
    auto [it, inserted] = d_data.insert(value);
    if (inserted)
    {
      d_values.emplace_back(*it);
    }
    return std::make_pair(it, inserted);
  }

  auto begin() const { return d_data.begin(); }

  auto end() const { return d_data.end(); }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_values.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_values.size());
    d_control.pop_back();

    while (d_values.size() > pop_to)
    {
      d_data.erase(d_values.back());
      d_values.pop_back();
    }
  }

 private:
  std::unordered_set<T> d_data;
  std::vector<std::reference_wrapper<const T>> d_values;
};

}  // namespace bzla::backtrack
#endif
