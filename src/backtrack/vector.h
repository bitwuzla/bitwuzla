/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_VECTOR_H_INCLUDED
#define BZLA_BACKTRACK_VECTOR_H_INCLUDED

#include <cassert>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class T>
class vector : public Backtrackable
{
 public:
  using iterator        = typename std::vector<T>::iterator;
  using const_iterator  = typename std::vector<T>::const_iterator;
  using const_reference = typename std::vector<T>::const_reference;

  vector() = delete;
  vector(BacktrackManager* mgr) : Backtrackable(mgr) {}

  /* --- std::vector interface ---------------------------------------------- */

  std::size_t size() const { return d_data.size(); }

  bool empty() const { return d_data.empty(); }

  const_reference operator[](std::size_t pos) const { return d_data[pos]; }

  void push_back(const T& value) { d_data.push_back(value); }

  template <class... Args>
  void emplace_back(Args&&... args)
  {
    d_data.emplace_back(std::forward<Args>(args)...);
  }

  const_reference back() { return d_data.back(); }

  const_iterator begin() const { return d_data.begin(); }

  const_iterator end() const { return d_data.end(); }

  void clear()
  {
    d_data.clear();
    for (std::size_t i = 0, size = d_control.size(); i < size; ++i)
    {
      d_control[i] = 0;
    }
  }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_control.push_back(d_data.size()); }

  void pop() override
  {
    assert(!d_control.empty());
    std::size_t pop_to = d_control.back();
    assert(pop_to <= d_data.size());
    d_control.pop_back();

    while (d_data.size() > pop_to)
    {
      d_data.pop_back();
    }
  }

  void insert_at_level(std::size_t level, const T& value)
  {
    // If inserted at current level, just use push_back().
    if (level == d_control.size())
    {
      push_back(value);
      return;
    }
    assert(level < d_control.size());

    std::size_t index = d_control[level];
    d_data.emplace(d_data.begin() + index, value);
    for (std::size_t i = level, size = d_control.size(); i < size; ++i)
    {
      ++d_control[i];
    }
  }

 private:
  std::vector<T> d_data;
};

}  // namespace bzla::backtrack
#endif
