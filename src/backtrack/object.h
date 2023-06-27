/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_BACKTRACK_OBJECT_H_INCLUDED
#define BZLA_BACKTRACK_OBJECT_H_INCLUDED

#include <cassert>
#include <vector>

#include "backtrack/backtrackable.h"

namespace bzla::backtrack {

template <class T>
class object : public Backtrackable
{
 public:
  object() = delete;
  object(BacktrackManager* mgr) : Backtrackable(mgr) { d_data.emplace_back(); }

  object<T>& operator=(const T& data)
  {
    d_data.back() = data;
    return *this;
  }

  typename std::vector<T>::const_reference get() const { return d_data.back(); }

  /* --- Backtrackable interface -------------------------------------------- */

  void push() override { d_data.emplace_back(d_data.back()); }

  void pop() override
  {
    assert(!d_data.empty());
    d_data.pop_back();
  }

 private:
  std::vector<T> d_data;
};

}  // namespace bzla::backtrack
#endif
