/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "preprocess/assertion_vector.h"

#include "backtrack/assertion_stack.h"

namespace bzla::preprocess {

/* --- AssertionVector public ----------------------------------------------- */

AssertionVector::AssertionVector(backtrack::AssertionView& view,
                                 AssertionTracker* tracker)
    : d_view(view),
      d_level(view.level(view.begin())),
      d_begin(view.begin()),
      d_modified(0),
      d_tracker(tracker)
{
#ifndef NDEBUG
  // Assertion should all be from one level.
  assert(view.begin(d_level) <= view.begin());
  assert(size() > 0);
  for (size_t i = d_begin; i < d_view.end(d_level); ++i)
  {
    assert(d_view.level(i) == d_level);
  }
#endif
}

void
AssertionVector::push_back(const Node& assertion, const Node& parent)
{
  if (d_view.insert_at_level(d_level, assertion))
  {
    ++d_modified;
    if (d_tracker)
    {
      d_tracker->track(assertion, parent);
    }
  }
}

size_t
AssertionVector::size() const
{
  return d_view.end(d_level) - d_begin;
}

const Node&
AssertionVector::operator[](std::size_t index) const
{
  assert(index < size());
  return d_view[d_begin + index];
}

void
AssertionVector::replace(size_t index, const Node& replacement)
{
  assert(index < size());
  size_t real_index = d_begin + index;
  Node assertion    = d_view[real_index];
  if (assertion != replacement)
  {
    if (d_view.replace(real_index, replacement))
    {
      ++d_modified;
      if (d_tracker)
      {
        d_tracker->track(replacement, assertion);
      }
    }
  }
}

bool
AssertionVector::initial_assertions() const
{
  return d_begin == 0;
}

size_t
AssertionVector::start_index() const
{
  return d_begin;
}

/* --- AssertionVector private ---------------------------------------------- */

void
AssertionVector::reset_modified()
{
  d_modified = 0;
}

size_t
AssertionVector::num_modified() const
{
  return d_modified;
}

bool
AssertionVector::modified() const
{
  return d_modified > 0;
}

}  // namespace bzla::preprocess
