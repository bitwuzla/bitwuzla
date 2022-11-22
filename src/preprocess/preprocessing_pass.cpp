#include "preprocess/preprocessing_pass.h"

#include "backtrack/assertion_stack.h"

namespace bzla::preprocess {

/* --- AssertionVector public ----------------------------------------------- */

AssertionVector::AssertionVector(backtrack::AssertionView& view)
    : d_view(view),
      d_level(view.level(view.begin())),
      d_begin(view.begin()),
      d_changed(false)
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
AssertionVector::push_back(const Node& assertion)
{
  d_changed = true;
  d_view.insert_at_level(d_level, assertion);
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
AssertionVector::replace(size_t index, const Node& assertion)
{
  assert(index < size());
  size_t real_index = d_begin + index;
  if (d_view[real_index] != assertion)
  {
    d_changed = true;
    d_view.replace(real_index, assertion);
  }
}

/* --- AssertionVector private ---------------------------------------------- */

void
AssertionVector::reset_changed()
{
  d_changed = false;
}

bool
AssertionVector::changed() const
{
  return d_changed;
}

}  // namespace bzla::preprocess
