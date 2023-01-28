#include "backtrack/assertion_stack.h"

namespace bzla::backtrack {

/* --- AssertionStack public ------------------------------------------------ */

bool
AssertionStack::push_back(const Node& assertion)
{
  assert(assertion.type().is_bool());
  auto [it, inserted] = d_cache.emplace(assertion, d_control.size());
  if (inserted)
  {
    d_assertions.emplace_back(assertion, d_control.size());
  }
  return inserted;
}

void
AssertionStack::replace(size_t index, const Node& replacement)
{
  const auto& [assertion, level] = d_assertions[index];
  auto it               = d_cache.find(assertion);
  // Only delete from cache if assertion is the first occurence.
  if (it != d_cache.end() && it->second == level)
  {
    d_cache.erase(it);
  }
  auto [iit, inserted] = d_cache.emplace(replacement, level);
  // New assertion already on stack, update cached index if index is the first
  // occurence of replacement on the stack.
  if (!inserted && iit->second > level)
  {
    iit->second = level;
  }
  d_assertions[index].first = replacement;
}

bool
AssertionStack::insert_at_level(size_t level, const Node& assertion)
{
  // If inserted at current level, just use push_back().
  if (level == d_control.size())
  {
    return push_back(assertion);
  }
  assert(level < d_control.size());

  size_t index        = d_control[level];
  auto [it, inserted] = d_cache.emplace(assertion, level);
  if (!inserted)
  {
    // Assertion already added in a previous level.
    if (it->second <= level)
    {
      return false;
    }
    // Assertion added to lower level, update index.
    it->second = level;
  }

  // Add assertion to given level and update control stack.
  d_assertions.emplace(d_assertions.begin() + index, assertion, level);
  for (size_t i = level, size = d_control.size(); i < size; ++i)
  {
    ++d_control[i];
  }
  return true;
}

size_t
AssertionStack::size() const
{
  return d_assertions.size();
}

size_t
AssertionStack::begin(size_t level) const
{
  if (level > 0)
  {
    return d_control[level - 1];
  }
  return 0;
}

size_t
AssertionStack::end(size_t level) const
{
  if (level == d_control.size())
  {
    return d_assertions.size();
  }
  return d_control[level];
}

size_t
AssertionStack::level(size_t index) const
{
  return d_assertions[index].second;
}

const Node&
AssertionStack::operator[](size_t index) const
{
  assert(index < d_assertions.size());
  return d_assertions[index].first;
}

AssertionView&
AssertionStack::view()
{
  d_views.emplace_back(new AssertionView(*this));
  return *d_views.back();
}

void
AssertionStack::push()
{
  d_control.push_back(d_assertions.size());
}

void
AssertionStack::pop()
{
  assert(!d_control.empty());
  size_t pop_to = d_control.back();
  assert(pop_to <= d_assertions.size());
  d_control.pop_back();

  // Pop back assertions
  while (d_assertions.size() > pop_to)
  {
    const auto& [assertion, level] = d_assertions.back();
    auto it                        = d_cache.find(assertion);
    // Only remove from cache if the assertion is at the correct index.
    // Original assertion might have been removed already due to replace().
    if (it != d_cache.end() && it->second == level)
    {
      d_cache.erase(it);
    }
    d_assertions.pop_back();
  }

#ifndef NDEBUG
  for (const auto& [assertion, level] : d_assertions)
  {
    assert(level <= d_control.size());
    auto it = d_cache.find(assertion);
    assert(it != d_cache.end());
    assert(it->second <= level);
  }
#endif

  // Update views
  size_t size = d_assertions.size();
  for (auto& view : d_views)
  {
    if (view->begin() > size)
    {
      view->set_index(size);
    }
  }
}

/* --- AssertionView public ------------------------------------------------- */

AssertionView::AssertionView(AssertionStack& assertions)
    : d_assertions(assertions), d_index(0)
{
}

const Node&
AssertionView::next()
{
  assert(!empty());
  return d_assertions[d_index++];
}

bool
AssertionView::empty() const
{
  return begin() >= end();
}

size_t
AssertionView::size() const
{
  return end() - begin();
}

size_t
AssertionView::begin(size_t level) const
{
  return d_assertions.begin(level);
}

size_t
AssertionView::end(size_t level) const
{
  return d_assertions.end(level);
}

const Node&
AssertionView::operator[](size_t index) const
{
  return d_assertions[index];
}

size_t
AssertionView::level(size_t index) const
{
  return d_assertions.level(index);
}

size_t
AssertionView::begin() const
{
  return d_index;
}

size_t
AssertionView::end() const
{
  return d_assertions.size();
}

void
AssertionView::set_index(size_t index)
{
  assert(index <= d_assertions.size());
  d_index = index;
}

void
AssertionView::replace(size_t index, const Node& replacement)
{
  d_assertions.replace(index, replacement);
}

bool
AssertionView::insert_at_level(size_t level, const Node& assertion)
{
  return d_assertions.insert_at_level(level, assertion);
}

}  // namespace bzla::backtrack
