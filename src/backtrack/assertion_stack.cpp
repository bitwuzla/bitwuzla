#include "backtrack/assertion_stack.h"

#include "node/node_manager.h"

namespace bzla::backtrack {

/* --- AssertionStack public ------------------------------------------------ */

AssertionStack::AssertionStack() : d_true(NodeManager::get().mk_value(true)) {}
AssertionStack::AssertionStack(BacktrackManager* mgr)
    : Backtrackable(mgr), d_true(NodeManager::get().mk_value(true))
{
}

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
  assert(d_cache.find(assertion) != d_cache.end());
  // If assertion is already a value, we do not need to perform the replacement.
  if (assertion.is_value())
  {
    assert(assertion == replacement);
    return;
  }
  d_cache.erase(assertion);

  auto [it, inserted] = d_cache.emplace(replacement, level);
  if (inserted)
  {
    d_assertions[index].first = replacement;
  }
  else  // Replacement assertion already on stack
  {
    if (level < it->second)
    {
      // Replacement assertion will be added to lower level, remove assertion
      // at higher level and update cache accordingly.
      remove(it->second, replacement);
      d_assertions[index].first = replacement;
      it->second                = level;
    }
    else
    {
      // Do not add replacement to stack, since assertion already exists in
      // previous level. Add true/false instead and update level accordingly.
      d_assertions[index].first = replacement.is_value() ? replacement : d_true;
      std::tie(it, inserted) =
          d_cache.emplace(d_assertions[index].first, level);
      if (!inserted && it->second > level)
      {
        it->second = level;
      }
    }
  }
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

  auto [it, inserted] = d_cache.emplace(assertion, level);
  if (!inserted)
  {
    // Assertion already added in a previous level.
    if (it->second <= level)
    {
      return false;
    }
    // Remove assertion at higher level.
    remove(it->second, assertion);
    // Assertion added to lower level, update index.
    it->second = level;
  }

  // Add assertion to given level and update control stack.
  size_t index = d_control[level];
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
    assert(it != d_cache.end() || assertion.is_value());
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
    assert(it->second == level || assertion.is_value());
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

/* --- AssertionStack private ----------------------------------------------- */

void
AssertionStack::remove(size_t level, const Node& assertion)
{
  if (assertion.is_value())
  {
    // No need to replace true/false
    return;
  }

#ifndef NDEBUG
  bool removed = false;
#endif
  for (size_t i = begin(level), size = end(level); i < size; ++i)
  {
    if (d_assertions[i].first == assertion)
    {
      d_assertions[i].first = d_true;
      auto [it, inserted]   = d_cache.emplace(d_true, level);
      if (!inserted && it->second > level)
      {
        it->second = level;
      }
#ifndef NDEBUG
      removed = true;
#endif
      break;
    }
  }
  assert(removed);
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
