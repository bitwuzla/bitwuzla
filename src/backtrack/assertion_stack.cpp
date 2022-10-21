#include "backtrack/assertion_stack.h"

namespace bzla::backtrack {

/* --- AssertionStack public ------------------------------------------------ */

bool
AssertionStack::push_back(const Node& assertion)
{
  assert(assertion.type().is_bool());
  auto [it, inserted] = d_cache.emplace(assertion, d_assertions.size());
  if (inserted)
  {
    d_assertions.emplace_back(assertion, d_control.size());
  }
  return inserted;
}

void
AssertionStack::replace(const Node& assertion, const Node& replacement)
{
  auto it = d_cache.find(assertion);
  assert(it != d_cache.end());
  size_t index = it->second;
  d_cache.erase(it);
  d_assertions[index].first = replacement;
  d_cache.emplace(replacement, index);
}

void
AssertionStack::insert_at_level(size_t level, const Node& assertion)
{
  // If inserted at current level, just use push_back().
  if (level == d_control.size())
  {
    push_back(assertion);
    return;
  }
  assert(level < d_control.size());

  size_t index        = d_control[level];
  auto [it, inserted] = d_cache.emplace(assertion, index);
  if (!inserted)
  {
    // Assertion already added in a previous level.
    if (it->second < index)
    {
      return;
    }
    // Assertion added to lower level, update index.
    it->second = index;
  }

  // Add assertion to given level and update control stack.
  d_assertions.emplace(d_assertions.begin() + index, assertion, level);
  for (size_t i = level, size = d_control.size(); i < size; ++i)
  {
    ++d_control[i];
  }
}

const std::pair<Node, size_t>&
AssertionView::operator[](size_t index) const
{
  assert(d_start_index + index < d_assertions.size());
  return d_assertions.get(d_start_index + index);
}

size_t
AssertionStack::size() const
{
  return d_assertions.size();
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

const std::pair<Node, size_t>&
AssertionStack::get(size_t index) const
{
  assert(index < d_assertions.size());
  return d_assertions[index];
}

AssertionView&
AssertionStack::create_view()
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
  assert(pop_to < d_assertions.size());
  d_control.pop_back();

  // Pop back assertions
  while (d_assertions.size() > pop_to)
  {
    const auto& [assertion, level] = d_assertions.back();
    auto it                        = d_cache.find(assertion);
    // Only remove from cache if the assertion is at the correct index.
    if (it->second == d_assertions.size() - 1)
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
    assert(it->second < d_assertions.size());
  }
#endif

  // Update views
  size_t size = d_assertions.size();
  for (auto& view : d_views)
  {
    if (view->d_cur_index > size)
    {
      view->d_cur_index   = size;
      view->d_start_index = size;
    }
  }
}

/* --- AssertionView public ------------------------------------------------- */

AssertionView::AssertionView(AssertionStack& assertions)
    : d_assertions(assertions), d_cur_index(0), d_start_index(0)
{
}

const Node&
AssertionView::next()
{
  assert(!empty());
  return d_assertions[d_cur_index++];
}

const std::pair<Node, size_t>&
AssertionView::next_level()
{
  assert(!empty());
  return d_assertions.get(d_cur_index++);
}

bool
AssertionView::empty() const
{
  return d_cur_index >= d_assertions.size();
}

size_t
AssertionView::size() const
{
  return d_assertions.size() - d_start_index;
}

void
AssertionView::replace(const Node& assertion, const Node& replacement)
{
  // Makes sure that we can only replace assertions that can be seen by this
  // view.
  assert(std::find_if(std::begin(d_assertions) + d_start_index,
                      std::end(d_assertions),
                      [assertion](const std::pair<Node, size_t>& p) {
                        return p.first == assertion;
                      })
         != std::end(d_assertions));
  d_assertions.replace(assertion, replacement);
}

void
AssertionView::insert_at_level(size_t level, const Node& assertion)
{
  // Makes sure that we can only insert assertions at levels that can be seen
  // by this view.
  assert(d_assertions.get(d_start_index).second <= level);
  d_assertions.insert_at_level(level, assertion);
}

}  // namespace bzla::backtrack
