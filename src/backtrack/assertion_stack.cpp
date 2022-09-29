#include "backtrack/assertion_stack.h"

namespace bzla::backtrack {

/* --- AssertionStack public ------------------------------------------------ */

void
AssertionStack::push_back(const Node& assertion)
{
  assert(assertion.type().is_bool());
  auto [it, inserted] = d_cache.insert(assertion);
  if (inserted)
  {
    d_assertions.emplace_back(assertion, d_control.size());
  }
}

void
AssertionStack::replace(size_t index, const Node& assertion)
{
  d_cache.erase(d_assertions[index].first);
  d_assertions[index].first = assertion;
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
    d_cache.erase(d_assertions.back().first);
    d_assertions.pop_back();
  }

  // Update views
  size_t size = d_assertions.size();
  for (auto& view : d_views)
  {
    if (view->d_index > size)
    {
      view->d_index = size;
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

const std::pair<Node, size_t>&
AssertionView::next_level()
{
  assert(!empty());
  return d_assertions.get(d_index++);
}

std::pair<Node, size_t>
AssertionView::next_index()
{
  assert(!empty());
  size_t index = d_index;
  return std::make_pair(next(), index);
}

bool
AssertionView::empty() const
{
  return d_index >= d_assertions.size();
}

size_t
AssertionView::size()
{
  return d_assertions.size() - d_index;
}

void
AssertionView::replace(size_t index, const Node& assertion)
{
  d_assertions.replace(index, assertion);
}

}  // namespace bzla::backtrack
