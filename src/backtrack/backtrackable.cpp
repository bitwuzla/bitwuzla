#include "backtrack/backtrackable.h"

#include <cassert>

namespace bzla::backtrack {

Backtrackable::Backtrackable(BacktrackManager* mgr) : d_mgr(mgr)
{
  d_mgr->register_backtrackable(this);
}

Backtrackable::~Backtrackable()
{
  if (d_mgr)
  {
    d_mgr->remove_backtrackable(this);
  }
}

void
BacktrackManager::push()
{
  ++d_scope_levels;
  for (auto& bt : d_backtrackables)
  {
    bt->push();
  }
}

void
BacktrackManager::pop()
{
  assert(d_scope_levels > 0);
  --d_scope_levels;
  for (auto& bt : d_backtrackables)
  {
    bt->pop();
  }
}

void
BacktrackManager::register_backtrackable(Backtrackable* backtrackable)
{
  d_backtrackables.insert(backtrackable);
}

void
BacktrackManager::remove_backtrackable(Backtrackable* backtrackable)
{
  d_backtrackables.erase(backtrackable);
}

}  // namespace bzla::backtrack
