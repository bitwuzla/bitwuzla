/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "backtrack/backtrackable.h"

#include <cassert>

namespace bzla::backtrack {

/* --- Backtrackable public ------------------------------------------------- */

Backtrackable::Backtrackable(BacktrackManager* mgr) : d_mgr(mgr)
{
  if (d_mgr)
  {
    d_mgr->register_backtrackable(this);
  }
}

Backtrackable::~Backtrackable()
{
  if (d_mgr)
  {
    d_mgr->remove_backtrackable(this);
  }
}

/* --- BacktrackManager public ---------------------------------------------- */

void
BacktrackManager::push()
{
  for (auto& bt : d_backtrackables)
  {
    bt->push();
  }
  ++d_scope_levels;
}

void
BacktrackManager::pop()
{
  assert(d_scope_levels > 0);
  for (auto& bt : d_backtrackables)
  {
    bt->pop();
  }
  --d_scope_levels;
}

std::size_t
BacktrackManager::num_levels() const
{
  return d_scope_levels;
}

/* --- BacktrackManager private --------------------------------------------- */

void
BacktrackManager::register_backtrackable(Backtrackable* backtrackable)
{
  d_backtrackables.insert(backtrackable);
  // If scopes were already pushed, sync the scopes of backtrackable.
  for (std::size_t i = 0; i < d_scope_levels; ++i)
  {
    backtrackable->push();
  }
}

void
BacktrackManager::remove_backtrackable(Backtrackable* backtrackable)
{
  d_backtrackables.erase(backtrackable);
}

}  // namespace bzla::backtrack
