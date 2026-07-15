/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*----------------------------------------------------------------------------*/

#include "sat/distinct_n_propagator.h"

#include <algorithm>
#include <cassert>
#include <cstdlib>

#include "lib/bv/bitvector.h"
#include "sat/propagator.h"

namespace bzla::sat {

WatchedBV::WatchedBV(const std::vector<int32_t>& lits) : d_lits(lits) {}

int32_t
WatchedBV::watched() const
{
  assert(d_watched < d_lits.size());
  return std::abs(d_lits[d_watched]);
}

bool
WatchedBV::assign(const Propagator& propagator, int32_t lit)
{
  (void) lit;
  assert(watched() == std::abs(lit));
  size_t size = d_lits.size();
  size_t i    = 0;
  while (i < size)
  {
    if (!assigned(propagator))
    {
      break;
    }
    d_watched = (d_watched + 1) % size;
    ++i;
  }
  return assigned(propagator);
}

bool
WatchedBV::init(const Propagator& propagator)
{
  size_t size = d_lits.size();
  size_t i    = 0;
  while (i < size)
  {
    if (!propagator.info(watched()).fixed)
    {
      break;
    }
    d_watched = (d_watched + 1) % size;
    ++i;
  }
  return propagator.info(watched()).fixed;
}

bool
WatchedBV::assigned(const Propagator& propagator) const
{
  return propagator.info(watched()).assignment != 0;
}

std::ostream&
WatchedBV::str(const Propagator& propagator, std::ostream& os) const
{
  os << " [";
  for (const int32_t lit : d_lits)
  {
    os << " " << lit;
    if (d_lits[d_watched] == lit)
    {
      os << "*";
    }
  }
  os << " ] (";
  for (const int32_t lit : d_lits)
  {
    const auto& vi = propagator.info(std::abs(lit));

    os << " " << ((lit < 0) ? -vi.assignment : vi.assignment);
  }
  os << " )";
  return os;
}

DistinctNPropagator::DistinctNPropagator(
    util::Integer& card,
    int32_t var,
    const std::vector<std::vector<int32_t>>& bvs)
    : d_propagator(nullptr),
      d_var(var),
      d_cardinality(card),
      d_num_conflict_thres(bvs.size()),
      d_num_conflicts(0)
{
  assert(!bvs.empty());
  d_num_conflict_thres -= d_cardinality;

  // Add watched bit-vectors. d_watched_vars will be initialized on
  // attach_propagator().
  for (const auto& bv : bvs)
  {
    d_watched_bv.emplace_back(new WatchedBV(bv));
  }
}

bool
DistinctNPropagator::done() const
{
  const auto& vi = d_propagator->info(d_var);
  return vi.fixed && vi.assignment == -1;
}

void
DistinctNPropagator::attach_propagator(Propagator* propagator)
{
  d_propagator = propagator;
  // Observe propagator variable since it can occur in conflict clauses.
  d_propagator->observe(d_var);
  // Always fix phase of propagator variable to true, it will only be assigned
  // false if forced on decision level 0.
  d_propagator->force_phase(d_var);

  // We can never reach the given cardinality since we do not have enough
  // bit-vectors. Force propagator to false.
  if (d_num_conflict_thres < 0)
  {
    d_propagator->add_clause({-d_var}, false);
  }
  else
  {
    assert(d_watched_vars.empty());
    assert(!d_watched_bv.empty());
    BitVector phase(d_watched_bv.front()->lits().size());
    // Watch all literals of watched bit-vectors.
    for (const auto& wbv : d_watched_bv)
    {
      const auto& lits = wbv->lits();
      for (size_t i = 0, size = lits.size(); i < size; ++i)
      {
        int32_t lit = lits[i];
        d_propagator->watch(lit);
        // This is a heuristic for now and should be adapated based on current
        // assignments. We assume all bit-vectors to be different.
        d_propagator->force_phase(phase.bit(size - 1 - i) ? lit : -lit);
      }
      phase.ibvinc();

      // Some (or all) literals may already be fixed. If all literals are fixed,
      // the bit-vector value is fully assigned which we register right away.
      if (wbv->init(*d_propagator))
      {
        assigned(wbv->watched(), wbv.get());
      }
      else
      {
        d_watched_vars[wbv->watched()].push_back(wbv.get());
      }
    }
  }
}

int32_t
DistinctNPropagator::var() const
{
  return d_var;
}

void
DistinctNPropagator::assign(int32_t lit)
{
  int32_t var = std::abs(lit);
  auto it     = d_watched_vars.find(var);
  if (it == d_watched_vars.end())
  {
    return;
  }
  for (const auto wbv : it->second)
  {
    if (wbv->assign(*d_propagator, lit))
    {
      assigned(var, wbv);
    }
    else
    {
      assert(wbv->watched() != var);
      d_watched_vars[wbv->watched()].push_back(wbv);
    }
  }
  it->second.clear();
}

void
DistinctNPropagator::unassign(int32_t var)
{
  // Retire every fully-assigned watched bit-vector that was triggered by this
  // var. Its recorded bit-vector value is now stale.
  auto vit = d_var_to_assigned.find(var);
  if (vit == d_var_to_assigned.end()) return;
  std::vector<std::pair<BitVector, WatchedBV*>> entries(std::move(vit->second));
  vit->second.clear();
  for (auto& [key, wbv] : entries)
  {
    auto map_it = d_assigned_map.find(key);
    assert(map_it != d_assigned_map.end());
    auto& bucket = map_it->second;
    auto find_it = std::find(bucket.begin(), bucket.end(), wbv);
    assert(find_it != bucket.end());
    bool was_collision = bucket.size() > 1;
    bucket.erase(find_it);
    if (bucket.empty())
    {
      d_assigned_map.erase(map_it);
    }
    else if (was_collision)
    {
      --d_num_conflicts;
      assert(d_num_conflicts >= 0);
    }
    // Re-register WBV for partial-assignment tracking.
    d_watched_vars[wbv->watched()].push_back(wbv);
  }
}

void
DistinctNPropagator::assigned(int32_t var, WatchedBV* wbv)
{
  (void) var;
  const auto& lits = wbv->lits();
  size_t size      = lits.size();

  // Construct bit-vector assignment.
  BitVector bv(size);
  for (size_t i = 0; i < size; ++i)
  {
    int32_t lit    = lits[i];
    const auto& vi = d_propagator->info(std::abs(lit));
    assert(vi.assignment != 0);
    bv.set_bit(size - 1 - i, lit * vi.assignment > 0);
  }

  auto [it, inserted] = d_assigned_map.try_emplace(bv);
  it->second.emplace_back(wbv);
  // Fully assigned watched bit-vector, triggered by var.
  assert(wbv->watched() == var);
  d_var_to_assigned[wbv->watched()].emplace_back(bv, wbv);

  // Assignment collision
  if (!inserted)
  {
    ++d_num_conflicts;
    assert(d_num_conflicts > 0);

    // Collision threshold exceeded
    if (d_num_conflicts > d_num_conflict_thres)
    {
      std::vector<int32_t> conflict;
      conflict.push_back(-d_var);
      // Generate conflict clause from all current collisions, i.e., at least
      // one involved literal needs to be different if the propagator is true.
      for (const auto& [k, conflicting_wbv] : d_assigned_map)
      {
        // We have at least one collision for assignment k
        if (conflicting_wbv.size() > 1)
        {
          for (const auto _wbv : conflicting_wbv)
          {
            for (const int32_t lit : _wbv->lits())
            {
              const auto& vi = d_propagator->info(std::abs(lit));
              assert(vi.assignment != 0);
              // We can't force fixed literals to have different assignments, so
              // we have to consider the remaining non-fixed ones.
              if (vi.fixed)
              {
                continue;
              }
              int32_t val = -std::abs(lit) * vi.assignment;
              conflict.push_back(val);
            }
          }
        }
      }
      d_propagator->add_clause(conflict, true);
    }
  }
}

std::ostream&
DistinctNPropagator::str(std::ostream& os) const
{
  os << "DistinctNPropagator state (var: " << d_var << ", size: " << d_watched_bv.size()
     << ", card: " << d_cardinality << ")\n";
  for (const auto& wbv : d_watched_bv)
  {
    os << "  ";
    wbv->str(*d_propagator, os);
    os << "\n";
  }
  return os;
}

}  // namespace bzla::sat

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/
