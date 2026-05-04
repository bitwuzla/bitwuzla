/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/propagator.h"

#include <cassert>
#include <cstdlib>
#include <iostream>

namespace bzla::sat {

void
Propagator::notify_assignment(const std::vector<int32_t>& lits)
{
  for (int32_t lit : lits)
  {
    int32_t var     = std::abs(lit);
    auto& info      = d_var_info[var];
    info.assignment = lit < 0 ? -1 : 1;
    info.decision   = d_solver->is_decision(lit);
    d_assignments.push_back(var);
    if (d_var_info[var].watched)
    {
      for (auto& sp : d_sat_propagators)
      {
        if (sp->done())
        {
          continue;
        }
        sp->assign(lit);
      }
    }
  }
}

void
Propagator::notify_new_decision_level()
{
  d_assignments_control.push_back(d_assignments.size());
  ++d_stats.num_decisions;
}

void
Propagator::notify_backtrack(size_t new_level)
{
  size_t backtrack_to = d_assignments_control[new_level];
  d_assignments_control.resize(new_level);
  while (backtrack_to < d_assignments.size())
  {
    int32_t var = std::abs(d_assignments.back());
    d_assignments.pop_back();
    auto& info      = d_var_info[var];
    info.assignment = 0;
    // If a forced phase is set, add to decision queue again.
    if (info.phase && !info.fixed)
    {
      d_decisions.push_back(var * info.phase);
    }
    // Notify watchers that variable assignment was undone.
    if (info.watched)
    {
      for (auto& sp : d_sat_propagators)
      {
        sp->unassign(var);
      }
    }
  }
}

bool
Propagator::cb_check_found_model(const std::vector<int32_t>& model)
{
  (void) model;
  assert(d_external_clause_forgettable.empty());
  assert(d_external_clause.empty());
  return true;
}

int32_t
Propagator::cb_decide()
{
  while (!d_decisions.empty())
  {
    int32_t d = d_decisions.front();
    d_decisions.pop_front();
    const auto& vi = info(std::abs(d));
    if (vi.fixed || vi.assignment)
    {
      continue;
    }
    return d;
  }
  return 0;
};

int32_t
Propagator::cb_propagate()
{
  return 0;
};

int32_t
Propagator::cb_add_reason_clause_lit(int32_t propagated_lit)
{
  (void) propagated_lit;
  return 0;
};

bool
Propagator::cb_has_external_clause(bool& is_forgettable)
{
  if (!d_external_clause.empty())
  {
    assert(!d_external_clause_forgettable.empty());
    is_forgettable = d_external_clause_forgettable.front();
    d_external_clause_forgettable.pop_front();
    return true;
  }
  assert(d_external_clause_forgettable.empty());
  return false;
}

int32_t
Propagator::cb_add_external_clause_lit()
{
  assert(!d_external_clause.empty());
  int32_t lit = d_external_clause.front();
  d_external_clause.pop_front();
  return lit;
}

void
Propagator::notify_fixed_assignment(int32_t lit)
{
  d_var_info[std::abs(lit)].fixed = true;
  ++d_stats.num_fixed;
}

void
Propagator::attach_solver(CaDiCaL::Solver* solver)
{
  assert(d_solver == nullptr);
  d_solver = solver;
}

void
Propagator::force_phase(int32_t lit)
{
  auto& var_info = d_var_info[std::abs(lit)];
  var_info.phase = lit < 0 ? -1 : 1;
  d_decisions.push_back(lit);
}

void
Propagator::force_unphase(int32_t lit)
{
  auto& var_info = d_var_info[std::abs(lit)];
  var_info.phase = 0;
}

void
Propagator::phase(int32_t lit)
{
  d_solver->phase(lit);
}

void
Propagator::resize(int32_t var)
{
  d_var_info.resize(std::abs(var) + 1);
}

void
Propagator::watch(int32_t lit)
{
  int32_t var       = std::abs(lit);
  info(var).watched = true;
  d_solver->add_observed_var(var);
  ++d_stats.num_observed;
  ++d_stats.num_watched;
}

void
Propagator::observe(int32_t lit)
{
  d_solver->add_observed_var(std::abs(lit));
  ++d_stats.num_observed;
}

Propagator::VarInfo&
Propagator::info(int32_t var)
{
  assert(var > 0);
  assert(static_cast<size_t>(var) < d_var_info.size());
  return d_var_info[var];
}

const Propagator::VarInfo&
Propagator::info(int32_t var) const
{
  assert(var > 0);
  assert(static_cast<size_t>(var) < d_var_info.size());
  return d_var_info[var];
}

void
Propagator::add_clause(const std::vector<int32_t>& lits, bool is_forgettable)
{
  d_external_clause_forgettable.push_back(is_forgettable);
  d_external_clause.insert(d_external_clause.end(), lits.begin(), lits.end());
  d_external_clause.push_back(0);
  ++d_stats.num_clauses;
}

void
Propagator::register_propagator(std::unique_ptr<SatPropagator> sp)
{
  sp->attach_propagator(this);
  d_sat_propagators.emplace_back(std::move(sp));
}

void
Propagator::print_state() const
{
}

void
Propagator::print_stats() const
{
  std::cout << "num_clauses: " << d_stats.num_clauses << std::endl;
  std::cout << "num_decisions: " << d_stats.num_decisions << std::endl;
  std::cout << "num_fixed: " << d_stats.num_fixed << std::endl;
  std::cout << "num_observed: " << d_stats.num_observed << std::endl;
  std::cout << "num_watched: " << d_stats.num_watched << std::endl;
}

}  // namespace bzla::sat
