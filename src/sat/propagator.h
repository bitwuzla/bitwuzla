/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_PROPAGATOR_H_INCLUDED
#define BZLA_SAT_PROPAGATOR_H_INCLUDED

/*----------------------------------------------------------------------------*/
#ifdef BZLA_USE_CADICAL
/*----------------------------------------------------------------------------*/

#include <cadical.hpp>
#include <deque>
#include <memory>
#include <unordered_set>

#include "sat/distinct_n_propagator.h"

namespace bzla::sat {

class Propagator : public CaDiCaL::ExternalPropagator,
                   public CaDiCaL::FixedAssignmentListener
{
 public:
  struct VarInfo
  {
    int8_t phase      = 0;
    int8_t assignment = 0;
    bool fixed        = false;
    bool active       = false;
    bool watched      = false;
    bool decision     = false;
  };

  ~Propagator() override = default;

  // ExternalPropagator interface
  void notify_assignment(const std::vector<int32_t>& lits) override;

  void notify_new_decision_level() override;

  void notify_backtrack(size_t new_level) override;

  bool cb_check_found_model(const std::vector<int32_t>& model) override;

  int32_t cb_decide() override;

  int32_t cb_propagate() override;

  int32_t cb_add_reason_clause_lit(int32_t propagated_lit) override;

  bool cb_has_external_clause(bool& is_forgettable) override;

  int32_t cb_add_external_clause_lit() override;

  // FixedAssignmentListener interface
  void notify_fixed_assignment(int32_t lit) override;

  void attach_solver(CaDiCaL::Solver* solver);

  void force_phase(int32_t lit);

  void force_unphase(int32_t lit);

  void phase(int32_t lit);

  /** Resize variable info struct include var. */
  void resize(int32_t var);

  /** Mark literal as watched. */
  void watch(int32_t lit);

  /**
   * Mark literal as observed, which indicates that it may occur in a clause
   * added via add_clause().
   */
  void observe(int32_t lit);

  /** @return Variable info. */
  VarInfo& info(int32_t var);
  const VarInfo& info(int32_t var) const;

  /** Add new (possibly forgettable) clause. */
  void add_clause(const std::vector<int32_t>& lits,
                  bool is_forgettable = false);

  void register_propagator(std::unique_ptr<SatPropagator> sp);

  void print_state() const;
  void print_stats() const;

 private:
  CaDiCaL::Solver* d_solver = nullptr;
  std::vector<int32_t> d_phases;
  std::vector<VarInfo> d_var_info;
  std::vector<int32_t> d_assignments;
  std::deque<int32_t> d_decisions;
  std::vector<size_t> d_assignments_control;
  std::vector<std::unique_ptr<SatPropagator>> d_sat_propagators;
  std::deque<int32_t> d_external_clause;
  std::deque<bool> d_external_clause_forgettable;

  struct Statistics
  {
    uint64_t num_clauses   = 0;
    uint64_t num_decisions = 0;
    uint64_t num_fixed     = 0;
    uint64_t num_observed  = 0;
    uint64_t num_watched   = 0;
  } d_stats;
};

}  // namespace bzla::sat

/*----------------------------------------------------------------------------*/
#endif
/*----------------------------------------------------------------------------*/

#endif
