/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_SAT_SOLVER_H_INCLUDED
#define BZLA_SAT_SAT_SOLVER_H_INCLUDED

#include <bitwuzla/cpp/sat_solver.h>

#include <cstdint>
#include <memory>

#include "sat/sat_propagator.h"

namespace bzla::sat {

/**
 * The internal SAT solver interface.
 *
 * Extends the public SAT solver interface with features that are only
 * implemented by the bundled SAT solvers. SAT solvers provided via a
 * bitwuzla::SatSolverFactory only implement the public interface and are
 * wrapped into an adapter that provides the defaults below.
 */
class SatSolver : public bitwuzla::SatSolver
{
 public:
  /**
   * Allocate new variable in SAT solver.
   * @return Fresh variable.
   */
  virtual int32_t new_var() = 0;

  /**
   * Register SAT propagator.
   *
   * SAT solvers without propagator support ignore registered propagators.
   * This is only sound for propagators that provide guidance but do not
   * enforce constraints (decision heuristics), propagators that enforce
   * constraints require SatSolverFactory::has_propagator_support().
   *
   * @param sp The propagator to register.
   */
  virtual void register_propagator(std::unique_ptr<SatPropagator> sp)
  {
    (void) sp;
  }

  /**
   * Push assertion level.
   *
   * Implementing push()/pop()/set_level() is optional: all clauses sent to
   * the SAT solver are globally valid (Tseitin definitions and theory-valid
   * lemmas; assertions of non-zero levels are assumption-guarded).
   * SAT backends may ignore assertion levels at the cost of accumulating
   * clauses from popped levels.
   */
  virtual void push() {}

  /**
   * Pop assertion level.
   * @note Resets the current clause level to 0.
   */
  virtual void pop() {}

  /**
   * Set assertion level for incoming clauses.
   * @param level A valid assertion level.
   */
  virtual void set_level(uint32_t level) { (void) level; }
};

}  // namespace bzla::sat
#endif
