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

#include <cstdint>
#include <string>

#include "solver/result.h"
#include "terminator.h"

namespace bzla::sat {

class SatSolver
{
 public:
  /**
   * Constructor.
   * @param name The name of the underlying SAT solver.
   */
  SatSolver() {}
  /** Destructor. */
  virtual ~SatSolver(){};

  /**
   * Add valid literal to current clause.
   * @param lit The literal to add, 0 to terminate clause..
   */
  virtual void add(int32_t lit) = 0;
  /**
   * Assume valid (non-zero) literal for next call to 'check_sat'.
   * @param lit The literal to assume.
   */
  virtual void assume(int32_t lit) = 0;
  /**
   * Get value of valid non-zero literal.
   * @param lit The literal to query.
   * @return The value of the literal (-1 = false, 1 = true, 0 = unknown).
   */
  virtual int32_t value(int32_t lit) = 0;
  /**
   * Determine if the valid non-zero literal is in the unsat core.
   * @param lit The literal to query.
   * @return True if the literal is in the core, and false otherwise.
   */
  virtual bool failed(int32_t lit) = 0;
  /**
   * Determine if the given literal is implied by the formula.
   * @return 1 if it is implied, -1 if it is not implied and 0 if unknown.
   */
  virtual int32_t fixed(int32_t lit) = 0;
  /**
   * Check satisfiability of current formula.
   * @return The result of the satisfiability check.
   */
  virtual Result solve() = 0;
  /**
   * Configure a termination callback function via a terminator.
   * @param terminator The terminator.
   */
  virtual void configure_terminator(Terminator *terminator) = 0;

  // virtual int32_t repr(int32_t) = 0;

  /**
   * Get the name of this SAT solver.
   * @return The name of this SAT solver.
   */
  virtual const char *get_name() const = 0;

  /**
   * Get the version of this SAT solver.
   * @return The version of the underly ing SAT solver.
   */
  virtual const char *get_version() const = 0;
};

}  // namespace bzla::sat
#endif
