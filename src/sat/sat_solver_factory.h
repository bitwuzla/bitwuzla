/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED
#define BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED

#include <memory>

#include "option/option.h"
#include "sat/sat_solver.h"

namespace bzla::sat {

class SatSolverFactory
{
 public:
  /** Constructor. */
  SatSolverFactory(const option::Options& options) : d_options(options) {}
  /** Create new SAT solver instance. */
  std::unique_ptr<SatSolver> new_sat_solver();
  /** Determine if configured SAT solver has terminator support. */
  bool has_terminator_support();

 private:
  const option::Options& d_options;
};

}  // namespace bzla::sat
#endif
