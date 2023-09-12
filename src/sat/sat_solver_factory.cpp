/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/sat_solver_factory.h"

#include "sat/cadical.h"
#include "sat/kissat.h"

namespace bzla::sat {

SatSolver*
new_sat_solver(option::SatSolver kind)
{
  (void) kind;
#ifdef BZLA_USE_KISSAT
  if (kind == option::SatSolver::KISSAT)
  {
    return new Kissat();
  }
#endif

  return new Cadical();
}

}  // namespace bzla::sat
