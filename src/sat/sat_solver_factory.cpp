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

#include "option/option.h"
#include "sat/cadical.h"
#ifdef BZLA_USE_CMS
#include "sat/cryptominisat.h"
#endif
#ifdef BZLA_USE_KISSAT
#include "sat/kissat.h"
#endif

#include <cassert>

namespace bzla::sat {

SatSolver*
SatSolverFactory::new_sat_solver()
{
#ifdef BZLA_USE_KISSAT
  if (d_options.sat_solver() == option::SatSolver::KISSAT)
  {
    return new Kissat();
  }
#endif
#ifdef BZLA_USE_CMS
  if (d_options.sat_solver() == option::SatSolver::CRYPTOMINISAT)
  {
    return new CryptoMiniSat(d_options.nthreads());
  }
#endif
  assert(d_options.sat_solver() == option::SatSolver::CADICAL);
  return new Cadical();
}

bool
SatSolverFactory::has_terminator_support()
{
#ifdef BZLA_USE_KISSAT
  if (d_options.sat_solver() == option::SatSolver::KISSAT)
  {
    return false;
  }
#endif
#ifdef BZLA_USE_CMS
  if (d_options.sat_solver() == option::SatSolver::CRYPTOMINISAT)
  {
    return false;
  }
#endif
  assert(d_options.sat_solver() == option::SatSolver::CADICAL);
  return true;
}

}  // namespace bzla::sat
