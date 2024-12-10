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
#include "sat/cryptominisat.h"
#include "sat/kissat.h"

namespace bzla::sat {

SatSolver*
new_sat_solver(const option::Options& options)
{
  (void) options;
#ifdef BZLA_USE_KISSAT
  if (options.sat_solver() == option::SatSolver::KISSAT)
  {
    return new Kissat();
  }
#endif
#ifdef BZLA_USE_CMS
  if (options.sat_solver() == option::SatSolver::CRYPTOMINISAT)
  {
    return new CryptoMiniSat(options.nthreads());
  }
#endif
  return new Cadical();
}

}  // namespace bzla::sat
