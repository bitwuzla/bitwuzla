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
#ifdef BZLA_USE_CMS
#include "sat/cryptominisat.h"
#endif
#ifdef BZLA_USE_KISSAT
#include "sat/kissat.h"
#endif
#ifdef BZLA_USE_AE_KISSAT
#include "sat/ae_kissat.h"
#endif

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
#ifdef BZLA_USE_AE_KISSAT
  if (options.sat_solver() == option::SatSolver::AE_KISSAT)
  {
    return new AEKissat();
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

bool
has_sat_solver_terminator_support(const option::Options& options)
{
  (void) options;
#ifdef BZLA_USE_KISSAT
  if (options.sat_solver() == option::SatSolver::KISSAT)
  {
    return false;
  }
#endif
#ifdef BZLA_USE_AE_KISSAT
  if (options.sat_solver() == option::SatSolver::AE_KISSAT)
  {
    return false;
  }
#endif
#ifdef BZLA_USE_CMS
  if (options.sat_solver() == option::SatSolver::CRYPTOMINISAT)
  {
    return false;
  }
#endif
  return true;
}

}  // namespace bzla::sat
