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
#ifdef BZLA_USE_CADICAL
#include "sat/cadical.h"
#endif
#ifdef BZLA_USE_CMS
#include "sat/cryptominisat.h"
#endif
#ifdef BZLA_USE_KISSAT
#include "sat/kissat.h"
#endif
#ifdef BZLA_USE_GIMSATUL
#include "sat/gimsatul.h"
#endif

#include <cassert>

#include "sat/sat_solver.h"

namespace bzla::sat {

std::unique_ptr<SatSolver>
SatSolverFactory::new_sat_solver()
{
#ifdef BZLA_USE_KISSAT
  if (d_sat_solver == option::SatSolver::KISSAT)
  {
    return std::unique_ptr<SatSolver>(new Kissat());
  }
#endif
#ifdef BZLA_USE_CMS
  if (d_sat_solver == option::SatSolver::CRYPTOMINISAT)
  {
    return std::unique_ptr<SatSolver>(new CryptoMiniSat(d_nthreads));
  }
#endif
#ifdef BZLA_USE_GIMSATUL
  if (d_sat_solver == option::SatSolver::GIMSATUL)
  {
    return std::unique_ptr<SatSolver>(new Gimsatul(d_nthreads));
  }
#endif
  assert(d_sat_solver == option::SatSolver::CADICAL);
#ifdef BZLA_USE_CADICAL
  return std::unique_ptr<SatSolver>(new Cadical());
#else
  return nullptr;
#endif
}

bool
SatSolverFactory::has_terminator_support()
{
#ifdef BZLA_USE_KISSAT
  if (d_sat_solver == option::SatSolver::KISSAT)
  {
    return false;
  }
#endif
#ifdef BZLA_USE_CMS
  if (d_sat_solver == option::SatSolver::CRYPTOMINISAT)
  {
    return false;
  }
#endif
#ifdef BZLA_USE_GIMSATUL
  if (d_sat_solver == option::SatSolver::GIMSATUL)
  {
    return false;
  }
#endif
  assert(d_sat_solver == option::SatSolver::CADICAL);
  return true;
}

}  // namespace bzla::sat
