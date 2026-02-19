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
#include "util/exceptions.h"

namespace bzla::sat {

std::unique_ptr<SatSolver>
SatSolverFactory::new_sat_solver(bool produce_interpolants)
{
#ifdef BZLA_USE_KISSAT
  if (d_sat_solver == option::SatSolver::KISSAT)
  {
    if (produce_interpolants)
    {
      throw Unsupported("interpolant generation not supported with Kissat");
    }
    return std::unique_ptr<SatSolver>(new Kissat());
  }
#endif
#ifdef BZLA_USE_CMS
  if (d_sat_solver == option::SatSolver::CRYPTOMINISAT)
  {
    if (produce_interpolants)
    {
      throw Unsupported(
          "interpolant generation not supported with CryptoMiniSat");
    }
    return std::unique_ptr<SatSolver>(new CryptoMiniSat(d_nthreads));
  }
#endif
#ifdef BZLA_USE_GIMSATUL
  if (d_sat_solver == option::SatSolver::GIMSATUL)
  {
    if (produce_interpolants)
    {
      throw Unsupported("interpolant generation not supported with Gimsatul");
    }
    return std::unique_ptr<SatSolver>(new Gimsatul(d_nthreads));
  }
#endif
  assert(d_sat_solver == option::SatSolver::CADICAL);
#ifdef BZLA_USE_CADICAL
  if (produce_interpolants)
  {
    return std::unique_ptr<SatSolver>(new CadicalInterpol());
  }
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
