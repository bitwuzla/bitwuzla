/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include <cassert>
#include "sat/sat_solver_factory.h"

#include "sat/cadical.h"
#include "sat/kissat.h"
#include "sat/cryptominisat.h"

namespace bzla::sat {

SatSolver*
new_sat_solver(option::SatSolver kind)
{
  switch(kind) {
    case option::SatSolver::CADICAL:
      return new Cadical();
#ifdef BZLA_USE_KISSAT
    case option::SatSolver::KISSAT:
      return new Kissat();
#endif
#ifdef BZLA_USE_CMS
    case option::SatSolver::CRYPTOMINISAT:
      return new CryptoMiniSat();
#endif
    default:
      assert(!"sat solver not supported");
      return new Cadical();
  }
}

}  // namespace bzla::sat
