#include "sat/sat_solver_factory.h"

#include "sat/cadical.h"
#include "sat/kissat.h"

namespace bzla::sat {

SatSolver*
new_sat_solver(option::SatSolver kind)
{
#ifdef BZLA_USE_KISSAT
  if (kind == option::SatSolver::KISSAT)
  {
    return new Kissat();
  }
#endif

  return new Cadical();
}

}  // namespace bzla::sat
