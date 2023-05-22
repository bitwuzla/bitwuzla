#ifndef BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED
#define BZLA_SAT_SAT_SOLVER_FACTORY_H_INCLUDED

#include "option/option.h"
#include "sat/sat_solver.h"

namespace bzla::sat {

SatSolver* new_sat_solver(option::SatSolver kind);

}

#endif
