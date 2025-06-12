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

#include "option/option.h"
#include "sat/sat_solver.h"

namespace bzla::sat {

/** Create new SAT solver instance. */
SatSolver* new_sat_solver(const option::Options& options);
/** Determine if configured SAT solver has terminator support. */
bool has_sat_solver_terminator_support(const option::Options& options);
}

#endif
