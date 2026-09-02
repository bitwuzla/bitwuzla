/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver.h"

#include "env.h"

namespace bzla {

Solver::Solver(Env& env, SolverState& state)
    : d_env(env), d_logger(env.logger()), d_solver_state(state)
{
}

}  // namespace bzla
