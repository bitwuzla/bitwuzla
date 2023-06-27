/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_RESULT_H_INCLUDED
#define BZLA_SOLVER_RESULT_H_INCLUDED

#include <iostream>

namespace bzla {

enum class Result
{
  SAT,
  UNSAT,
  UNKNOWN
};

std::ostream& operator<<(std::ostream& out, const Result& r);

}  // namespace bzla

#endif
