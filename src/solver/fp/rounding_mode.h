/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SOLVER_FP_ROUNDING_MODE_H_INCLUDED
#define BZLA_SOLVER_FP_ROUNDING_MODE_H_INCLUDED

#include <iostream>

#define BZLA_RM_BV_SIZE 3

namespace bzla {

enum class RoundingMode
{
  RNA = 0,  // roundNearestTiesToAway
  RNE,      // roundNearestTiesToEven
  RTN,      // roundTowardNegative
  RTP,      // roundTowardPositive
  RTZ,      // roundTowardZero
  NUM_RM,
};

std::ostream& operator<<(std::ostream& out, const RoundingMode& rm);

}  // namespace bzla

#endif
