#ifndef BZLA_SOLVER_FP_ROUNDING_MODE_H_INCLUDED
#define BZLA_SOLVER_FP_ROUNDING_MODE_H_INCLUDED

#include <iostream>

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
