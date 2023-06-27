/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/fp/rounding_mode.h"

#include <cassert>

namespace bzla {

std::ostream&
operator<<(std::ostream& out, const RoundingMode& rm)
{
  switch (rm)
  {
    case RoundingMode::RNA: out << "RNA"; break;
    case RoundingMode::RNE: out << "RNE"; break;
    case RoundingMode::RTN: out << "RTN"; break;
    case RoundingMode::RTP: out << "RTP"; break;
    case RoundingMode::RTZ: out << "RTZ"; break;
    case RoundingMode::NUM_RM: assert(false);
  }
  return out;
}

}  // namespace bzla
