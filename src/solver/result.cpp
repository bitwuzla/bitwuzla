/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "solver/result.h"

namespace bzla {

std::ostream&
operator<<(std::ostream& out, const Result& r)
{
  switch (r)
  {
    case Result::SAT: out << "sat"; break;
    case Result::UNSAT: out << "unsat"; break;
    case Result::UNKNOWN: out << "unknown"; break;
  }
  return out;
}

}  // namespace bzla
