/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */
#include <bitwuzla/result.h>

#include <cassert>

namespace bitwuzla {
std::ostream&
operator<<(std::ostream& out, Result result)
{
  out << std::to_string(result);
  return out;
}
}  // namespace bitwuzla

namespace std {
std::string
to_string(bitwuzla::Result result)
{
  switch (result)
  {
    case bitwuzla::Result::SAT: return "sat";
    case bitwuzla::Result::UNSAT: return "unsat";
    default: assert(result == bitwuzla::Result::UNKNOWN); return "unknown";
  }
}
}  // namespace std
