/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "sat/interpolants/tracer_kinds.h"

#include <iostream>

namespace bzla::sat::interpolants {

std::ostream&
operator<<(std::ostream& out, VariableKind kind)
{
  out << (kind == VariableKind::A ? "A"
                                  : (kind == VariableKind::B ? "B" : "GLOBAL"));
  return out;
}

std::ostream&
operator<<(std::ostream& out, ClauseKind kind)
{
  out << (kind == ClauseKind::A ? "A"
                                : (kind == ClauseKind::B ? "B" : "LEARNED"));
  return out;
}

}  // namespace bzla::sat::interpolants
