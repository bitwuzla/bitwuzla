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

#include <cassert>
#include <iostream>

namespace bzla::sat::interpolants {

std::ostream&
operator<<(std::ostream& out, VariableKind kind)
{
  switch (kind)
  {
    case VariableKind::A: out << "A"; break;
    case VariableKind::B: out << "B"; break;
    case VariableKind::GLOBAL: out << "GLOBAL"; break;
    default: assert(kind == VariableKind::NONE); out << "NONE";
  }
  return out;
}

std::ostream&
operator<<(std::ostream& out, ClauseKind kind)
{
  switch (kind)
  {
    case ClauseKind::A: out << "A"; break;
    case ClauseKind::B: out << "B"; break;
    default: assert(kind == ClauseKind::LEARNED); out << "LEARNED";
  }
  return out;
}

}  // namespace bzla::sat::interpolants
