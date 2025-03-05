/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2025 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_SAT_INTERPOLANTS_TRACER_KINDS_H_INCLUDED
#define BZLA_SAT_INTERPOLANTS_TRACER_KINDS_H_INCLUDED

#include <iomanip>

namespace bzla::sat::interpolants {

enum class VariableKind
{
  A,
  B,
  GLOBAL,
};
enum class ClauseKind
{
  A,
  B,
  LEARNED,  // internal
};

std::ostream& operator<<(std::ostream& out, VariableKind kind);
std::ostream& operator<<(std::ostream& out, ClauseKind kind);

}  // namespace bzla::sat::interpolants
#endif
