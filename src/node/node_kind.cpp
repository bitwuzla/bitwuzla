/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2022 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "node/node_kind.h"

#include "node/kind_info.h"

namespace bzla::node {

std::ostream&
operator<<(std::ostream& out, Kind kind)
{
  return out << KindInfo::enum_name(kind);
}

}  // namespace bzla::node
