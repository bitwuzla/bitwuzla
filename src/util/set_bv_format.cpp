/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/set_bv_format.h"

namespace bzla::util {

int32_t set_bv_format::s_stream_index_bv_format = std::ios_base::xalloc();

std::ostream&
operator<<(std::ostream& ostream, const set_bv_format& f)
{
  ostream.iword(set_bv_format::s_stream_index_bv_format) = f.format();
  return ostream;
}

}  // namespace bzla::util
