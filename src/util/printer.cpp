/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#include "util/printer.h"

namespace bzla::util {

/* -------------------------------------------------------------------------- */

int32_t set_depth::s_stream_index_maximum_depth = std::ios_base::xalloc();

std::ostream&
operator<<(std::ostream& ostream, const set_depth& d)
{
  ostream.iword(set_depth::s_stream_index_maximum_depth) = d.depth();
  return ostream;
}

/* -------------------------------------------------------------------------- */

int32_t set_bv_format::s_stream_index_bv_format = std::ios_base::xalloc();

std::ostream&
operator<<(std::ostream& ostream, const set_bv_format& f)
{
  ostream.iword(set_bv_format::s_stream_index_bv_format) = f.format();
  return ostream;
}

/* -------------------------------------------------------------------------- */

int32_t set_letify::s_stream_index_no_letify = std::ios_base::xalloc();

std::ostream&
operator<<(std::ostream& ostream, const set_letify& l)
{
  ostream.iword(set_letify::s_stream_index_no_letify) = !l.letify();
  return ostream;
}

/* -------------------------------------------------------------------------- */

}  // namespace bzla::util
