/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2024 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_SET_DEPTH_H_INCLUDED
#define BZLA_UTIL_SET_DEPTH_H_INCLUDED

#include <iostream>

namespace bzla::util {

/** Struct to set maximum printing depth of nodes via stream manipulator. */
struct set_depth
{
  /** std::ios_base index for setting maximum print depth. */
  static int32_t s_stream_index_maximum_depth;
  /**
   * Constructor.
   * @param depth The maximum printing depth.
   */
  set_depth(size_t depth) : d_depth(depth) {}
  /** @return The configured maximum printing depth. */
  size_t depth() const { return d_depth; }

 private:
  /** The configured maximum printing depth. */
  size_t d_depth;
};

std::ostream& operator<<(std::ostream& ostream, const set_depth& d);

}  // namespace bzla::util

#endif
