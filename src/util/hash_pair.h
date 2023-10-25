/***
 * Bitwuzla: Satisfiability Modulo Theories (SMT) solver.
 *
 * Copyright (C) 2023 by the authors listed in the AUTHORS file at
 * https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS
 *
 * This file is part of Bitwuzla under the MIT license. See COPYING for more
 * information at https://github.com/bitwuzla/bitwuzla/blob/main/COPYING
 */

#ifndef BZLA_UTIL_HASH_PAIR_H_INCLUDED
#define BZLA_UTIL_HASH_PAIR_H_INCLUDED

#include <cstdint>
#include <functional>
#include <utility>

namespace std {
template <>
struct hash<std::pair<uint64_t, uint64_t>>
{
  /**
   * Hash function for pair of uint64_t.
   * @param p The pair.
   * @return The hash value.
   */
  size_t operator()(const std::pair<uint64_t, uint64_t>& p) const;
};
}  // namespace std
#endif
